//! EMI/EMC metrics: loop areas, edge effects, stitching, plane gaps.

use std::collections::BTreeMap;

use crate::board::{OutlineSegment, Point, Via};
use crate::model::{CategoryResult, MetricResult, WorstEntry};
use crate::net_graph::point_in_polygon;
use crate::norm;
use crate::stackup::{StackupGeometry, nearest_plane, plane_layers};

use super::{ScoreContext, ScorePass};

pub struct EmiPass;

fn dist_point_outline(p: Point, outline: &[OutlineSegment]) -> f64 {
    outline
        .iter()
        .map(|seg| {
            let (dx, dy) = (seg.end.x - seg.start.x, seg.end.y - seg.start.y);
            let len2 = dx * dx + dy * dy;
            if len2 < 1e-18 {
                return p.dist(&seg.start);
            }
            let t = (((p.x - seg.start.x) * dx + (p.y - seg.start.y) * dy) / len2).clamp(0.0, 1.0);
            p.dist(&Point {
                x: seg.start.x + t * dx,
                y: seg.start.y + t * dy,
            })
        })
        .fold(f64::INFINITY, f64::min)
}

impl ScorePass for EmiPass {
    fn id(&self) -> &'static str {
        "emi"
    }

    fn run(&self, ctx: &ScoreContext) -> CategoryResult {
        let mut metrics = Vec::new();
        let weight = ctx.weights.emi;
        let geometry = StackupGeometry::from_board(ctx.board);

        let classes = ctx.net_classes;
        let hs_net_ids: Vec<(i64, &str)> = classes
            .map(|classes| {
                ctx.board
                    .nets
                    .iter()
                    .filter_map(|(&id, name)| {
                        classes
                            .get(name)
                            .filter(|info| info.is_high_speed())
                            .map(|_| (id, name.as_str()))
                    })
                    .collect()
            })
            .unwrap_or_default();
        let ground_vias: Vec<&Via> = classes
            .map(|classes| {
                ctx.board
                    .vias
                    .iter()
                    .filter(|v| {
                        classes
                            .get(ctx.board.net_name(v.net))
                            .map(|info| info.is_ground)
                            .unwrap_or(false)
                    })
                    .collect()
            })
            .unwrap_or_default();
        let planes = classes
            .map(|classes| plane_layers(ctx.board, Some(classes)))
            .unwrap_or_default();

        let netlist_note = "netlist unavailable: declarative net classification required";
        let no_hs_note = "no high-speed nets declared";

        // loop_area_proxy: HS length x height above the nearest reference
        // plane; no plane found counts the full board thickness.
        if classes.is_none() {
            metrics.push(MetricResult::not_applicable(
                "loop_area_proxy",
                3.0,
                netlist_note,
            ));
        } else if hs_net_ids.is_empty() {
            metrics.push(MetricResult::not_applicable(
                "loop_area_proxy",
                3.0,
                no_hs_note,
            ));
        } else if let Some(geometry) = geometry.as_ref() {
            let fallback_h = geometry.total_thickness_mm.unwrap_or(1.6);
            let mut area = 0.0;
            let mut worst: BTreeMap<String, f64> = BTreeMap::new();
            for (id, name) in &hs_net_ids {
                for track in ctx.board.tracks.iter().filter(|t| t.net == *id) {
                    let h = nearest_plane(&track.layer, &planes, geometry)
                        .map(|(_, h)| h)
                        .unwrap_or(fallback_h);
                    let contribution = track.length() * h;
                    area += contribution;
                    *worst.entry((*name).to_string()).or_default() += contribution;
                }
            }
            let worst: Vec<WorstEntry> = worst
                .into_iter()
                .map(|(label, value)| WorstEntry { label, value })
                .collect();
            metrics.push(
                MetricResult::new("loop_area_proxy", area, "mm2", norm::decay(area, 20.0), 3.0)
                    .with_worst(worst, true),
            );
        } else {
            metrics.push(MetricResult::not_applicable(
                "loop_area_proxy",
                3.0,
                "stackup data missing",
            ));
        }

        // edge_clearance: copper distance to the board outline.
        if ctx.board.outline.is_empty() {
            metrics.push(MetricResult::not_applicable(
                "edge_clearance",
                2.0,
                "no board outline (Edge.Cuts) found",
            ));
        } else if ctx.board.tracks.is_empty() {
            metrics.push(MetricResult::not_applicable(
                "edge_clearance",
                2.0,
                "no routed tracks",
            ));
        } else {
            let mut min_dist = f64::INFINITY;
            let mut worst: BTreeMap<String, f64> = BTreeMap::new();
            for track in &ctx.board.tracks {
                for p in [track.start, track.end] {
                    let d = dist_point_outline(p, &ctx.board.outline) - track.width / 2.0;
                    min_dist = min_dist.min(d);
                    let name = ctx.board.net_name(track.net).to_string();
                    worst.entry(name).and_modify(|v| *v = v.min(d)).or_insert(d);
                }
            }
            let worst: Vec<WorstEntry> = worst
                .into_iter()
                .map(|(label, value)| WorstEntry { label, value })
                .collect();
            metrics.push(
                MetricResult::new(
                    "edge_clearance",
                    min_dist,
                    "mm",
                    norm::ratio_clamp(min_dist / 0.5),
                    2.0,
                )
                .with_worst(worst, false),
            );
        }

        // edge_stitching_density: largest gap between ground vias near the
        // board edge (fence quality).
        if classes.is_none() {
            metrics.push(MetricResult::not_applicable(
                "edge_stitching_density",
                1.0,
                netlist_note,
            ));
        } else if ctx.board.outline.is_empty() || planes.is_empty() {
            metrics.push(MetricResult::not_applicable(
                "edge_stitching_density",
                1.0,
                "needs an outline and reference planes",
            ));
        } else {
            let edge_vias: Vec<&Via> = ground_vias
                .iter()
                .copied()
                .filter(|v| dist_point_outline(v.at, &ctx.board.outline) <= 1.5)
                .collect();
            if edge_vias.len() < 2 {
                metrics.push(
                    MetricResult::new("edge_stitching_density", 99.0, "mm", 0.0, 1.0)
                        .with_note("fewer than two ground vias near the board edge"),
                );
            } else {
                // Worst nearest-neighbour spacing among edge vias.
                let mut max_gap = 0.0f64;
                for (i, a) in edge_vias.iter().enumerate() {
                    let nearest = edge_vias
                        .iter()
                        .enumerate()
                        .filter(|(j, _)| *j != i)
                        .map(|(_, b)| a.at.dist(&b.at))
                        .fold(f64::INFINITY, f64::min);
                    if nearest.is_finite() {
                        max_gap = max_gap.max(nearest);
                    }
                }
                metrics.push(MetricResult::new(
                    "edge_stitching_density",
                    max_gap,
                    "mm",
                    norm::ratio_clamp(5.0 / max_gap.max(1e-6)).min(1.0),
                    1.0,
                ));
            }
        }

        // stitching_via_density: mean distance from HS track midpoints to the
        // nearest ground via.
        if classes.is_none() {
            metrics.push(MetricResult::not_applicable(
                "stitching_via_density",
                1.0,
                netlist_note,
            ));
        } else if hs_net_ids.is_empty() {
            metrics.push(MetricResult::not_applicable(
                "stitching_via_density",
                1.0,
                no_hs_note,
            ));
        } else if ground_vias.is_empty() {
            metrics.push(
                MetricResult::new("stitching_via_density", 99.0, "mm", 0.0, 1.0)
                    .with_note("no ground vias on the board"),
            );
        } else {
            let mut sum = 0.0;
            let mut count = 0usize;
            for (id, _) in &hs_net_ids {
                for track in ctx.board.tracks.iter().filter(|t| t.net == *id) {
                    let mid = Point {
                        x: (track.start.x + track.end.x) / 2.0,
                        y: (track.start.y + track.end.y) / 2.0,
                    };
                    let nearest = ground_vias
                        .iter()
                        .map(|v| v.at.dist(&mid))
                        .fold(f64::INFINITY, f64::min);
                    if nearest.is_finite() {
                        sum += nearest;
                        count += 1;
                    }
                }
            }
            if count == 0 {
                metrics.push(MetricResult::not_applicable(
                    "stitching_via_density",
                    1.0,
                    "high-speed nets have no routed tracks",
                ));
            } else {
                let mean = sum / count as f64;
                metrics.push(MetricResult::new(
                    "stitching_via_density",
                    mean,
                    "mm",
                    norm::decay(mean, 3.0),
                    1.0,
                ));
            }
        }

        // plane_slot_crossings: interior gaps in the reference underneath a
        // high-speed track (covered -> uncovered -> covered transitions).
        if classes.is_none() {
            metrics.push(MetricResult::not_applicable(
                "plane_slot_crossings",
                2.0,
                netlist_note,
            ));
        } else {
            let reference_polys: Vec<&crate::board::ZonePolygon> = ctx
                .board
                .zones
                .iter()
                .filter(|z| {
                    classes
                        .unwrap()
                        .get(ctx.board.net_name(z.net))
                        .map(|info| info.is_ground || info.is_power)
                        .unwrap_or(false)
                })
                .flat_map(|z| z.filled_polygons.iter())
                .collect();
            if hs_net_ids.is_empty() || reference_polys.is_empty() {
                metrics.push(MetricResult::not_applicable(
                    "plane_slot_crossings",
                    2.0,
                    "needs high-speed nets and reference plane fills",
                ));
            } else {
                let mut crossings = 0usize;
                let mut worst: BTreeMap<String, f64> = BTreeMap::new();
                for (id, name) in &hs_net_ids {
                    for track in ctx.board.tracks.iter().filter(|t| t.net == *id) {
                        let length = track.length();
                        if length < 1e-9 {
                            continue;
                        }
                        let samples = (length / 0.5).ceil().max(2.0) as usize;
                        let covered: Vec<bool> = (0..=samples)
                            .map(|k| {
                                let t = k as f64 / samples as f64;
                                let p = Point {
                                    x: track.start.x + t * (track.end.x - track.start.x),
                                    y: track.start.y + t * (track.end.y - track.start.y),
                                };
                                reference_polys.iter().any(|poly| {
                                    poly.layer != track.layer && point_in_polygon(p, &poly.points)
                                })
                            })
                            .collect();
                        // Count interior uncovered runs bounded by coverage.
                        let mut k = 1;
                        while k < covered.len() {
                            if covered[k - 1]
                                && !covered[k]
                                && let Some(rest) = covered[k..].iter().position(|c| *c)
                            {
                                crossings += 1;
                                *worst.entry((*name).to_string()).or_default() += 1.0;
                                k += rest;
                            }
                            k += 1;
                        }
                    }
                }
                let worst: Vec<WorstEntry> = worst
                    .into_iter()
                    .map(|(label, value)| WorstEntry { label, value })
                    .collect();
                metrics.push(
                    MetricResult::new(
                        "plane_slot_crossings",
                        crossings as f64,
                        "count",
                        norm::decay(crossings as f64, 1.0),
                        2.0,
                    )
                    .with_worst(worst, true),
                );
            }
        }

        // outer_layer_hs_exposure: HS wire length on outer layers (>=4 layer
        // boards should route high-speed on inner layers).
        if classes.is_none() {
            metrics.push(MetricResult::not_applicable(
                "outer_layer_hs_exposure",
                1.0,
                netlist_note,
            ));
        } else if ctx.board.copper_layers.len() <= 2 {
            metrics.push(MetricResult::not_applicable(
                "outer_layer_hs_exposure",
                1.0,
                "two-layer board: no inner layers available",
            ));
        } else if hs_net_ids.is_empty() {
            metrics.push(MetricResult::not_applicable(
                "outer_layer_hs_exposure",
                1.0,
                no_hs_note,
            ));
        } else {
            let mut outer = 0.0;
            let mut total = 0.0;
            for (id, _) in &hs_net_ids {
                for track in ctx.board.tracks.iter().filter(|t| t.net == *id) {
                    let length = track.length();
                    total += length;
                    if track.layer == "F.Cu" || track.layer == "B.Cu" {
                        outer += length;
                    }
                }
            }
            if total > 1e-9 {
                let ratio = outer / total;
                metrics.push(MetricResult::new(
                    "outer_layer_hs_exposure",
                    ratio,
                    "ratio",
                    1.0 - ratio,
                    1.0,
                ));
            } else {
                metrics.push(MetricResult::not_applicable(
                    "outer_layer_hs_exposure",
                    1.0,
                    "high-speed nets have no routed tracks",
                ));
            }
        }

        // connector_shield_grounding: connectors must tie to ground with
        // nearby stitching vias.
        let roles = ctx.roles;
        match (classes, roles) {
            (Some(classes), Some(roles)) => {
                let connectors: Vec<&crate::board::Footprint> = ctx
                    .board
                    .footprints
                    .iter()
                    .filter(|f| roles.get(&f.reference) == Some(&crate::roles::Role::Connector))
                    .collect();
                if connectors.is_empty() {
                    metrics.push(MetricResult::not_applicable(
                        "connector_shield_grounding",
                        1.0,
                        "no connectors declared (type=\"connector\")",
                    ));
                } else {
                    let mut ok = 0usize;
                    let mut worst = Vec::new();
                    for connector in &connectors {
                        let grounded = connector.pads.iter().any(|pad| {
                            pad.net_name
                                .as_deref()
                                .and_then(|n| classes.get(n))
                                .map(|info| info.is_ground)
                                .unwrap_or(false)
                        });
                        let nearby_gnd_vias = ground_vias
                            .iter()
                            .filter(|v| {
                                v.at.dist(&connector.at)
                                    <= 2.0 + connector.bbox_half.0.max(connector.bbox_half.1)
                            })
                            .count();
                        if grounded && nearby_gnd_vias >= 2 {
                            ok += 1;
                        } else {
                            worst.push(WorstEntry {
                                label: connector.reference.clone(),
                                value: nearby_gnd_vias as f64,
                            });
                        }
                    }
                    let ratio = ok as f64 / connectors.len() as f64;
                    metrics.push(
                        MetricResult::new(
                            "connector_shield_grounding",
                            ratio,
                            "ratio",
                            norm::ratio_clamp(ratio),
                            1.0,
                        )
                        .with_worst(worst, false),
                    );
                }
            }
            _ => metrics.push(MetricResult::not_applicable(
                "connector_shield_grounding",
                1.0,
                netlist_note,
            )),
        }

        CategoryResult::new("emi", "EMI / EMC", weight, metrics)
    }
}
