//! Power integrity metrics, driven by declared per-io currents and
//! `Power`/`Ground` net kinds.

use std::collections::BTreeMap;

use crate::model::{CategoryResult, MetricResult, WorstEntry};
use crate::net_graph::point_in_polygon;
use crate::norm;
use crate::stackup::{StackupGeometry, plane_layers};

use super::{ScoreContext, ScorePass};

pub struct PowerPass;

/// IPC-2152-style required trace width (mm) for a current (A) at ~10 C rise,
/// given copper thickness (mm). Uses the external-layer fit
/// I = 0.048 * dT^0.44 * A^0.725 with A in mil^2.
pub fn required_width_mm(current_a: f64, copper_thickness_mm: f64) -> f64 {
    if current_a <= 0.0 {
        return 0.0;
    }
    let dt: f64 = 10.0;
    let k = 0.048;
    let area_mil2 = (current_a / (k * dt.powf(0.44))).powf(1.0 / 0.725);
    let thickness_mil = copper_thickness_mm / 0.0254;
    if thickness_mil <= 0.0 {
        return f64::INFINITY;
    }
    (area_mil2 / thickness_mil) * 0.0254
}

fn polygon_area(points: &[crate::board::Point]) -> f64 {
    if points.len() < 3 {
        return 0.0;
    }
    let mut area = 0.0;
    let n = points.len();
    for i in 0..n {
        let j = (i + 1) % n;
        area += points[i].x * points[j].y - points[j].x * points[i].y;
    }
    area.abs() / 2.0
}

impl ScorePass for PowerPass {
    fn id(&self) -> &'static str {
        "power_integrity"
    }

    fn run(&self, ctx: &ScoreContext) -> CategoryResult {
        let mut metrics = Vec::new();
        let weight = ctx.weights.power_integrity;
        let netlist_note = "netlist unavailable: declarative net classification required";

        let Some(classes) = ctx.net_classes else {
            for id in [
                "trace_current_capacity",
                "current_budget_margin",
                "power_net_width_consistency",
                "decoupling_loop",
                "plane_coverage",
                "power_via_count",
                "power_gnd_plane_pairing",
            ] {
                metrics.push(MetricResult::not_applicable(id, 1.0, netlist_note));
            }
            return CategoryResult::new("power_integrity", "Power integrity", weight, metrics);
        };

        let geometry = StackupGeometry::from_board(ctx.board);
        let copper_t = |layer: &str| {
            geometry
                .as_ref()
                .and_then(|g| g.copper_thickness(layer))
                .unwrap_or(0.035)
        };

        // Nets with declared current, by board net id.
        let current_nets: Vec<(i64, &str, f64)> = ctx
            .board
            .nets
            .iter()
            .filter_map(|(&id, name)| {
                classes.get(name).and_then(|info| {
                    info.sink_total_amps
                        .or(info.source_total_amps)
                        .map(|amps| (id, name.as_str(), amps))
                })
            })
            .collect();

        // trace_current_capacity: min track width per current-carrying net vs
        // the IPC-2152 requirement for the net's total declared current.
        // Conservative: branch segments carry less than the total.
        if current_nets.is_empty() {
            metrics.push(MetricResult::not_applicable(
                "trace_current_capacity",
                4.0,
                "no io() current declarations on any net",
            ));
        } else {
            let mut worst_ratio = f64::INFINITY;
            let mut worst = Vec::new();
            let mut any = false;
            for (id, name, amps) in &current_nets {
                let tracks: Vec<&crate::board::Track> =
                    ctx.board.tracks.iter().filter(|t| t.net == *id).collect();
                let has_zone = ctx.net_stats.get(id).map(|s| s.has_zone).unwrap_or(false);
                if tracks.is_empty() || has_zone {
                    // Plane-fed nets are judged by plane_coverage instead.
                    continue;
                }
                any = true;
                let min_width = tracks.iter().map(|t| t.width).fold(f64::INFINITY, f64::min);
                let layer = &tracks
                    .iter()
                    .min_by(|a, b| {
                        a.width
                            .partial_cmp(&b.width)
                            .unwrap_or(std::cmp::Ordering::Equal)
                    })
                    .unwrap()
                    .layer;
                let required = required_width_mm(*amps, copper_t(layer));
                let ratio = if required <= 1e-9 {
                    1.0
                } else {
                    min_width / required
                };
                worst_ratio = worst_ratio.min(ratio);
                if ratio < 1.5 {
                    worst.push(WorstEntry {
                        label: (*name).to_string(),
                        value: ratio,
                    });
                }
            }
            if any {
                metrics.push(
                    MetricResult::new(
                        "trace_current_capacity",
                        worst_ratio,
                        "width_ratio",
                        norm::target_band(worst_ratio, 1.0, f64::INFINITY, 0.7, 0.0),
                        4.0,
                    )
                    .with_worst(worst, false)
                    .with_note(
                        "net-total current vs narrowest segment (per-branch flow analysis planned)",
                    ),
                );
            } else {
                metrics.push(MetricResult::not_applicable(
                    "trace_current_capacity",
                    4.0,
                    "current-declared nets are plane-fed or unrouted",
                ));
            }
        }

        // current_budget_margin: source headroom per net (scoring complement
        // of the blocking ERC check).
        {
            let budgets: Vec<(&str, f64)> = ctx
                .board
                .nets.values().filter_map(|name| {
                    let info = classes.get(name)?;
                    let sink = info.sink_total_amps?;
                    let source = info.source_total_amps?;
                    (sink > 0.0).then(|| (name.as_str(), source / sink))
                })
                .collect();
            if budgets.is_empty() {
                metrics.push(MetricResult::not_applicable(
                    "current_budget_margin",
                    1.0,
                    "no net declares both source and sink currents",
                ));
            } else {
                let worst_margin = budgets
                    .iter()
                    .map(|(_, m)| *m)
                    .fold(f64::INFINITY, f64::min);
                let worst: Vec<WorstEntry> = budgets
                    .iter()
                    .map(|(name, margin)| WorstEntry {
                        label: (*name).to_string(),
                        value: *margin,
                    })
                    .collect();
                metrics.push(
                    MetricResult::new(
                        "current_budget_margin",
                        worst_margin,
                        "ratio",
                        norm::target_band(worst_margin, 1.2, f64::INFINITY, 0.2, 0.0),
                        1.0,
                    )
                    .with_worst(worst, false),
                );
            }
        }

        // power_net_width_consistency: power nets should keep a consistent
        // (wide) trunk; ratio of min/max width per net.
        {
            let power_net_ids: Vec<(i64, &str)> = ctx
                .board
                .nets
                .iter()
                .filter_map(|(&id, name)| {
                    classes
                        .get(name)
                        .filter(|info| info.is_power)
                        .map(|_| (id, name.as_str()))
                })
                .collect();
            let mut ratios = Vec::new();
            let mut worst = Vec::new();
            for (id, name) in &power_net_ids {
                let widths: Vec<f64> = ctx
                    .board
                    .tracks
                    .iter()
                    .filter(|t| t.net == *id)
                    .map(|t| t.width)
                    .collect();
                if widths.is_empty() {
                    continue;
                }
                let min = widths.iter().cloned().fold(f64::INFINITY, f64::min);
                let max = widths.iter().cloned().fold(0.0f64, f64::max);
                let ratio = if max > 1e-9 { min / max } else { 1.0 };
                ratios.push(ratio);
                if ratio < 0.99 {
                    worst.push(WorstEntry {
                        label: (*name).to_string(),
                        value: ratio,
                    });
                }
            }
            if ratios.is_empty() {
                metrics.push(MetricResult::not_applicable(
                    "power_net_width_consistency",
                    1.0,
                    "no routed Power-kind nets",
                ));
            } else {
                let mean = ratios.iter().sum::<f64>() / ratios.len() as f64;
                metrics.push(
                    MetricResult::new(
                        "power_net_width_consistency",
                        mean,
                        "ratio",
                        norm::ratio_clamp(mean),
                        1.0,
                    )
                    .with_worst(worst, false),
                );
            }
        }

        // decoupling_loop: declared capacitors bridging Power and Ground; how
        // close is each pad to its plane connection (via or in-zone).
        match ctx.roles {
            Some(roles) => {
                let caps: Vec<&crate::board::Footprint> = ctx
                    .board
                    .footprints
                    .iter()
                    .filter(|f| roles.get(&f.reference) == Some(&crate::roles::Role::Capacitor))
                    .filter(|f| {
                        let mut has_power = false;
                        let mut has_ground = false;
                        for pad in &f.pads {
                            if let Some(info) = pad.net_name.as_deref().and_then(|n| classes.get(n))
                            {
                                has_power |= info.is_power;
                                has_ground |= info.is_ground;
                            }
                        }
                        has_power && has_ground
                    })
                    .collect();
                if caps.is_empty() {
                    metrics.push(MetricResult::not_applicable(
                        "decoupling_loop",
                        2.0,
                        "no declared capacitors bridging Power and Ground",
                    ));
                } else {
                    let mut loop_sum = 0.0;
                    let mut worst = Vec::new();
                    for cap in &caps {
                        let mut cap_loop = 0.0;
                        for pad in &cap.pads {
                            let Some(net_id) = pad.net else { continue };
                            let Some(info) = pad.net_name.as_deref().and_then(|n| classes.get(n))
                            else {
                                continue;
                            };
                            if !info.is_power && !info.is_ground {
                                continue;
                            }
                            // Distance to plane connection: nearest same-net
                            // via, or zero if the pad sits in a same-net fill.
                            let in_zone = ctx
                                .board
                                .zones
                                .iter()
                                .filter(|z| z.net == net_id)
                                .flat_map(|z| z.filled_polygons.iter())
                                .any(|poly| point_in_polygon(pad.at, &poly.points));
                            if in_zone {
                                continue;
                            }
                            let nearest_via = ctx
                                .board
                                .vias
                                .iter()
                                .filter(|v| v.net == net_id)
                                .map(|v| v.at.dist(&pad.at))
                                .fold(f64::INFINITY, f64::min);
                            cap_loop += if nearest_via.is_finite() {
                                nearest_via
                            } else {
                                5.0
                            };
                        }
                        loop_sum += cap_loop;
                        if cap_loop > 0.5 {
                            worst.push(WorstEntry {
                                label: cap.reference.clone(),
                                value: cap_loop,
                            });
                        }
                    }
                    let mean = loop_sum / caps.len() as f64;
                    metrics.push(
                        MetricResult::new(
                            "decoupling_loop",
                            mean,
                            "mm",
                            norm::decay(mean, 2.0),
                            2.0,
                        )
                        .with_worst(worst, true),
                    );
                }
            }
            None => metrics.push(MetricResult::not_applicable(
                "decoupling_loop",
                2.0,
                netlist_note,
            )),
        }

        // plane_coverage: reference plane fill area vs board area.
        {
            let planes = plane_layers(ctx.board, Some(classes));
            match ctx.board.outline_bbox() {
                Some((min, max)) if !planes.is_empty() => {
                    let board_area = ((max.x - min.x) * (max.y - min.y)).max(1e-9);
                    let mut best_layer_cov = 0.0f64;
                    for layer in &planes {
                        let area: f64 = ctx
                            .board
                            .zones
                            .iter()
                            .filter(|z| {
                                classes
                                    .get(ctx.board.net_name(z.net))
                                    .map(|info| info.is_ground || info.is_power)
                                    .unwrap_or(false)
                            })
                            .flat_map(|z| z.filled_polygons.iter())
                            .filter(|poly| &poly.layer == layer)
                            .map(|poly| polygon_area(&poly.points))
                            .sum();
                        best_layer_cov = best_layer_cov.max(area / board_area);
                    }
                    metrics.push(MetricResult::new(
                        "plane_coverage",
                        best_layer_cov,
                        "ratio",
                        norm::ratio_clamp(best_layer_cov / 0.7),
                        1.0,
                    ));
                }
                Some(_) => metrics.push(MetricResult::not_applicable(
                    "plane_coverage",
                    1.0,
                    "no ground/power plane fills present",
                )),
                None => metrics.push(MetricResult::not_applicable(
                    "plane_coverage",
                    1.0,
                    "no board outline (Edge.Cuts) found",
                )),
            }
        }

        // power_via_count: power nets crossing layers should do so with
        // enough vias to share current.
        {
            let mut ratios = Vec::new();
            let mut worst = Vec::new();
            for (&id, name) in &ctx.board.nets {
                let Some(info) = classes.get(name) else {
                    continue;
                };
                if !info.is_power {
                    continue;
                }
                let Some(stats) = ctx.net_stats.get(&id) else {
                    continue;
                };
                if stats.layers_used.len() < 2 && !stats.has_zone {
                    continue;
                }
                let vias = stats.via_count;
                let target = info
                    .sink_total_amps
                    .map(|amps| (amps / 0.5).ceil().max(2.0) as usize)
                    .unwrap_or(2);
                let ratio = (vias as f64 / target as f64).min(1.0);
                ratios.push(ratio);
                if ratio < 1.0 {
                    worst.push(WorstEntry {
                        label: name.clone(),
                        value: vias as f64,
                    });
                }
            }
            if ratios.is_empty() {
                metrics.push(MetricResult::not_applicable(
                    "power_via_count",
                    1.0,
                    "no power nets crossing layers",
                ));
            } else {
                let mean = ratios.iter().sum::<f64>() / ratios.len() as f64;
                metrics.push(
                    MetricResult::new("power_via_count", mean, "ratio", mean, 1.0)
                        .with_worst(worst, false),
                );
            }
        }

        // power_gnd_plane_pairing: adjacent power/ground plane pair in the
        // stack provides interplane capacitance.
        {
            if ctx.board.copper_layers.len() <= 2 {
                metrics.push(MetricResult::not_applicable(
                    "power_gnd_plane_pairing",
                    1.0,
                    "two-layer board",
                ));
            } else {
                // Layer -> carries ground fill / power fill.
                let mut layer_kind: BTreeMap<&str, (bool, bool)> = BTreeMap::new();
                for zone in &ctx.board.zones {
                    let Some(info) = classes.get(ctx.board.net_name(zone.net)) else {
                        continue;
                    };
                    for poly in &zone.filled_polygons {
                        let entry = layer_kind.entry(poly.layer.as_str()).or_default();
                        entry.0 |= info.is_ground;
                        entry.1 |= info.is_power;
                    }
                }
                let mut paired = false;
                for pair in ctx.board.copper_layers.windows(2) {
                    let a = layer_kind
                        .get(pair[0].as_str())
                        .copied()
                        .unwrap_or_default();
                    let b = layer_kind
                        .get(pair[1].as_str())
                        .copied()
                        .unwrap_or_default();
                    if (a.0 && b.1) || (a.1 && b.0) {
                        paired = true;
                    }
                }
                if layer_kind.is_empty() {
                    metrics.push(MetricResult::not_applicable(
                        "power_gnd_plane_pairing",
                        1.0,
                        "no plane fills present",
                    ));
                } else {
                    metrics.push(MetricResult::new(
                        "power_gnd_plane_pairing",
                        if paired { 1.0 } else { 0.0 },
                        "bool",
                        if paired { 1.0 } else { 0.0 },
                        1.0,
                    ));
                }
            }
        }

        CategoryResult::new("power_integrity", "Power integrity", weight, metrics)
    }
}
