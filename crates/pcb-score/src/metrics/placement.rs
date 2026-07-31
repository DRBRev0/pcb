//! Placement quality metrics (routing difficulty predictors).

use std::collections::BTreeMap;

use crate::board::Point;
use crate::model::{CategoryResult, MetricResult, WorstEntry};
use crate::norm;
use crate::roles::Role;

use super::{ScoreContext, ScorePass};

pub struct PlacementPass;

fn segments_intersect(a1: Point, a2: Point, b1: Point, b2: Point) -> bool {
    let cross =
        |o: Point, p: Point, q: Point| (p.x - o.x) * (q.y - o.y) - (p.y - o.y) * (q.x - o.x);
    let d1 = cross(b1, b2, a1);
    let d2 = cross(b1, b2, a2);
    let d3 = cross(a1, a2, b1);
    let d4 = cross(a1, a2, b2);
    ((d1 > 0.0 && d2 < 0.0) || (d1 < 0.0 && d2 > 0.0))
        && ((d3 > 0.0 && d4 < 0.0) || (d3 < 0.0 && d4 > 0.0))
}

/// MST edges over each net's pads (the pre-route airwire set).
fn airwire_edges(ctx: &ScoreContext) -> Vec<(i64, Point, Point)> {
    let mut edges = Vec::new();
    for &net_id in ctx.board.nets.keys() {
        let pads: Vec<Point> = ctx
            .board
            .footprints
            .iter()
            .flat_map(|f| f.pads.iter())
            .filter(|p| p.net == Some(net_id))
            .map(|p| p.at)
            .collect();
        if pads.len() < 2 {
            continue;
        }
        // Prim's MST, recording edges.
        let n = pads.len();
        let mut in_tree = vec![false; n];
        let mut best = vec![(f64::INFINITY, 0usize); n];
        in_tree[0] = true;
        for i in 1..n {
            best[i] = (pads[0].dist(&pads[i]), 0);
        }
        for _ in 1..n {
            let mut next = None;
            for i in 0..n {
                if !in_tree[i] && next.map(|j: usize| best[i].0 < best[j].0).unwrap_or(true) {
                    next = Some(i);
                }
            }
            let Some(next) = next else { break };
            in_tree[next] = true;
            edges.push((net_id, pads[best[next].1], pads[next]));
            for i in 0..n {
                if !in_tree[i] {
                    let d = pads[next].dist(&pads[i]);
                    if d < best[i].0 {
                        best[i] = (d, next);
                    }
                }
            }
        }
    }
    edges
}

impl ScorePass for PlacementPass {
    fn id(&self) -> &'static str {
        "placement"
    }

    fn run(&self, ctx: &ScoreContext) -> CategoryResult {
        let mut metrics = Vec::new();
        let weight = ctx.weights.placement;

        // airwire_crossings: intersections of the pre-route MST airwire set,
        // a classic routability predictor.
        {
            let edges = airwire_edges(ctx);
            let routable_nets = ctx.net_stats.values().filter(|s| s.pad_count >= 2).count();
            if edges.is_empty() || routable_nets == 0 {
                metrics.push(MetricResult::not_applicable(
                    "airwire_crossings",
                    2.0,
                    "no multi-pad nets placed",
                ));
            } else {
                let mut crossings = 0usize;
                for i in 0..edges.len() {
                    for j in (i + 1)..edges.len() {
                        if edges[i].0 != edges[j].0
                            && segments_intersect(edges[i].1, edges[i].2, edges[j].1, edges[j].2)
                        {
                            crossings += 1;
                        }
                    }
                }
                let per_net = crossings as f64 / routable_nets as f64;
                metrics.push(MetricResult::new(
                    "airwire_crossings",
                    per_net,
                    "count_per_net",
                    norm::decay(per_net, 1.0),
                    2.0,
                ));
            }
        }

        // connector_edge_placement: connectors belong near the board edge.
        match ctx.roles {
            Some(roles) if !ctx.board.outline.is_empty() => {
                let connectors: Vec<_> = ctx
                    .board
                    .footprints
                    .iter()
                    .filter(|f| roles.get(&f.reference) == Some(&Role::Connector))
                    .collect();
                if connectors.is_empty() {
                    metrics.push(MetricResult::not_applicable(
                        "connector_edge_placement",
                        1.0,
                        "no connectors declared (type=\"connector\")",
                    ));
                } else {
                    let mut sum = 0.0;
                    let mut worst = Vec::new();
                    for connector in &connectors {
                        let d = ctx
                            .board
                            .outline
                            .iter()
                            .map(|seg| {
                                let (dx, dy) = (seg.end.x - seg.start.x, seg.end.y - seg.start.y);
                                let len2 = dx * dx + dy * dy;
                                let t = if len2 < 1e-18 {
                                    0.0
                                } else {
                                    (((connector.at.x - seg.start.x) * dx
                                        + (connector.at.y - seg.start.y) * dy)
                                        / len2)
                                        .clamp(0.0, 1.0)
                                };
                                connector.at.dist(&Point {
                                    x: seg.start.x + t * dx,
                                    y: seg.start.y + t * dy,
                                })
                            })
                            .fold(f64::INFINITY, f64::min);
                        let d = (d - connector.bbox_half.0.max(connector.bbox_half.1)).max(0.0);
                        sum += d;
                        if d > 1.0 {
                            worst.push(WorstEntry {
                                label: connector.reference.clone(),
                                value: d,
                            });
                        }
                    }
                    let mean = sum / connectors.len() as f64;
                    metrics.push(
                        MetricResult::new(
                            "connector_edge_placement",
                            mean,
                            "mm",
                            norm::decay(mean, 3.0),
                            1.0,
                        )
                        .with_worst(worst, true),
                    );
                }
            }
            Some(_) => metrics.push(MetricResult::not_applicable(
                "connector_edge_placement",
                1.0,
                "no board outline (Edge.Cuts) found",
            )),
            None => metrics.push(MetricResult::not_applicable(
                "connector_edge_placement",
                1.0,
                "netlist unavailable: declarative roles required",
            )),
        }

        // component_density: footprint extent area vs board area.
        match ctx.board.outline_bbox() {
            Some((min, max)) if !ctx.board.footprints.is_empty() => {
                let board_area = ((max.x - min.x) * (max.y - min.y)).max(1e-9);
                let component_area: f64 = ctx
                    .board
                    .footprints
                    .iter()
                    .map(|f| 4.0 * f.bbox_half.0 * f.bbox_half.1)
                    .sum();
                let density = component_area / board_area;
                metrics.push(MetricResult::new(
                    "component_density",
                    density,
                    "ratio",
                    norm::target_band(density, 0.05, 0.6, 0.05, 0.3),
                    1.0,
                ));
            }
            _ => metrics.push(MetricResult::not_applicable(
                "component_density",
                1.0,
                "needs an outline and placed footprints",
            )),
        }

        // pin_density_hotspots: worst pad count in a 10x10 mm window.
        {
            let pads: Vec<Point> = ctx
                .board
                .footprints
                .iter()
                .flat_map(|f| f.pads.iter())
                .map(|p| p.at)
                .collect();
            if pads.is_empty() {
                metrics.push(MetricResult::not_applicable(
                    "pin_density_hotspots",
                    1.0,
                    "no pads placed",
                ));
            } else {
                let mut cells: BTreeMap<(i64, i64), usize> = BTreeMap::new();
                for p in &pads {
                    *cells
                        .entry(((p.x / 10.0).floor() as i64, (p.y / 10.0).floor() as i64))
                        .or_default() += 1;
                }
                let worst_cell = cells.values().cloned().max().unwrap_or(0) as f64;
                // Routability threshold scales with layer count.
                let layers = ctx.board.copper_layers.len().max(1) as f64;
                let threshold = 40.0 * layers;
                metrics.push(MetricResult::new(
                    "pin_density_hotspots",
                    worst_cell,
                    "pads_per_cm2_window",
                    norm::target_band(worst_cell, 0.0, threshold, 0.0, threshold),
                    1.0,
                ));
            }
        }

        CategoryResult::new("placement", "Placement", weight, metrics)
    }
}
