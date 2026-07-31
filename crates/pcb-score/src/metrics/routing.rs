//! Routing efficiency metrics (§ routing_efficiency of the metric catalog).

use crate::model::{CategoryResult, MetricResult, WorstEntry};
use crate::net_graph::NetStats;
use crate::norm;

use super::{ScoreContext, ScorePass};

pub struct RoutingPass;

/// Length-weighted mean detour and per-net worst offenders.
fn detour_metrics(stats: &[&NetStats]) -> Option<(f64, Vec<WorstEntry>)> {
    let mut weighted = 0.0;
    let mut weight_sum = 0.0;
    let mut worst = Vec::new();
    for stat in stats {
        if let Some(detour) = stat.detour() {
            weighted += detour * stat.mst_length;
            weight_sum += stat.mst_length;
            worst.push(WorstEntry {
                label: stat.name.clone(),
                value: detour,
            });
        }
    }
    (weight_sum > 1e-9).then(|| (weighted / weight_sum, worst))
}

/// Gini coefficient of a distribution (0 = perfectly even).
fn gini(values: &[f64]) -> f64 {
    let n = values.len();
    if n < 2 {
        return 0.0;
    }
    let mut sorted = values.to_vec();
    sorted.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
    let total: f64 = sorted.iter().sum();
    if total <= 1e-12 {
        return 0.0;
    }
    let mut cum = 0.0;
    let mut area = 0.0;
    for value in &sorted {
        cum += value;
        area += cum;
    }
    // area / (n * total) is the Lorenz area estimate; 0.5 for equality.
    1.0 - 2.0 * (area / (n as f64 * total)) + 1.0 / n as f64
}

impl ScorePass for RoutingPass {
    fn id(&self) -> &'static str {
        "routing_efficiency"
    }

    fn run(&self, ctx: &ScoreContext) -> CategoryResult {
        let mut metrics = Vec::new();
        let stats: Vec<&NetStats> = ctx.net_stats.values().collect();
        let routable: Vec<&NetStats> = stats.iter().copied().filter(|s| s.pad_count >= 2).collect();

        // detour_factor: routed length vs Euclidean MST lower bound.
        match detour_metrics(&routable) {
            Some((mean_detour, worst)) => {
                metrics.push(
                    MetricResult::new(
                        "detour_factor",
                        mean_detour,
                        "ratio",
                        norm::target_band(mean_detour, 0.0, 1.25, 0.0, 1.25),
                        4.0,
                    )
                    .with_worst(worst, true),
                );
            }
            None => metrics.push(MetricResult::not_applicable(
                "detour_factor",
                4.0,
                "no fully routed multi-pad nets yet",
            )),
        }

        // total_wire_length: raw aggregate with the same detour normalization.
        let total_routed: f64 = stats.iter().map(|s| s.routed_length).sum();
        let total_mst: f64 = routable.iter().map(|s| s.mst_length).sum();
        if total_mst > 1e-9 {
            let ratio = total_routed / total_mst;
            metrics.push(MetricResult::new(
                "total_wire_length",
                total_routed,
                "mm",
                norm::target_band(ratio, 0.0, 1.25, 0.0, 1.25),
                2.0,
            ));
        } else {
            metrics.push(MetricResult::not_applicable(
                "total_wire_length",
                2.0,
                "no multi-pad nets to route",
            ));
        }

        // via_count_per_net: mean vias per routed net, excluding plane nets
        // (their vias are mostly stitching).
        let via_nets: Vec<&NetStats> = routable.iter().copied().filter(|s| !s.has_zone).collect();
        if via_nets.is_empty() {
            metrics.push(MetricResult::not_applicable(
                "via_count_per_net",
                3.0,
                "no zone-free multi-pad nets",
            ));
        } else {
            let mean =
                via_nets.iter().map(|s| s.via_count as f64).sum::<f64>() / via_nets.len() as f64;
            let worst: Vec<WorstEntry> = via_nets
                .iter()
                .filter(|s| s.via_count > 0)
                .map(|s| WorstEntry {
                    label: s.name.clone(),
                    value: s.via_count as f64,
                })
                .collect();
            metrics.push(
                MetricResult::new(
                    "via_count_per_net",
                    mean,
                    "count",
                    norm::decay(mean, 2.0),
                    3.0,
                )
                .with_worst(worst, true),
            );
        }

        // unnecessary_layer_usage: nets spreading over more than 2 copper layers.
        if routable.is_empty() {
            metrics.push(MetricResult::not_applicable(
                "unnecessary_layer_usage",
                2.0,
                "no multi-pad nets",
            ));
        } else {
            let spread = routable.iter().filter(|s| s.layers_used.len() > 2).count() as f64;
            let ratio = spread / routable.len() as f64;
            metrics.push(MetricResult::new(
                "unnecessary_layer_usage",
                ratio,
                "ratio",
                1.0 - ratio,
                2.0,
            ));
        }

        // segment_fragmentation: mergeable collinear pairs / total segments.
        let total_segments: usize = stats.iter().map(|s| s.segment_count).sum();
        if total_segments == 0 {
            metrics.push(MetricResult::not_applicable(
                "segment_fragmentation",
                1.0,
                "no routed segments",
            ));
        } else {
            let mergeable: usize = stats.iter().map(|s| s.mergeable_pairs).sum();
            let ratio = mergeable as f64 / total_segments as f64;
            metrics.push(MetricResult::new(
                "segment_fragmentation",
                ratio,
                "ratio",
                1.0 - norm::ratio_clamp(ratio),
                1.0,
            ));
        }

        // meander_score: sharp direction reversals per routed net.
        if routable.is_empty() || total_segments == 0 {
            metrics.push(MetricResult::not_applicable(
                "meander_score",
                2.0,
                "no routed segments",
            ));
        } else {
            let reversals: usize = stats.iter().map(|s| s.direction_reversals).sum();
            let mean = reversals as f64 / routable.len() as f64;
            let worst: Vec<WorstEntry> = stats
                .iter()
                .filter(|s| s.direction_reversals > 0)
                .map(|s| WorstEntry {
                    label: s.name.clone(),
                    value: s.direction_reversals as f64,
                })
                .collect();
            metrics.push(
                MetricResult::new("meander_score", mean, "count", norm::decay(mean, 3.0), 2.0)
                    .with_worst(worst, true),
            );
        }

        // stub_length: dangling copper (worst offenders listed per net).
        let stub_total: f64 = stats.iter().map(|s| s.stub_length).sum();
        let worst_stubs: Vec<WorstEntry> = stats
            .iter()
            .filter(|s| s.stub_length > 0.0)
            .map(|s| WorstEntry {
                label: s.name.clone(),
                value: s.stub_length,
            })
            .collect();
        metrics.push(
            MetricResult::new(
                "stub_length",
                stub_total,
                "mm",
                norm::decay(stub_total, 2.0),
                2.0,
            )
            .with_worst(worst_stubs, true),
        );

        // routing_layer_balance: Gini of routed length across copper layers
        // that carry routing (multi-layer boards only).
        let mut per_layer: Vec<f64> = Vec::new();
        for layer in &ctx.board.copper_layers {
            let length: f64 = ctx
                .board
                .tracks
                .iter()
                .filter(|t| &t.layer == layer)
                .map(|t| t.length())
                .sum();
            per_layer.push(length);
        }
        let signal_layers = per_layer.iter().filter(|&&l| l > 0.0).count();
        if ctx.board.copper_layers.len() < 2 || signal_layers < 2 {
            metrics.push(MetricResult::not_applicable(
                "routing_layer_balance",
                1.0,
                "routing on fewer than two copper layers",
            ));
        } else {
            let g = gini(&per_layer);
            metrics.push(MetricResult::new(
                "routing_layer_balance",
                g,
                "gini",
                1.0 - norm::ratio_clamp(g),
                1.0,
            ));
        }

        CategoryResult::new(
            "routing_efficiency",
            "Routing efficiency",
            ctx.weights.routing_efficiency,
            metrics,
        )
    }
}
