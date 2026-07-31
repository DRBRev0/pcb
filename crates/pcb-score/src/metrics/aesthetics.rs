//! Convention/aesthetics metrics: angle discipline, width consistency,
//! grid adherence, orphan copper.

use std::collections::BTreeSet;

use crate::model::{CategoryResult, MetricResult, WorstEntry};
use crate::norm;

use super::{ScoreContext, ScorePass};

pub struct AestheticsPass;

impl ScorePass for AestheticsPass {
    fn id(&self) -> &'static str {
        "aesthetics"
    }

    fn run(&self, ctx: &ScoreContext) -> CategoryResult {
        let mut metrics = Vec::new();
        let weight = ctx.weights.aesthetics;

        if ctx.board.tracks.is_empty() {
            for id in [
                "angle_discipline",
                "width_consistency",
                "grid_adherence",
                "orphan_copper",
            ] {
                metrics.push(MetricResult::not_applicable(id, 1.0, "no routed tracks"));
            }
            return CategoryResult::new("aesthetics", "Aesthetics", weight, metrics);
        }

        // angle_discipline: routed length at multiples of 45 degrees (arcs
        // count as disciplined).
        {
            let mut disciplined = 0.0;
            let mut total = 0.0;
            for track in &ctx.board.tracks {
                let length = track.length();
                if length < 1e-9 {
                    continue;
                }
                total += length;
                let angle = (track.end.y - track.start.y)
                    .atan2(track.end.x - track.start.x)
                    .to_degrees();
                let rem = (angle.rem_euclid(45.0)).min(45.0 - angle.rem_euclid(45.0));
                if rem < 0.5 {
                    disciplined += length;
                }
            }
            disciplined += ctx.board.arcs.iter().map(|a| a.length()).sum::<f64>();
            total += ctx.board.arcs.iter().map(|a| a.length()).sum::<f64>();
            let ratio = if total > 1e-9 {
                disciplined / total
            } else {
                1.0
            };
            metrics.push(MetricResult::new(
                "angle_discipline",
                ratio,
                "ratio",
                norm::ratio_clamp(ratio),
                2.0,
            ));
        }

        // width_consistency: nets should use at most two widths (trunk +
        // neckdown).
        {
            let mut conforming = 0usize;
            let mut counted = 0usize;
            let mut worst = Vec::new();
            for stats in ctx.net_stats.values() {
                let widths: BTreeSet<u64> = ctx
                    .board
                    .tracks
                    .iter()
                    .filter(|t| t.net == stats.net)
                    .map(|t| (t.width * 1000.0).round() as u64)
                    .collect();
                if widths.is_empty() {
                    continue;
                }
                counted += 1;
                if widths.len() <= 2 {
                    conforming += 1;
                } else {
                    worst.push(WorstEntry {
                        label: stats.name.clone(),
                        value: widths.len() as f64,
                    });
                }
            }
            if counted == 0 {
                metrics.push(MetricResult::not_applicable(
                    "width_consistency",
                    1.0,
                    "no routed nets",
                ));
            } else {
                let ratio = conforming as f64 / counted as f64;
                metrics.push(
                    MetricResult::new(
                        "width_consistency",
                        ratio,
                        "ratio",
                        norm::ratio_clamp(ratio),
                        1.0,
                    )
                    .with_worst(worst, true),
                );
            }
        }

        // grid_adherence: endpoints on a 0.025 mm grid.
        {
            let mut on_grid = 0usize;
            let mut total = 0usize;
            for track in &ctx.board.tracks {
                for p in [track.start, track.end] {
                    total += 2;
                    for coord in [p.x, p.y] {
                        let scaled = coord / 0.025;
                        if (scaled - scaled.round()).abs() < 1e-6 {
                            on_grid += 1;
                        }
                    }
                }
            }
            let ratio = if total > 0 {
                on_grid as f64 / total as f64
            } else {
                1.0
            };
            metrics.push(MetricResult::new(
                "grid_adherence",
                ratio,
                "ratio",
                norm::ratio_clamp(ratio),
                0.5,
            ));
        }

        // orphan_copper: tracks/vias on net 0 or nameless nets.
        {
            let orphans = ctx
                .board
                .tracks
                .iter()
                .map(|t| t.net)
                .chain(ctx.board.vias.iter().map(|v| v.net))
                .filter(|&net| net == 0 || ctx.board.net_name(net).is_empty())
                .count();
            metrics.push(MetricResult::new(
                "orphan_copper",
                orphans as f64,
                "count",
                norm::decay(orphans as f64, 2.0),
                1.0,
            ));
        }

        CategoryResult::new("aesthetics", "Aesthetics", weight, metrics)
    }
}
