//! Manufacturability metrics computable from the parsed board. Full
//! morphological copper analysis (thin features/gaps, silkscreen overlap)
//! remains with KiCad DRC and `pcb ipc dfm`; these metrics cover the
//! geometry the score can check directly.

use crate::model::{CategoryResult, MetricResult, WorstEntry};
use crate::norm;
use crate::stackup::StackupGeometry;

use super::{ScoreContext, ScorePass};

pub struct DfmPass;

/// Conservative fab floor values (mm) used when no design rules are declared.
const MIN_ANNULAR_RING: f64 = 0.125;
const MIN_DRILL: f64 = 0.2;
const MAX_ASPECT_RATIO: f64 = 10.0;

impl ScorePass for DfmPass {
    fn id(&self) -> &'static str {
        "dfm"
    }

    fn run(&self, ctx: &ScoreContext) -> CategoryResult {
        let mut metrics = Vec::new();
        let weight = ctx.weights.dfm;

        // annular_ring_margin / drill_margin / aspect_ratio over vias.
        if ctx.board.vias.is_empty() {
            for id in ["annular_ring_margin", "drill_margin", "via_aspect_ratio"] {
                metrics.push(MetricResult::not_applicable(
                    id,
                    1.0,
                    "no vias on the board",
                ));
            }
        } else {
            let mut min_ring = f64::INFINITY;
            let mut min_drill = f64::INFINITY;
            for via in &ctx.board.vias {
                if via.drill > 0.0 && via.size > 0.0 {
                    min_ring = min_ring.min((via.size - via.drill) / 2.0);
                    min_drill = min_drill.min(via.drill);
                }
            }
            if min_ring.is_finite() {
                metrics.push(MetricResult::new(
                    "annular_ring_margin",
                    min_ring,
                    "mm",
                    norm::ratio_clamp(min_ring / MIN_ANNULAR_RING),
                    2.0,
                ));
                metrics.push(MetricResult::new(
                    "drill_margin",
                    min_drill,
                    "mm",
                    norm::ratio_clamp(min_drill / MIN_DRILL),
                    1.0,
                ));
            } else {
                for id in ["annular_ring_margin", "drill_margin"] {
                    metrics.push(MetricResult::not_applicable(
                        id,
                        1.0,
                        "vias carry no size/drill data",
                    ));
                }
            }

            match StackupGeometry::from_board(ctx.board).and_then(|g| g.total_thickness_mm) {
                Some(thickness) if min_drill.is_finite() => {
                    let aspect = thickness / min_drill;
                    metrics.push(MetricResult::new(
                        "via_aspect_ratio",
                        aspect,
                        "ratio",
                        norm::target_band(aspect, 0.0, MAX_ASPECT_RATIO, 0.0, 4.0),
                        1.0,
                    ));
                }
                _ => metrics.push(MetricResult::not_applicable(
                    "via_aspect_ratio",
                    1.0,
                    "board thickness unknown (no stackup)",
                )),
            }
        }

        // via_in_pad: vias centered inside SMD pads (unfilled via-in-pad risk).
        {
            let smd_pads: Vec<&crate::board::Pad> = ctx
                .board
                .footprints
                .iter()
                .flat_map(|f| f.pads.iter())
                .filter(|p| p.kind == "smd")
                .collect();
            if smd_pads.is_empty() || ctx.board.vias.is_empty() {
                metrics.push(MetricResult::not_applicable(
                    "via_in_pad",
                    1.0,
                    "no SMD pads or no vias",
                ));
            } else {
                let count = ctx
                    .board
                    .vias
                    .iter()
                    .filter(|via| {
                        smd_pads.iter().any(|pad| {
                            (via.at.x - pad.at.x).abs() <= pad.size.0 / 2.0
                                && (via.at.y - pad.at.y).abs() <= pad.size.1 / 2.0
                                // Thermal-pad via farms are intentional.
                                && pad.size.0 * pad.size.1 < 4.0
                        })
                    })
                    .count();
                metrics.push(MetricResult::new(
                    "via_in_pad",
                    count as f64,
                    "count",
                    norm::decay(count as f64, 2.0),
                    1.0,
                ));
            }
        }

        // min_track_width_margin against a conservative fab floor.
        if ctx.board.tracks.is_empty() {
            metrics.push(MetricResult::not_applicable(
                "min_track_width_margin",
                1.0,
                "no routed tracks",
            ));
        } else {
            let min_width = ctx
                .board
                .tracks
                .iter()
                .map(|t| t.width)
                .fold(f64::INFINITY, f64::min);
            metrics.push(MetricResult::new(
                "min_track_width_margin",
                min_width,
                "mm",
                norm::ratio_clamp(min_width / 0.15),
                1.0,
            ));
        }

        // acid_traps: acute copper junctions.
        {
            let acute: usize = ctx.net_stats.values().map(|s| s.acute_junctions).sum();
            let worst: Vec<WorstEntry> = ctx
                .net_stats
                .values()
                .filter(|s| s.acute_junctions > 0)
                .map(|s| WorstEntry {
                    label: s.name.clone(),
                    value: s.acute_junctions as f64,
                })
                .collect();
            metrics.push(
                MetricResult::new(
                    "acid_traps",
                    acute as f64,
                    "count",
                    norm::decay(acute as f64, 5.0),
                    1.0,
                )
                .with_worst(worst, true),
            );
        }

        CategoryResult::new("dfm", "Manufacturability", weight, metrics)
    }
}
