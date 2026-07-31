//! Thermal metrics based on exposed-pad geometry (a physical fact of the
//! footprint, not a naming heuristic).

use crate::board::Pad;
use crate::model::{CategoryResult, MetricResult, WorstEntry};
use crate::norm;
use crate::stackup::plane_layers;

use super::{ScoreContext, ScorePass};

pub struct ThermalPass;

/// SMD pads at least this large (mm^2) are treated as thermal/exposed pads.
const EXPOSED_PAD_MIN_AREA: f64 = 4.0;

fn is_exposed_pad(pad: &Pad) -> bool {
    pad.kind == "smd" && pad.size.0 * pad.size.1 >= EXPOSED_PAD_MIN_AREA
}

fn via_in_pad(pad: &Pad, via: &crate::board::Via) -> bool {
    (via.at.x - pad.at.x).abs() <= pad.size.0 / 2.0
        && (via.at.y - pad.at.y).abs() <= pad.size.1 / 2.0
}

impl ScorePass for ThermalPass {
    fn id(&self) -> &'static str {
        "thermal"
    }

    fn run(&self, ctx: &ScoreContext) -> CategoryResult {
        let mut metrics = Vec::new();
        let weight = ctx.weights.thermal;

        let exposed: Vec<(&str, &Pad)> = ctx
            .board
            .footprints
            .iter()
            .flat_map(|f| f.pads.iter().map(move |p| (f.reference.as_str(), p)))
            .filter(|(_, p)| is_exposed_pad(p))
            .collect();

        if exposed.is_empty() {
            for id in ["thermal_via_fill", "heat_spreading_layers"] {
                metrics.push(MetricResult::not_applicable(
                    id,
                    1.0,
                    "no exposed/thermal pads (large SMD pads) found",
                ));
            }
            return CategoryResult::new("thermal", "Thermal", weight, metrics);
        }

        // thermal_via_fill: vias inside each exposed pad vs ~1 via per mm^2.
        {
            let mut ratios = Vec::new();
            let mut worst = Vec::new();
            for (reference, pad) in &exposed {
                let vias_in = ctx
                    .board
                    .vias
                    .iter()
                    .filter(|v| pad.net.is_some() && v.net == pad.net.unwrap())
                    .filter(|v| via_in_pad(pad, v))
                    .count();
                let expected = (pad.size.0 * pad.size.1 / 2.0).ceil().max(1.0);
                let ratio = (vias_in as f64 / expected).min(1.0);
                ratios.push(ratio);
                if ratio < 1.0 {
                    worst.push(WorstEntry {
                        label: (*reference).to_string(),
                        value: vias_in as f64,
                    });
                }
            }
            let mean = ratios.iter().sum::<f64>() / ratios.len() as f64;
            metrics.push(
                MetricResult::new(
                    "thermal_via_fill",
                    mean,
                    "ratio",
                    norm::ratio_clamp(mean),
                    2.0,
                )
                .with_worst(worst, false),
            );
        }

        // heat_spreading_layers: thermal vias should land on a plane layer.
        {
            let planes = ctx
                .net_classes
                .map(|classes| plane_layers(ctx.board, Some(classes)))
                .unwrap_or_default();
            if ctx.board.copper_layers.len() <= 2 {
                metrics.push(MetricResult::not_applicable(
                    "heat_spreading_layers",
                    1.0,
                    "two-layer board",
                ));
            } else if planes.is_empty() {
                metrics.push(MetricResult::not_applicable(
                    "heat_spreading_layers",
                    1.0,
                    "no reference planes to spread into",
                ));
            } else {
                let mut total = 0usize;
                let mut spreading = 0usize;
                for (_, pad) in &exposed {
                    for via in ctx
                        .board
                        .vias
                        .iter()
                        .filter(|v| pad.net.is_some() && v.net == pad.net.unwrap())
                        .filter(|v| via_in_pad(pad, v))
                    {
                        total += 1;
                        let spans_plane = planes.iter().any(|plane| {
                            crate::net_graph::via_spans_layer(via, plane, &ctx.board.copper_layers)
                        });
                        if spans_plane {
                            spreading += 1;
                        }
                    }
                }
                if total == 0 {
                    metrics.push(
                        MetricResult::new("heat_spreading_layers", 0.0, "ratio", 0.0, 1.0)
                            .with_note("no thermal vias under exposed pads"),
                    );
                } else {
                    let ratio = spreading as f64 / total as f64;
                    metrics.push(MetricResult::new(
                        "heat_spreading_layers",
                        ratio,
                        "ratio",
                        norm::ratio_clamp(ratio),
                        1.0,
                    ));
                }
            }
        }

        CategoryResult::new("thermal", "Thermal", weight, metrics)
    }
}
