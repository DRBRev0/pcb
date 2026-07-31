//! Crosstalk metrics: geometric coupling between declared aggressors and
//! victims, plus the purely geometric 3W-rule compliance.

use std::collections::BTreeMap;

use crate::classify::NetInfo;
use crate::model::{CategoryResult, MetricResult, WorstEntry};
use crate::norm;
use crate::spatial::{SegmentIndex, parallel_overlap};
use crate::stackup::StackupGeometry;

use super::{ScoreContext, ScorePass};

pub struct CrosstalkPass;

/// Coupling exposure threshold (mm / mm^2) above which a pair counts as a
/// hotspot; ~10 mm parallel run at 0.25 mm spacing.
const HOTSPOT_EXPOSURE: f64 = 160.0;

impl ScorePass for CrosstalkPass {
    fn id(&self) -> &'static str {
        "crosstalk"
    }

    fn run(&self, ctx: &ScoreContext) -> CategoryResult {
        let mut metrics = Vec::new();
        let weight = ctx.weights.crosstalk;
        let index = SegmentIndex::build(ctx.board);

        // three_w_compliance is purely geometric: applies to every
        // same-layer parallel adjacency regardless of classification.
        {
            let mut total_overlap = 0.0;
            let mut compliant_overlap = 0.0;
            for (i, a) in ctx.board.tracks.iter().enumerate() {
                let radius = 4.0 * a.width.max(0.2);
                for j in index.neighbours(i, &a.layer, radius) {
                    if j <= i {
                        continue;
                    }
                    let b = &ctx.board.tracks[j];
                    if b.net == a.net || b.layer != a.layer {
                        continue;
                    }
                    if let Some((overlap, sep)) = parallel_overlap(a, b) {
                        let w = a.width.max(b.width);
                        if sep > 4.0 * w {
                            continue;
                        }
                        total_overlap += overlap;
                        if sep >= 3.0 * w {
                            compliant_overlap += overlap;
                        }
                    }
                }
            }
            if total_overlap > 1e-9 {
                let ratio = compliant_overlap / total_overlap;
                metrics.push(MetricResult::new(
                    "three_w_compliance",
                    ratio,
                    "ratio",
                    norm::ratio_clamp(ratio),
                    3.0,
                ));
            } else {
                metrics.push(
                    MetricResult::new("three_w_compliance", 1.0, "ratio", 1.0, 3.0)
                        .with_note("no parallel adjacencies found"),
                );
            }
        }

        let Some(classes) = ctx.net_classes else {
            let note = "netlist unavailable: declarative net classification required";
            for id in [
                "parallel_coupling",
                "broadside_coupling",
                "sensitive_net_isolation",
                "crosstalk_hotspot_count",
            ] {
                metrics.push(MetricResult::not_applicable(id, 2.0, note));
            }
            return CategoryResult::new("crosstalk", "Crosstalk", weight, metrics);
        };

        // Classified aggressor/victim net ids.
        let class_of = |net: i64| -> Option<&NetInfo> { classes.get(ctx.board.net_name(net)) };
        let is_aggressor = |net: i64| {
            class_of(net)
                .and_then(|info| info.class)
                .map(|class| class.is_aggressor())
                .unwrap_or(false)
        };
        let is_victim = |net: i64| {
            class_of(net)
                .map(|info| {
                    info.class.map(|class| class.is_victim()).unwrap_or(false)
                        || info.impedance_ohms.is_some()
                        || info.differential_impedance_ohms.is_some()
                })
                .unwrap_or(false)
        };
        let classified_pairs_exist = ctx.board.nets.keys().any(|&id| is_aggressor(id))
            && ctx.board.nets.keys().any(|&id| is_victim(id));

        if !classified_pairs_exist {
            let note = "no aggressor/victim pairs declared (`signal` classes)";
            for id in [
                "parallel_coupling",
                "broadside_coupling",
                "sensitive_net_isolation",
                "crosstalk_hotspot_count",
            ] {
                metrics.push(MetricResult::not_applicable(id, 2.0, note));
            }
            return CategoryResult::new("crosstalk", "Crosstalk", weight, metrics);
        }

        // parallel_coupling: per-victim exposure sum(overlap / sep^2) from
        // same-layer aggressor segments; plus hotspot count.
        let mut victim_exposure: BTreeMap<String, f64> = BTreeMap::new();
        let mut hotspots = 0usize;
        let mut sensitive_min_ratio: BTreeMap<String, f64> = BTreeMap::new();
        for (i, a) in ctx.board.tracks.iter().enumerate() {
            if !is_aggressor(a.net) {
                continue;
            }
            let radius = 4.0 * a.width.max(0.5);
            for j in index.neighbours(i, &a.layer, radius) {
                let b = &ctx.board.tracks[j];
                if b.net == a.net || b.layer != a.layer || !is_victim(b.net) {
                    continue;
                }
                if let Some((overlap, sep)) = parallel_overlap(a, b) {
                    let w = a.width.max(b.width);
                    if sep > 4.0 * w.max(0.5) {
                        continue;
                    }
                    let sep = sep.max(0.05);
                    let exposure = overlap / (sep * sep);
                    let victim_name = ctx.board.net_name(b.net).to_string();
                    *victim_exposure.entry(victim_name.clone()).or_default() += exposure;
                    if exposure > HOTSPOT_EXPOSURE {
                        hotspots += 1;
                    }
                    // Track 3W margin for declared-sensitive victims.
                    if class_of(b.net)
                        .and_then(|info| info.class)
                        .map(|class| {
                            matches!(
                                class,
                                crate::classify::SignalClass::Analog
                                    | crate::classify::SignalClass::Rf
                            )
                        })
                        .unwrap_or(false)
                    {
                        let ratio = sep / (3.0 * w);
                        sensitive_min_ratio
                            .entry(victim_name)
                            .and_modify(|r| *r = r.min(ratio))
                            .or_insert(ratio);
                    }
                }
            }
        }

        let worst_exposure = victim_exposure.values().cloned().fold(0.0f64, f64::max);
        let worst: Vec<WorstEntry> = victim_exposure
            .iter()
            .map(|(name, exposure)| WorstEntry {
                label: name.clone(),
                value: *exposure,
            })
            .collect();
        metrics.push(
            MetricResult::new(
                "parallel_coupling",
                worst_exposure,
                "mm_per_mm2",
                norm::decay(worst_exposure, 100.0),
                4.0,
            )
            .with_worst(worst, true),
        );

        // broadside_coupling: parallel overlap on adjacent copper layers with
        // no reference plane between (stackup required).
        {
            let geometry = StackupGeometry::from_board(ctx.board);
            let planes = crate::stackup::plane_layers(ctx.board, Some(classes));
            match geometry {
                Some(geometry) if ctx.board.copper_layers.len() >= 2 => {
                    let mut exposure_total = 0.0;
                    let layer_pos: BTreeMap<&str, usize> = ctx
                        .board
                        .copper_layers
                        .iter()
                        .enumerate()
                        .map(|(k, name)| (name.as_str(), k))
                        .collect();
                    for (i, a) in ctx.board.tracks.iter().enumerate() {
                        if !is_aggressor(a.net) {
                            continue;
                        }
                        for (j, b) in ctx.board.tracks.iter().enumerate() {
                            if j <= i || b.net == a.net || !is_victim(b.net) {
                                continue;
                            }
                            let (Some(&pa), Some(&pb)) = (
                                layer_pos.get(a.layer.as_str()),
                                layer_pos.get(b.layer.as_str()),
                            ) else {
                                continue;
                            };
                            if pa.abs_diff(pb) != 1 {
                                continue; // only adjacent copper layers couple broadside
                            }
                            if planes.contains(&a.layer) || planes.contains(&b.layer) {
                                continue;
                            }
                            let Some(h) = geometry.dielectric_span(&a.layer, &b.layer) else {
                                continue;
                            };
                            if let Some((overlap, sep)) = parallel_overlap(a, b)
                                && sep <= 2.0 * a.width.max(b.width).max(0.5)
                            {
                                exposure_total += overlap / (h * h).max(1e-6);
                            }
                        }
                    }
                    metrics.push(MetricResult::new(
                        "broadside_coupling",
                        exposure_total,
                        "mm_per_mm2",
                        norm::decay(exposure_total, 200.0),
                        2.0,
                    ));
                }
                _ => metrics.push(MetricResult::not_applicable(
                    "broadside_coupling",
                    2.0,
                    "stackup data missing",
                )),
            }
        }

        // sensitive_net_isolation: worst 3W margin of analog/rf victims.
        if sensitive_min_ratio.is_empty() {
            let has_sensitive = ctx.board.nets.keys().any(|&id| {
                class_of(id)
                    .and_then(|info| info.class)
                    .map(|class| {
                        matches!(
                            class,
                            crate::classify::SignalClass::Analog | crate::classify::SignalClass::Rf
                        )
                    })
                    .unwrap_or(false)
            });
            if has_sensitive {
                metrics.push(
                    MetricResult::new("sensitive_net_isolation", 1.0, "ratio", 1.0, 2.0)
                        .with_note("sensitive nets have no aggressor adjacency"),
                );
            } else {
                metrics.push(MetricResult::not_applicable(
                    "sensitive_net_isolation",
                    2.0,
                    "no nets declared analog/rf",
                ));
            }
        } else {
            let worst_ratio = sensitive_min_ratio
                .values()
                .cloned()
                .fold(f64::INFINITY, f64::min);
            let worst: Vec<WorstEntry> = sensitive_min_ratio
                .iter()
                .map(|(name, ratio)| WorstEntry {
                    label: name.clone(),
                    value: *ratio,
                })
                .collect();
            metrics.push(
                MetricResult::new(
                    "sensitive_net_isolation",
                    worst_ratio,
                    "x3w",
                    norm::ratio_clamp(worst_ratio),
                    2.0,
                )
                .with_worst(worst, false),
            );
        }

        metrics.push(MetricResult::new(
            "crosstalk_hotspot_count",
            hotspots as f64,
            "count",
            norm::decay(hotspots as f64, 3.0),
            2.0,
        ));

        CategoryResult::new("crosstalk", "Crosstalk", weight, metrics)
    }
}
