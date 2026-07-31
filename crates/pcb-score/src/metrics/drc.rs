//! DRC-derived soft metrics (the hard gates live in the report driver).

use std::collections::BTreeMap;

use crate::model::{CategoryResult, MetricResult, WorstEntry};
use crate::norm;

use super::{ScoreContext, ScorePass};

pub struct DrcPass;

impl ScorePass for DrcPass {
    fn id(&self) -> &'static str {
        "drc"
    }

    fn run(&self, ctx: &ScoreContext) -> CategoryResult {
        let mut metrics = Vec::new();

        match ctx.drc {
            Some(report) => {
                let (_, warning_count) = report.violation_counts();
                let mut by_kind: BTreeMap<String, usize> = BTreeMap::new();
                for violation in &report.violations {
                    if violation.severity == "warning" && !violation.excluded {
                        *by_kind.entry(violation.violation_type.clone()).or_default() += 1;
                    }
                }
                let worst: Vec<WorstEntry> = by_kind
                    .iter()
                    .map(|(kind, count)| WorstEntry {
                        label: kind.clone(),
                        value: *count as f64,
                    })
                    .collect();
                metrics.push(
                    MetricResult::new(
                        "drc_warning_count",
                        warning_count as f64,
                        "count",
                        norm::decay(warning_count as f64, 10.0),
                        3.0,
                    )
                    .with_worst(worst, true),
                );

                let excluded = report
                    .violations
                    .iter()
                    .chain(&report.unconnected_items)
                    .filter(|v| v.excluded)
                    .count();
                metrics.push(MetricResult::new(
                    "drc_exclusion_count",
                    excluded as f64,
                    "count",
                    norm::decay(excluded as f64, 5.0),
                    1.0,
                ));

                let parity_issues = report
                    .schematic_parity
                    .iter()
                    .filter(|v| !v.excluded)
                    .count();
                metrics.push(MetricResult::new(
                    "schematic_parity",
                    parity_issues as f64,
                    "count",
                    if parity_issues == 0 { 1.0 } else { 0.0 },
                    2.0,
                ));
            }
            None => {
                for id in [
                    "drc_warning_count",
                    "drc_exclusion_count",
                    "schematic_parity",
                ] {
                    metrics.push(MetricResult::not_applicable(
                        id,
                        1.0,
                        "DRC was not run (--skip-drc or kicad-cli unavailable)",
                    ));
                }
            }
        }

        CategoryResult::new("drc", "DRC hygiene", ctx.weights.drc, metrics)
    }
}
