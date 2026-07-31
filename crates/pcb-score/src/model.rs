//! Report data model for routing quality scoring.
//!
//! The JSON serialization of [`ScoreReport`] is a stable contract
//! (`schema_version`) consumed by external tools; keep changes additive.

use std::collections::BTreeMap;

use serde::Serialize;

pub const SCHEMA_VERSION: u32 = 1;

/// Round to 4 decimal places for stable, comparable output.
pub fn round4(x: f64) -> f64 {
    (x * 10_000.0).round() / 10_000.0
}

#[derive(Debug, Clone, Serialize)]
pub struct ScoreReport {
    pub schema_version: u32,
    pub generator: Generator,
    pub board: BoardSummary,
    pub inputs: InputsSummary,
    pub gates: Gates,
    /// Headline quality score: 0 while any gate fails, otherwise `quality`.
    pub score: f64,
    /// Continuous optimizer objective; always computed, strictly improves as
    /// connectivity, DRC and quality improve.
    pub fitness: f64,
    /// Weighted composite of category scores over applicable metrics (0-100).
    pub quality: f64,
    pub categories: Vec<CategoryResult>,
}

#[derive(Debug, Clone, Serialize)]
pub struct Generator {
    pub tool: String,
    pub version: String,
}

#[derive(Debug, Clone, Serialize)]
pub struct BoardSummary {
    pub path: String,
    pub sha256: String,
    pub copper_layers: usize,
    pub nets: usize,
    pub components: usize,
}

#[derive(Debug, Clone, Serialize)]
pub struct InputsSummary {
    pub netlist_available: bool,
    pub drc_ran: bool,
}

#[derive(Debug, Clone, Serialize)]
pub struct Gates {
    pub passed: bool,
    pub connectivity: ConnectivityGate,
    pub drc_errors: DrcGate,
}

#[derive(Debug, Clone, Serialize)]
pub struct ConnectivityGate {
    pub passed: bool,
    /// Nets whose pads are all joined by copper.
    pub connected_nets: usize,
    /// Nets with at least two pads (the ones that need routing).
    pub total_nets: usize,
    pub ratio: f64,
    /// Unconnected items reported by KiCad DRC, when DRC ran.
    pub drc_unconnected_items: Option<usize>,
}

#[derive(Debug, Clone, Serialize)]
pub struct DrcGate {
    pub passed: bool,
    pub count: usize,
    pub by_kind: BTreeMap<String, usize>,
}

#[derive(Debug, Clone, Serialize)]
pub struct CategoryResult {
    pub id: String,
    pub label: String,
    pub weight: f64,
    /// Weighted mean of applicable metric scores in [0, 1]; `None` when no
    /// metric in the category is applicable.
    pub score: Option<f64>,
    pub metrics: Vec<MetricResult>,
}

#[derive(Debug, Clone, Serialize)]
pub struct MetricResult {
    pub id: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub raw: Option<f64>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub unit: Option<String>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub normalized: Option<f64>,
    pub weight: f64,
    pub applicable: bool,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub note: Option<String>,
    /// Worst offenders (top 5, sorted worst-first then by label) so
    /// regressions are traceable to specific nets/locations.
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub worst: Vec<WorstEntry>,
}

#[derive(Debug, Clone, Serialize)]
pub struct WorstEntry {
    pub label: String,
    pub value: f64,
}

impl MetricResult {
    pub fn new(id: &str, raw: f64, unit: &str, normalized: f64, weight: f64) -> Self {
        Self {
            id: id.to_string(),
            raw: Some(round4(raw)),
            unit: Some(unit.to_string()),
            normalized: Some(round4(normalized.clamp(0.0, 1.0))),
            weight,
            applicable: true,
            note: None,
            worst: Vec::new(),
        }
    }

    pub fn not_applicable(id: &str, weight: f64, note: &str) -> Self {
        Self {
            id: id.to_string(),
            raw: None,
            unit: None,
            normalized: None,
            weight,
            applicable: false,
            note: Some(note.to_string()),
            worst: Vec::new(),
        }
    }

    pub fn with_note(mut self, note: impl Into<String>) -> Self {
        self.note = Some(note.into());
        self
    }

    /// Keep the top 5 worst offenders, sorted worst-first then by label for
    /// deterministic output.
    pub fn with_worst(mut self, mut entries: Vec<WorstEntry>, higher_is_worse: bool) -> Self {
        entries.sort_by(|a, b| {
            let ord = a
                .value
                .partial_cmp(&b.value)
                .unwrap_or(std::cmp::Ordering::Equal);
            let ord = if higher_is_worse { ord.reverse() } else { ord };
            ord.then_with(|| a.label.cmp(&b.label))
        });
        entries.truncate(5);
        for entry in &mut entries {
            entry.value = round4(entry.value);
        }
        self.worst = entries;
        self
    }
}

impl CategoryResult {
    pub fn new(id: &str, label: &str, weight: f64, metrics: Vec<MetricResult>) -> Self {
        let mut weight_sum = 0.0;
        let mut acc = 0.0;
        for metric in metrics.iter().filter(|m| m.applicable) {
            if let Some(normalized) = metric.normalized {
                weight_sum += metric.weight;
                acc += metric.weight * normalized;
            }
        }
        let score = (weight_sum > 0.0).then(|| round4(acc / weight_sum));
        Self {
            id: id.to_string(),
            label: label.to_string(),
            weight,
            score,
            metrics,
        }
    }
}
