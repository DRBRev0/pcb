//! Routing quality scoring for PCB layouts.
//!
//! Evaluates a routed `.kicad_pcb` against hard gates (full connectivity,
//! zero DRC errors) and a weighted catalog of quality metrics, producing a
//! deterministic [`model::ScoreReport`] usable as an autorouting fitness
//! function.

pub mod board;
pub mod classify;
pub mod impedance;
pub mod metrics;
pub mod model;
pub mod net_graph;
pub mod norm;
pub mod roles;
pub mod spatial;
pub mod stackup;

use std::collections::BTreeMap;

use anyhow::Result;
use sha2::Digest;

pub use board::BoardModel;
pub use metrics::{ScoreContext, Weights};
pub use model::ScoreReport;
pub use pcb_kicad::drc::DrcReport;

pub struct ScoreInputs<'a> {
    pub board: &'a BoardModel,
    /// Raw `.kicad_pcb` contents, for the content hash in the report.
    pub board_source: &'a str,
    /// Displayed path of the board file.
    pub board_path: &'a str,
    pub drc: Option<&'a DrcReport>,
    pub netlist: Option<&'a pcb_sch::Schematic>,
    pub weights: Weights,
}

/// Score a parsed board. Deterministic: identical inputs yield an identical
/// report.
pub fn score_board(inputs: &ScoreInputs) -> Result<ScoreReport> {
    let board = inputs.board;
    let net_stats = net_graph::compute_net_stats(board);
    let net_classes = inputs.netlist.map(classify::classify_nets);
    let component_roles = inputs.netlist.map(roles::component_roles);

    let ctx = ScoreContext {
        board,
        net_stats: &net_stats,
        drc: inputs.drc,
        netlist: inputs.netlist,
        net_classes: net_classes.as_ref(),
        roles: component_roles.as_ref(),
        weights: &inputs.weights,
    };

    let categories: Vec<model::CategoryResult> = metrics::all_passes()
        .iter()
        .map(|pass| pass.run(&ctx))
        .collect();

    // Composite quality over applicable categories, weight-renormalized.
    let mut weight_sum = 0.0;
    let mut acc = 0.0;
    for category in &categories {
        if let Some(score) = category.score {
            weight_sum += category.weight;
            acc += category.weight * score;
        }
    }
    let quality = if weight_sum > 0.0 {
        100.0 * acc / weight_sum
    } else {
        0.0
    };

    let gates = compute_gates(&net_stats, inputs.drc);
    let connectivity_ratio = gates.connectivity.ratio;
    let drc_error_count = gates.drc_errors.count as f64;

    // Continuous optimizer objective: strictly improves as nets connect,
    // errors disappear and quality rises.
    let fitness = 100.0
        * (0.55 * connectivity_ratio
            + 0.20 * (-drc_error_count / 5.0).exp()
            + 0.25 * quality / 100.0);

    let score = if gates.passed { quality } else { 0.0 };

    Ok(ScoreReport {
        schema_version: model::SCHEMA_VERSION,
        generator: model::Generator {
            tool: "pcb-score".to_string(),
            version: env!("CARGO_PKG_VERSION").to_string(),
        },
        board: model::BoardSummary {
            path: inputs.board_path.to_string(),
            sha256: hex_sha256(inputs.board_source),
            copper_layers: board.copper_layers.len(),
            nets: board.used_net_ids().len(),
            components: board.footprints.len(),
        },
        inputs: model::InputsSummary {
            netlist_available: inputs.netlist.is_some(),
            drc_ran: inputs.drc.is_some(),
        },
        gates,
        score: model::round4(score),
        fitness: model::round4(fitness),
        quality: model::round4(quality),
        categories,
    })
}

fn compute_gates(
    net_stats: &BTreeMap<i64, net_graph::NetStats>,
    drc: Option<&DrcReport>,
) -> model::Gates {
    let routable: Vec<&net_graph::NetStats> =
        net_stats.values().filter(|s| s.pad_count >= 2).collect();
    let total_nets = routable.len();
    let connected_nets = routable.iter().filter(|s| s.connected).count();
    let ratio = if total_nets == 0 {
        1.0
    } else {
        connected_nets as f64 / total_nets as f64
    };

    let drc_unconnected_items = drc.map(|report| {
        report
            .unconnected_items
            .iter()
            .filter(|v| !v.excluded)
            .count()
    });
    let connectivity_passed =
        connected_nets == total_nets && drc_unconnected_items.unwrap_or(0) == 0;

    let mut error_count = 0usize;
    let mut by_kind: BTreeMap<String, usize> = BTreeMap::new();
    if let Some(report) = drc {
        for violation in &report.violations {
            if violation.severity == "error" && !violation.excluded {
                error_count += 1;
                *by_kind.entry(violation.violation_type.clone()).or_default() += 1;
            }
        }
    }
    let drc_passed = error_count == 0;

    model::Gates {
        passed: connectivity_passed && drc_passed,
        connectivity: model::ConnectivityGate {
            passed: connectivity_passed,
            connected_nets,
            total_nets,
            ratio: model::round4(ratio),
            drc_unconnected_items,
        },
        drc_errors: model::DrcGate {
            passed: drc_passed,
            count: error_count,
            by_kind,
        },
    }
}

fn hex_sha256(content: &str) -> String {
    let mut hasher = sha2::Sha256::new();
    hasher.update(content.as_bytes());
    let digest = hasher.finalize();
    digest.iter().map(|b| format!("{b:02x}")).collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    const TWO_NET_BOARD: &str = r#"(kicad_pcb
  (layers (0 "F.Cu" signal) (2 "B.Cu" signal))
  (net 0 "")
  (net 1 "A")
  (net 2 "B")
  (footprint "lib:R1" (layer "F.Cu") (at 0 0)
    (pad "1" smd rect (at 0 0) (size 1 1) (layers "F.Cu") (net 1 "A"))
    (pad "2" smd rect (at 2 0) (size 1 1) (layers "F.Cu") (net 2 "B")))
  (footprint "lib:R2" (layer "F.Cu") (at 10 0)
    (pad "1" smd rect (at 0 0) (size 1 1) (layers "F.Cu") (net 1 "A"))
    (pad "2" smd rect (at 2 0) (size 1 1) (layers "F.Cu") (net 2 "B")))
  (segment (start 0 0) (end 10 0) (width 0.25) (layer "F.Cu") (net 1))
)"#;

    fn score(source: &str) -> ScoreReport {
        let board = BoardModel::parse(source).unwrap();
        score_board(&ScoreInputs {
            board: &board,
            board_source: source,
            board_path: "test.kicad_pcb",
            drc: None,
            netlist: None,
            weights: Weights::default(),
        })
        .unwrap()
    }

    #[test]
    fn gate_blocks_score_until_fully_routed() {
        let partial = score(TWO_NET_BOARD);
        assert!(!partial.gates.passed);
        assert_eq!(partial.score, 0.0);
        assert!(partial.fitness > 0.0);
        assert_eq!(partial.gates.connectivity.connected_nets, 1);
        assert_eq!(partial.gates.connectivity.total_nets, 2);

        let full_source = TWO_NET_BOARD.replace(
            r#"(segment (start 0 0) (end 10 0) (width 0.25) (layer "F.Cu") (net 1))"#,
            r#"(segment (start 0 0) (end 10 0) (width 0.25) (layer "F.Cu") (net 1))
  (segment (start 2 0) (end 12 0) (width 0.25) (layer "F.Cu") (net 2))"#,
        );
        let full = score(&full_source);
        assert!(full.gates.passed);
        assert!(full.score > 0.0);
        assert!(
            full.fitness > partial.fitness,
            "fitness must strictly improve"
        );
    }

    #[test]
    fn deterministic_output() {
        let a = serde_json::to_string(&score(TWO_NET_BOARD)).unwrap();
        let b = serde_json::to_string(&score(TWO_NET_BOARD)).unwrap();
        assert_eq!(a, b);
    }
}
