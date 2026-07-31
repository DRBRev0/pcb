//! Integration tests for signal-integrity and crosstalk metrics using a
//! synthetic netlist (declared classifications) and hand-built boards with
//! analytically known geometry.

use std::collections::HashMap;

use pcb_sch::{AttributeValue, Net, Schematic};
use pcb_score::{BoardModel, ScoreInputs, Weights, score_board};

fn net(kind: &str, id: u64, name: &str, props: &[(&str, AttributeValue)]) -> Net {
    let mut properties = HashMap::new();
    for (key, value) in props {
        properties.insert((*key).to_string(), value.clone());
    }
    Net {
        kind: kind.to_string(),
        id,
        name: name.to_string(),
        ports: Vec::new(),
        properties,
    }
}

fn schematic(nets: Vec<Net>) -> Schematic {
    let mut sch = Schematic::new();
    for n in nets {
        sch.add_net(n);
    }
    sch
}

fn score(board_src: &str, netlist: &Schematic) -> pcb_score::ScoreReport {
    let board = BoardModel::parse(board_src).unwrap();
    score_board(&ScoreInputs {
        board: &board,
        board_source: board_src,
        board_path: "test.kicad_pcb",
        drc: None,
        netlist: Some(netlist),
        weights: Weights::default(),
    })
    .unwrap()
}

fn metric<'a>(
    report: &'a pcb_score::ScoreReport,
    category: &str,
    id: &str,
) -> &'a pcb_score::model::MetricResult {
    report
        .categories
        .iter()
        .find(|c| c.id == category)
        .unwrap_or_else(|| panic!("category {category} missing"))
        .metrics
        .iter()
        .find(|m| m.id == id)
        .unwrap_or_else(|| panic!("metric {id} missing"))
}

/// Four-layer board: two parallel aggressor/victim tracks, 10 mm run.
/// Separation is edge-to-edge center distance 0.4 mm with 0.2 mm widths:
/// under the 3W rule (3 * 0.2 = 0.6 center spacing).
fn coupled_board(sep_mm: f64) -> String {
    format!(
        r#"(kicad_pcb
  (layers (0 "F.Cu" signal) (1 "In1.Cu" signal) (2 "In2.Cu" signal) (3 "B.Cu" signal))
  (net 0 "")
  (net 1 "CLK_OUT")
  (net 2 "VSENSE")
  (footprint "lib:A" (layer "F.Cu") (at 0 0)
    (pad "1" smd rect (at 0 0) (size 0.4 0.4) (layers "F.Cu") (net 1 "CLK_OUT"))
    (pad "2" smd rect (at 0 {sep_mm}) (size 0.4 0.4) (layers "F.Cu") (net 2 "VSENSE")))
  (footprint "lib:B" (layer "F.Cu") (at 10 0)
    (pad "1" smd rect (at 0 0) (size 0.4 0.4) (layers "F.Cu") (net 1 "CLK_OUT"))
    (pad "2" smd rect (at 0 {sep_mm}) (size 0.4 0.4) (layers "F.Cu") (net 2 "VSENSE")))
  (segment (start 0 0) (end 10 0) (width 0.2) (layer "F.Cu") (net 1))
  (segment (start 0 {sep_mm}) (end 10 {sep_mm}) (width 0.2) (layer "F.Cu") (net 2))
)"#
    )
}

fn classified_nets() -> Schematic {
    schematic(vec![
        net(
            "Net",
            1,
            "CLK_OUT",
            &[("signal", AttributeValue::String("clock".to_string()))],
        ),
        net(
            "Net",
            2,
            "VSENSE",
            &[("signal", AttributeValue::String("analog".to_string()))],
        ),
    ])
}

#[test]
fn crosstalk_close_pair_scores_worse_than_spaced_pair() {
    let close = score(&coupled_board(0.4), &classified_nets());
    let spaced = score(&coupled_board(2.5), &classified_nets());

    let close_coupling = metric(&close, "crosstalk", "parallel_coupling");
    let spaced_coupling = metric(&spaced, "crosstalk", "parallel_coupling");
    assert!(close_coupling.applicable && spaced_coupling.applicable);
    // 10mm at 0.4mm: exposure 62.5; at 2.0mm: outside the 4W capture window.
    assert!(close_coupling.raw.unwrap() > 60.0);
    assert!(spaced_coupling.raw.unwrap() < 1.0);
    assert!(close_coupling.normalized.unwrap() < spaced_coupling.normalized.unwrap());

    // 3W compliance: 0.4mm spacing < 0.6mm fails; 2.0mm passes trivially.
    let close_3w = metric(&close, "crosstalk", "three_w_compliance");
    assert!(close_3w.raw.unwrap() < 0.01);
    let spaced_3w = metric(&spaced, "crosstalk", "three_w_compliance");
    assert!(spaced_3w.raw.unwrap() > 0.99);

    // Sensitive isolation flags the analog net.
    let isolation = metric(&close, "crosstalk", "sensitive_net_isolation");
    assert!(isolation.applicable);
    assert!(isolation.raw.unwrap() < 1.0);
    assert_eq!(isolation.worst[0].label, "VSENSE");
}

#[test]
fn crosstalk_na_without_declarations() {
    let undeclared = schematic(vec![
        net("Net", 1, "CLK_OUT", &[]),
        net("Net", 2, "VSENSE", &[]),
    ]);
    let report = score(&coupled_board(0.4), &undeclared);
    let coupling = metric(&report, "crosstalk", "parallel_coupling");
    assert!(!coupling.applicable);
    // Purely geometric 3W stays applicable.
    let three_w = metric(&report, "crosstalk", "three_w_compliance");
    assert!(three_w.applicable);
}

/// Board with a stackup and a ground plane on In1.Cu; one impedance-target
/// microstrip on F.Cu. Geometry chosen so that Z(w=0.25, h=0.2, er=4.2)
/// lands near 50 ohms.
fn impedance_board(width: f64) -> String {
    format!(
        r#"(kicad_pcb
  (layers (0 "F.Cu" signal) (1 "In1.Cu" signal) (2 "In2.Cu" signal) (3 "B.Cu" signal))
  (setup
    (stackup
      (layer "F.Cu" (type "copper") (thickness 0.035))
      (layer "dielectric 1" (type "prepreg") (thickness 0.2) (epsilon_r 4.2))
      (layer "In1.Cu" (type "copper") (thickness 0.035))
      (layer "dielectric 2" (type "core") (thickness 1.0) (epsilon_r 4.2))
      (layer "In2.Cu" (type "copper") (thickness 0.035))
      (layer "dielectric 3" (type "prepreg") (thickness 0.2) (epsilon_r 4.2))
      (layer "B.Cu" (type "copper") (thickness 0.035))))
  (net 0 "")
  (net 1 "USB_DM")
  (net 2 "GNDNET")
  (footprint "lib:A" (layer "F.Cu") (at 0 0)
    (pad "1" smd rect (at 0 0) (size 0.4 0.4) (layers "F.Cu") (net 1 "USB_DM")))
  (footprint "lib:B" (layer "F.Cu") (at 10 0)
    (pad "1" smd rect (at 0 0) (size 0.4 0.4) (layers "F.Cu") (net 1 "USB_DM")))
  (segment (start 0 0) (end 10 0) (width {width}) (layer "F.Cu") (net 1))
  (zone (net 2) (net_name "GNDNET") (layer "In1.Cu")
    (filled_polygon (layer "In1.Cu") (pts (xy -5 -5) (xy 15 -5) (xy 15 5) (xy -5 5))))
)"#
    )
}

fn impedance_nets() -> Schematic {
    schematic(vec![
        net(
            "Net",
            1,
            "USB_DM",
            &[("impedance", AttributeValue::String("50Ohm".to_string()))],
        ),
        net("Ground", 2, "GNDNET", &[]),
    ])
}

#[test]
fn impedance_compliance_prefers_correct_width() {
    // Near-target width vs. a much too wide (low impedance) trace.
    let good = score(&impedance_board(0.35), &impedance_nets());
    let bad = score(&impedance_board(2.0), &impedance_nets());

    let good_metric = metric(&good, "signal_integrity", "impedance_compliance");
    let bad_metric = metric(&bad, "signal_integrity", "impedance_compliance");
    assert!(good_metric.applicable && bad_metric.applicable);
    assert!(good_metric.raw.unwrap() < bad_metric.raw.unwrap());
    assert!(good_metric.normalized.unwrap() > bad_metric.normalized.unwrap());

    // The plane under the whole run gives full reference continuity.
    let continuity = metric(&good, "signal_integrity", "reference_plane_continuity");
    assert!(continuity.applicable);
    assert!(continuity.raw.unwrap() > 0.99);
}

#[test]
fn impedance_na_without_stackup() {
    // Same board minus the stackup block.
    let source = impedance_board(0.35);
    let no_stackup: String = source
        .lines()
        .filter(|line| {
            !line.contains("(layer \"dielectric")
                && !line.contains("(stackup")
                && !line.contains("(type \"copper\"")
                && !line.contains("(setup")
        })
        .collect::<Vec<_>>()
        .join("\n");
    let report = score(&no_stackup, &impedance_nets());
    let metric = metric(&report, "signal_integrity", "impedance_compliance");
    assert!(!metric.applicable);
}

/// Differential pair with a deliberate 1 mm skew on the N side.
fn diffpair_board(extra_n: f64) -> String {
    let n_end = 10.0 + extra_n;
    format!(
        r#"(kicad_pcb
  (layers (0 "F.Cu" signal) (2 "B.Cu" signal))
  (net 0 "")
  (net 1 "PAIR_P")
  (net 2 "PAIR_N")
  (footprint "lib:A" (layer "F.Cu") (at 0 0)
    (pad "1" smd rect (at 0 0) (size 0.3 0.3) (layers "F.Cu") (net 1 "PAIR_P"))
    (pad "2" smd rect (at 0 0.3) (size 0.3 0.3) (layers "F.Cu") (net 2 "PAIR_N")))
  (footprint "lib:B" (layer "F.Cu") (at 10 0)
    (pad "1" smd rect (at 0 0) (size 0.3 0.3) (layers "F.Cu") (net 1 "PAIR_P"))
    (pad "2" smd rect (at {n_end} 0.3) (size 0.3 0.3) (layers "F.Cu") (net 2 "PAIR_N")))
  (segment (start 0 0) (end 10 0) (width 0.2) (layer "F.Cu") (net 1))
  (segment (start 0 0.3) (end {n_end} 0.3) (width 0.2) (layer "F.Cu") (net 2))
)"#
    )
}

fn diffpair_nets() -> Schematic {
    schematic(vec![
        net(
            "Net",
            1,
            "PAIR_P",
            &[
                (
                    "differential_impedance",
                    AttributeValue::String("90Ohm".to_string()),
                ),
                ("diff_pair_peer", AttributeValue::Number(2.0)),
                ("diff_pair_role", AttributeValue::String("p".to_string())),
            ],
        ),
        net(
            "Net",
            2,
            "PAIR_N",
            &[
                (
                    "differential_impedance",
                    AttributeValue::String("90Ohm".to_string()),
                ),
                ("diff_pair_peer", AttributeValue::Number(1.0)),
                ("diff_pair_role", AttributeValue::String("n".to_string())),
            ],
        ),
    ])
}

#[test]
fn diffpair_skew_is_measured() {
    let matched = score(&diffpair_board(0.0), &diffpair_nets());
    let skewed = score(&diffpair_board(1.0), &diffpair_nets());

    let matched_skew = metric(&matched, "signal_integrity", "diffpair_skew");
    let skewed_skew = metric(&skewed, "signal_integrity", "diffpair_skew");
    assert!(matched_skew.raw.unwrap() < 0.01);
    assert!((skewed_skew.raw.unwrap() - 1.0).abs() < 0.01);
    assert!(matched_skew.normalized.unwrap() > skewed_skew.normalized.unwrap());
    assert_eq!(skewed_skew.worst[0].label, "PAIR_P/PAIR_N");
}
