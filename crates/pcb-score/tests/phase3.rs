//! Integration tests for EMI, power-integrity, ESD and thermal metrics with
//! declared roles and currents.

use std::collections::HashMap;

use pcb_sch::{AttributeValue, Instance, InstanceRef, ModuleRef, Net, Schematic};
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

fn component(refdes: &str, type_attr: &str) -> (InstanceRef, Instance) {
    let module = ModuleRef::new("test.zen", refdes);
    let mut instance = Instance::component(module.clone());
    instance.set_reference_designator(refdes);
    instance.add_attribute(
        "type".to_string(),
        AttributeValue::String(type_attr.to_string()),
    );
    (InstanceRef::new(module, vec![refdes.to_string()]), instance)
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

/// Connector J1 at the left edge, TVS D1 near it (or far), IC U1 to the
/// right, all sharing net USB_DP; ground net with a via near the TVS.
fn esd_board(tvs_x: f64) -> String {
    format!(
        r#"(kicad_pcb
  (layers (0 "F.Cu" signal) (2 "B.Cu" signal))
  (net 0 "")
  (net 1 "USB_DP")
  (net 2 "GNDX")
  (footprint "lib:J" (layer "F.Cu") (at 1 10)
    (property "Reference" "J1" (at 0 0) (layer "F.SilkS"))
    (pad "1" smd rect (at 0 0) (size 0.6 0.6) (layers "F.Cu") (net 1 "USB_DP"))
    (pad "2" smd rect (at 0 2) (size 0.6 0.6) (layers "F.Cu") (net 2 "GNDX")))
  (footprint "lib:TVS" (layer "F.Cu") (at {tvs_x} 10)
    (property "Reference" "D1" (at 0 0) (layer "F.SilkS"))
    (pad "1" smd rect (at 0 0) (size 0.5 0.5) (layers "F.Cu") (net 1 "USB_DP"))
    (pad "2" smd rect (at 0 1) (size 0.5 0.5) (layers "F.Cu") (net 2 "GNDX")))
  (footprint "lib:IC" (layer "F.Cu") (at 30 10)
    (property "Reference" "U1" (at 0 0) (layer "F.SilkS"))
    (pad "1" smd rect (at 0 0) (size 0.5 0.5) (layers "F.Cu") (net 1 "USB_DP")))
  (via (at {tvs_x} 11) (size 0.6) (drill 0.3) (layers "F.Cu" "B.Cu") (net 2))
  (segment (start 1 10) (end 30 10) (width 0.2) (layer "F.Cu") (net 1))
  (gr_rect (start 0 0) (end 40 20) (layer "Edge.Cuts"))
)"#
    )
}

fn esd_netlist() -> Schematic {
    let mut sch = Schematic::new();
    sch.add_net(net("Net", 1, "USB_DP", &[]));
    sch.add_net(net("Ground", 2, "GNDX", &[]));
    for (reference, instance) in [
        component("J1", "connector"),
        component("D1", "tvs"),
        component("U1", "other"),
    ] {
        sch.add_instance(reference, instance);
    }
    sch
}

#[test]
fn esd_metrics_reward_tvs_near_connector() {
    let near = score(&esd_board(3.0), &esd_netlist());
    let far = score(&esd_board(35.0), &esd_netlist());

    let near_prox = metric(&near, "esd", "tvs_proximity");
    let far_prox = metric(&far, "esd", "tvs_proximity");
    assert!(near_prox.applicable && far_prox.applicable);
    assert!(near_prox.raw.unwrap() < far_prox.raw.unwrap());
    assert!(near_prox.normalized.unwrap() > far_prox.normalized.unwrap());

    // Topology: near TVS sits between connector and IC; far TVS is beyond it.
    let near_topo = metric(&near, "esd", "protection_topology");
    let far_topo = metric(&far, "esd", "protection_topology");
    assert_eq!(near_topo.raw.unwrap(), 1.0);
    assert_eq!(far_topo.raw.unwrap(), 0.0);

    // Return path: ground via sits 1 mm from the TVS ground pad.
    let ret = metric(&near, "esd", "esd_return_path");
    assert_eq!(ret.raw.unwrap(), 1.0);
}

#[test]
fn esd_na_without_declared_tvs() {
    let mut sch = Schematic::new();
    sch.add_net(net("Net", 1, "USB_DP", &[]));
    sch.add_net(net("Ground", 2, "GNDX", &[]));
    // No `type` attributes at all: roles unknown, metrics N/A.
    let report = score(&esd_board(3.0), &sch);
    let prox = metric(&report, "esd", "tvs_proximity");
    assert!(!prox.applicable);
}

/// A power net with declared current: wide vs narrow trunk.
fn power_board(width: f64) -> String {
    format!(
        r#"(kicad_pcb
  (layers (0 "F.Cu" signal) (2 "B.Cu" signal))
  (net 0 "")
  (net 1 "V5")
  (net 2 "GNDX")
  (footprint "lib:A" (layer "F.Cu") (at 0 0)
    (pad "1" smd rect (at 0 0) (size 1 1) (layers "F.Cu") (net 1 "V5")))
  (footprint "lib:B" (layer "F.Cu") (at 20 0)
    (pad "1" smd rect (at 0 0) (size 1 1) (layers "F.Cu") (net 1 "V5")))
  (segment (start 0 0) (end 20 0) (width {width}) (layer "F.Cu") (net 1))
)"#
    )
}

fn power_netlist(amps: &str) -> Schematic {
    let mut sch = Schematic::new();
    sch.add_net(net(
        "Power",
        1,
        "V5",
        &[
            (
                "current_sink_total",
                AttributeValue::String(amps.to_string()),
            ),
            (
                "current_source_total",
                AttributeValue::String("3A".to_string()),
            ),
        ],
    ));
    sch.add_net(net("Ground", 2, "GNDX", &[]));
    sch
}

#[test]
fn trace_current_capacity_flags_narrow_power_trace() {
    // 2A through a 0.2mm trace on 35um copper is far under IPC-2152.
    let narrow = score(&power_board(0.2), &power_netlist("2A"));
    let wide = score(&power_board(3.0), &power_netlist("2A"));

    let narrow_cap = metric(&narrow, "power_integrity", "trace_current_capacity");
    let wide_cap = metric(&wide, "power_integrity", "trace_current_capacity");
    assert!(narrow_cap.applicable && wide_cap.applicable);
    assert!(narrow_cap.raw.unwrap() < 1.0, "narrow trace under-sized");
    assert!(wide_cap.raw.unwrap() > narrow_cap.raw.unwrap());
    assert!(wide_cap.normalized.unwrap() > narrow_cap.normalized.unwrap());

    // Budget margin: 3A source vs 2A sink = 1.5x.
    let margin = metric(&narrow, "power_integrity", "current_budget_margin");
    assert!((margin.raw.unwrap() - 1.5).abs() < 1e-6);
}

#[test]
fn power_metrics_na_without_current_declarations() {
    let mut sch = Schematic::new();
    sch.add_net(net("Power", 1, "V5", &[]));
    sch.add_net(net("Ground", 2, "GNDX", &[]));
    let report = score(&power_board(0.2), &sch);
    let cap = metric(&report, "power_integrity", "trace_current_capacity");
    assert!(!cap.applicable);
}

/// EMI: high-speed track along the board edge vs centered, with a ground
/// plane underneath.
fn emi_board(y: f64) -> String {
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
  (net 1 "CLK1")
  (net 2 "GNDX")
  (footprint "lib:A" (layer "F.Cu") (at 5 {y})
    (pad "1" smd rect (at 0 0) (size 0.4 0.4) (layers "F.Cu") (net 1 "CLK1")))
  (footprint "lib:B" (layer "F.Cu") (at 25 {y})
    (pad "1" smd rect (at 0 0) (size 0.4 0.4) (layers "F.Cu") (net 1 "CLK1")))
  (segment (start 5 {y}) (end 25 {y}) (width 0.2) (layer "F.Cu") (net 1))
  (zone (net 2) (net_name "GNDX") (layer "In1.Cu")
    (filled_polygon (layer "In1.Cu") (pts (xy 0 0) (xy 30 0) (xy 30 20) (xy 0 20))))
  (via (at 5 {y}) (size 0.6) (drill 0.3) (layers "F.Cu" "B.Cu") (net 2))
  (via (at 25 {y}) (size 0.6) (drill 0.3) (layers "F.Cu" "B.Cu") (net 2))
  (gr_rect (start 0 0) (end 30 20) (layer "Edge.Cuts"))
)"#
    )
}

fn emi_netlist() -> Schematic {
    let mut sch = Schematic::new();
    sch.add_net(net(
        "Net",
        1,
        "CLK1",
        &[("signal", AttributeValue::String("clock".to_string()))],
    ));
    sch.add_net(net("Ground", 2, "GNDX", &[]));
    sch
}

#[test]
fn emi_edge_clearance_prefers_centered_routing() {
    let centered = score(&emi_board(10.0), &emi_netlist());
    let edge = score(&emi_board(0.3), &emi_netlist());

    let centered_clearance = metric(&centered, "emi", "edge_clearance");
    let edge_clearance = metric(&edge, "emi", "edge_clearance");
    assert!(centered_clearance.normalized.unwrap() > edge_clearance.normalized.unwrap());

    // Loop area: plane at 0.2mm below over 20mm run => ~4 mm^2.
    let loop_area = metric(&centered, "emi", "loop_area_proxy");
    assert!(loop_area.applicable);
    assert!((loop_area.raw.unwrap() - 4.0).abs() < 0.5);

    // Ground stitching vias are close to the track.
    let stitching = metric(&centered, "emi", "stitching_via_density");
    assert!(stitching.applicable);
    assert!(stitching.raw.unwrap() < 11.0);
}

#[test]
fn deterministic_full_report() {
    let a = serde_json::to_string(&score(&emi_board(10.0), &emi_netlist())).unwrap();
    let b = serde_json::to_string(&score(&emi_board(10.0), &emi_netlist())).unwrap();
    assert_eq!(a, b);
}

/// Length-matched pair: two nets in group "lane0", one deliberately longer.
fn matched_board(extra: f64) -> String {
    let end = 10.0 + extra;
    format!(
        r#"(kicad_pcb
  (layers (0 "F.Cu" signal) (2 "B.Cu" signal))
  (net 0 "")
  (net 1 "D0")
  (net 2 "D1")
  (footprint "lib:A" (layer "F.Cu") (at 0 0)
    (pad "1" smd rect (at 0 0) (size 0.3 0.3) (layers "F.Cu") (net 1 "D0"))
    (pad "2" smd rect (at 0 2) (size 0.3 0.3) (layers "F.Cu") (net 2 "D1")))
  (footprint "lib:B" (layer "F.Cu") (at 10 0)
    (pad "1" smd rect (at 0 0) (size 0.3 0.3) (layers "F.Cu") (net 1 "D0"))
    (pad "2" smd rect (at {end} 2) (size 0.3 0.3) (layers "F.Cu") (net 2 "D1")))
  (segment (start 0 0) (end 10 0) (width 0.2) (layer "F.Cu") (net 1))
  (segment (start 0 2) (end {end} 2) (width 0.2) (layer "F.Cu") (net 2))
)"#
    )
}

fn matched_netlist() -> Schematic {
    let group = ("matched_group", AttributeValue::String("lane0".to_string()));
    let mut sch = Schematic::new();
    sch.add_net(net("Net", 1, "D0", &[group.clone()]));
    sch.add_net(net("Net", 2, "D1", &[group]));
    sch
}

#[test]
fn length_matching_groups_measures_group_skew() {
    let matched = score(&matched_board(0.0), &matched_netlist());
    let skewed = score(&matched_board(3.0), &matched_netlist());

    let m = metric(&matched, "signal_integrity", "length_matching_groups");
    let s = metric(&skewed, "signal_integrity", "length_matching_groups");
    assert!(m.applicable && s.applicable);
    assert!(m.raw.unwrap() < 0.01);
    assert!((s.raw.unwrap() - 3.0).abs() < 0.01);
    assert!(m.normalized.unwrap() > s.normalized.unwrap());
    assert_eq!(s.worst[0].label, "lane0");

    // Without declarations the metric stays out of the score.
    let mut undeclared = Schematic::new();
    undeclared.add_net(net("Net", 1, "D0", &[]));
    undeclared.add_net(net("Net", 2, "D1", &[]));
    let report = score(&matched_board(3.0), &undeclared);
    assert!(!metric(&report, "signal_integrity", "length_matching_groups").applicable);
}

/// T-topology: source U1 feeds a heavy sink U2 over a wide trunk and a light
/// sink U3 over a thin branch. Per-branch flow must accept the thin branch
/// (it only carries 0.2A); the old net-total model would reject it.
fn tee_board() -> &'static str {
    r#"(kicad_pcb
  (layers (0 "F.Cu" signal) (2 "B.Cu" signal))
  (net 0 "")
  (net 1 "V5")
  (net 2 "GNDX")
  (footprint "lib:SRC" (layer "F.Cu") (at 0 0)
    (property "Reference" "U1" (at 0 0) (layer "F.SilkS"))
    (pad "1" smd rect (at 0 0) (size 1 1) (layers "F.Cu") (net 1 "V5")))
  (footprint "lib:BIG" (layer "F.Cu") (at 20 0)
    (property "Reference" "U2" (at 0 0) (layer "F.SilkS"))
    (pad "1" smd rect (at 0 0) (size 1 1) (layers "F.Cu") (net 1 "V5")))
  (footprint "lib:SMALL" (layer "F.Cu") (at 0 10)
    (property "Reference" "U3" (at 0 0) (layer "F.SilkS"))
    (pad "1" smd rect (at 0 0) (size 1 1) (layers "F.Cu") (net 1 "V5")))
  (segment (start 0 0) (end 20 0) (width 2.0) (layer "F.Cu") (net 1))
  (segment (start 0 0) (end 0 10) (width 0.25) (layer "F.Cu") (net 1))
)"#
}

fn tee_netlist() -> Schematic {
    use serde_json::json;
    let module = ModuleRef::new("test.zen", "root");
    let mut sch = Schematic::new();

    let mut ports = Vec::new();
    for (path, refdes) in [
        (vec!["src", "U1"], "U1"),
        (vec!["big", "U2"], "U2"),
        (vec!["small", "U3"], "U3"),
    ] {
        let path: Vec<String> = path.into_iter().map(str::to_string).collect();
        let component_ref = InstanceRef::new(module.clone(), path.clone());
        let mut instance = Instance::component(module.clone());
        instance.set_reference_designator(refdes);
        sch.add_instance(component_ref.clone(), instance);
        ports.push(component_ref.append("1".to_string()));
    }

    let current_ports = json!([
        {"port": "big.VIN", "role": "sink", "amps": 1.8},
        {"port": "small.VIN", "role": "sink", "amps": 0.2},
        {"port": "src.VOUT", "role": "source", "amps": 2.0},
    ]);
    let mut v5 = net(
        "Power",
        1,
        "V5",
        &[
            (
                "current_sink_total",
                AttributeValue::String("2A".to_string()),
            ),
            (
                "current_source_total",
                AttributeValue::String("2A".to_string()),
            ),
            ("current_ports", AttributeValue::Json(current_ports)),
        ],
    );
    v5.ports = ports;
    sch.add_net(v5);
    sch.add_net(net("Ground", 2, "GNDX", &[]));
    sch
}

#[test]
fn per_branch_flow_accepts_thin_light_branch() {
    let report = score(tee_board(), &tee_netlist());
    let cap = metric(&report, "power_integrity", "trace_current_capacity");
    assert!(cap.applicable);
    assert!(
        cap.note.as_deref().unwrap_or("").contains("per-branch"),
        "flow model used, got note {:?}",
        cap.note
    );
    // 0.25mm carries only 0.2A (needs ~0.1mm) and the 2mm trunk carries
    // 1.8-2A (needs ~1.6mm): both fine, unlike net-total-vs-narrowest.
    assert!(cap.raw.unwrap() >= 1.0, "worst ratio {:?}", cap.raw);
}

/// Static-inference `component:<refdes>` port entries drive the flow solve.
#[test]
fn flow_maps_static_component_ports() {
    use serde_json::json;
    let board_src = r#"(kicad_pcb
  (layers (0 "F.Cu" signal) (2 "B.Cu" signal))
  (net 0 "")
  (net 1 "VCC")
  (net 2 "GNDX")
  (footprint "lib:SRC" (layer "F.Cu") (at 0 0)
    (property "Reference" "U1" (at 0 0) (layer "F.SilkS"))
    (pad "1" smd rect (at 0 0) (size 1 1) (layers "F.Cu") (net 1 "VCC")))
  (footprint "lib:R" (layer "F.Cu") (at 15 0)
    (property "Reference" "R9" (at 0 0) (layer "F.SilkS"))
    (pad "1" smd rect (at 0 0) (size 0.5 0.5) (layers "F.Cu") (net 1 "VCC")))
  (segment (start 0 0) (end 15 0) (width 1.0) (layer "F.Cu") (net 1))
)"#;

    let module = ModuleRef::new("test.zen", "root");
    let mut sch = Schematic::new();
    let src_ref = InstanceRef::new(module.clone(), vec!["src".into(), "U1".into()]);
    let mut src = Instance::component(module.clone());
    src.set_reference_designator("U1");
    sch.add_instance(src_ref.clone(), src);

    let current_ports = json!([
        {"port": "component:R9", "role": "sink", "amps": 0.5},
        {"port": "src.VOUT", "role": "source", "amps": 0.5},
    ]);
    let mut vcc = net(
        "Power",
        1,
        "VCC",
        &[
            (
                "current_sink_static",
                AttributeValue::String("0.5A".to_string()),
            ),
            (
                "current_source_total",
                AttributeValue::String("0.5A".to_string()),
            ),
            ("current_ports", AttributeValue::Json(current_ports)),
        ],
    );
    vcc.ports = vec![src_ref.append("1".to_string())];
    sch.add_net(vcc);
    sch.add_net(net("Ground", 2, "GNDX", &[]));

    let report = score(board_src, &sch);
    let cap = metric(&report, "power_integrity", "trace_current_capacity");
    assert!(cap.applicable);
    assert!(
        cap.note.as_deref().unwrap_or("").contains("per-branch"),
        "static component port mapped into the flow solve, note: {:?}",
        cap.note
    );
}
