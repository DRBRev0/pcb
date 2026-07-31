//! Static (DC worst-case) current inference over declared passives.
//!
//! Typed two-pin passives link nets with a known DC element model:
//! - resistors contribute `1/R` (multi-element parts bridging two nets count
//!   one element per pin pair);
//! - inductors and ferrite beads are near-shorts;
//! - capacitors and TVS diodes are open (their static current is known to be
//!   zero);
//! - diodes/rectifiers/LEDs conduct only anode->cathode above their forward
//!   voltage, and Zeners additionally conduct cathode->anode above their
//!   breakdown voltage. Orientation comes from the component's SPICE net
//!   order (`nets=[A, K]`), so it is generic for any part with a SpiceModel.
//!
//! Combined with declared net voltages (`Power(voltage=...)`, `Ground` = 0V)
//! and io()-declared currents, this solves simple source/impedance
//! structures — a divider or a Zener clamp needs no hand-written
//! `sink_current` — and warns when a subnetwork has no voltage reference to
//! infer from. Nonlinear elements are handled by piecewise-linear state
//! iteration (off / forward / breakdown) to a fixpoint.
//!
//! Results land as net properties:
//! - `current_sink_static` / `current_source_static`: amps the passive
//!   network draws from / feeds into the net ("0A" marks a known-zero net);
//! - `current_static_uninferable`: set when the net belongs to a subnetwork
//!   that cannot be solved from declared data;
//! - `current_ports` gains `{"port": "component:<refdes>", ...}` entries so
//!   layout-level flow analysis can inject at the passive's pads.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use pcb_sch::{AttributeValue, InstanceKind, InstanceRef, Schematic};
use serde_json::{Map as JsonMap, Number as JsonNumber, Value as JsonValue};

/// Below this magnitude a computed current is considered zero (1 nA).
const CURRENT_EPS: f64 = 1e-9;
/// DC resistance modelling an inductor / ferrite bead (1 mOhm).
const SHORT_OHMS: f64 = 1e-3;
/// On-state series resistance of a conducting diode (ohms).
const DIODE_ON_OHMS: f64 = 1.0;
/// Default forward voltages when the component does not declare one.
const DIODE_VF: f64 = 0.7;
const LED_VF: f64 = 2.0;
/// Piecewise-linear state iteration cap.
const MAX_STATE_ITERATIONS: usize = 32;

#[derive(Debug, Clone, Copy, PartialEq)]
enum DcModel {
    /// Conductance in siemens.
    Conductive(f64),
    /// Anode->cathode conduction above `vf`; optional cathode->anode
    /// breakdown above `vz` (Zener).
    Diode { vf: f64, vz: Option<f64> },
    /// No DC current (capacitors, TVS in normal operation).
    Open,
}

#[derive(Debug, Clone, Copy, PartialEq)]
enum EdgeKind {
    Linear,
    Diode { vf: f64, vz: Option<f64> },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DiodeState {
    Off,
    Forward,
    Breakdown,
}

struct DcEdge {
    refdes: String,
    /// For diodes, `net_a` is the anode and `net_b` the cathode.
    net_a: String,
    net_b: String,
    conductance: f64,
    kind: EdgeKind,
}

/// One linearized stamp: `i = g * (V_from - V_to - emf)` flowing from->to.
struct Stamp {
    from: usize,
    to: usize,
    g: f64,
    emf: f64,
}

fn attr_nominal(value: &AttributeValue) -> Option<f64> {
    use rust_decimal::prelude::ToPrimitive;
    value.physical().and_then(|p| p.nominal.to_f64())
}

fn instance_volts(instance: &pcb_sch::Instance, key: &str) -> Option<f64> {
    instance.attributes.get(key).and_then(attr_nominal)
}

fn dc_model(instance: &pcb_sch::Instance) -> Option<DcModel> {
    let type_attr = instance.attributes.get("type").and_then(|v| v.string())?;
    match type_attr {
        "resistor" => {
            let ohms = instance
                .attributes
                .get("resistance")
                .and_then(attr_nominal)?;
            (ohms > 0.0).then(|| DcModel::Conductive(1.0 / ohms))
        }
        "inductor" | "ferrite_bead" => Some(DcModel::Conductive(1.0 / SHORT_OHMS)),
        "capacitor" | "tvs" => Some(DcModel::Open),
        "diode" | "rectifier" => Some(DcModel::Diode {
            vf: instance_volts(instance, "forward_voltage").unwrap_or(DIODE_VF),
            vz: None,
        }),
        "led" => Some(DcModel::Diode {
            vf: instance_volts(instance, "forward_voltage").unwrap_or(LED_VF),
            vz: None,
        }),
        "zener" => Some(DcModel::Diode {
            vf: instance_volts(instance, "forward_voltage").unwrap_or(DIODE_VF),
            vz: Some(instance_volts(instance, "zener_voltage")?),
        }),
        _ => None,
    }
}

/// Anode/cathode net names from the component's SPICE net order
/// (`SpiceModel(nets=[A, K])`).
fn spice_net_order(instance: &pcb_sch::Instance) -> Option<Vec<String>> {
    match instance.attributes.get(crate::attrs::MODEL_NETS)? {
        AttributeValue::Array(nets) => Some(
            nets.iter()
                .filter_map(|v| v.string().map(str::to_string))
                .collect(),
        ),
        _ => None,
    }
}

/// Fixed potential of a net, if declared: `Ground` nets are 0V, any net with
/// a parsable `voltage` property uses its nominal.
fn fixed_voltage(net: &pcb_sch::Net) -> Option<f64> {
    if net.kind == "Ground" {
        return Some(
            net.properties
                .get("voltage")
                .and_then(attr_nominal)
                .unwrap_or(0.0),
        );
    }
    net.properties.get("voltage").and_then(attr_nominal)
}

fn declared_amps(net: &pcb_sch::Net, key: &str) -> f64 {
    net.properties
        .get(key)
        .and_then(attr_nominal)
        .unwrap_or(0.0)
}

fn format_amps(amps: f64) -> String {
    // Stable, unit-suffixed decimal (avoid float noise at the nA level).
    format!("{}A", (amps * 1e9).round() / 1e9)
}

/// Current through `edge` given node voltages (NaN = floating) and state.
fn edge_current(edge: &DcEdge, state: DiodeState, va: f64, vb: f64) -> f64 {
    if va.is_nan() || vb.is_nan() {
        return 0.0;
    }
    match edge.kind {
        EdgeKind::Linear => (va - vb) * edge.conductance,
        EdgeKind::Diode { vf, vz } => match state {
            DiodeState::Off => 0.0,
            DiodeState::Forward => ((va - vb - vf) / DIODE_ON_OHMS).max(0.0),
            DiodeState::Breakdown => {
                let vz = vz.unwrap_or(f64::INFINITY);
                -((vb - va - vz) / DIODE_ON_OHMS).max(0.0)
            }
        },
    }
}

/// Solve one connected subnetwork with Dirichlet (fixed-voltage) nodes and
/// piecewise-linear diode states. Returns node voltages (NaN for nodes left
/// floating by off diodes) and the final per-edge states, or `None` when the
/// subnetwork cannot be solved (no reference, singular, or no fixpoint).
fn solve_component(
    nets: &[String],
    fixed: &HashMap<&str, f64>,
    sink_injections: &HashMap<&str, f64>,
    edges: &[&DcEdge],
) -> Option<(HashMap<String, f64>, Vec<DiodeState>)> {
    let unknown: Vec<&str> = nets
        .iter()
        .map(String::as_str)
        .filter(|name| !fixed.contains_key(name))
        .collect();
    if unknown.len() == nets.len() {
        return None; // no voltage reference anywhere in this subnetwork
    }
    let unknown_index: HashMap<&str, usize> = unknown
        .iter()
        .enumerate()
        .map(|(i, name)| (*name, i))
        .collect();
    let n = unknown.len();

    let node_voltage = |name: &str, solution: &[f64]| -> f64 {
        fixed.get(name).copied().unwrap_or_else(|| {
            unknown_index
                .get(name)
                .map(|&i| solution[i])
                .unwrap_or(f64::NAN)
        })
    };

    let mut states: Vec<DiodeState> = vec![DiodeState::Off; edges.len()];
    let mut solution: Vec<f64> = vec![f64::NAN; n];

    for _ in 0..MAX_STATE_ITERATIONS {
        // Linearized stamps for the current states.
        let mut stamps: Vec<Stamp> = Vec::new();
        // Node indexing: unknowns 0..n, fixed nodes virtual index n + k.
        let fixed_list: Vec<(&str, f64)> = nets
            .iter()
            .filter_map(|name| fixed.get(name.as_str()).map(|v| (name.as_str(), *v)))
            .collect();
        let fixed_index: HashMap<&str, usize> = fixed_list
            .iter()
            .enumerate()
            .map(|(k, (name, _))| (*name, n + k))
            .collect();
        let index_of = |name: &str| -> Option<usize> {
            unknown_index
                .get(name)
                .copied()
                .or_else(|| fixed_index.get(name).copied())
        };
        let voltage_of_fixed = |idx: usize| fixed_list[idx - n].1;

        for (edge, state) in edges.iter().zip(&states) {
            let (Some(a), Some(b)) = (index_of(&edge.net_a), index_of(&edge.net_b)) else {
                continue;
            };
            match (edge.kind, state) {
                (EdgeKind::Linear, _) => stamps.push(Stamp {
                    from: a,
                    to: b,
                    g: edge.conductance,
                    emf: 0.0,
                }),
                (EdgeKind::Diode { .. }, DiodeState::Off) => {}
                (EdgeKind::Diode { vf, .. }, DiodeState::Forward) => stamps.push(Stamp {
                    from: a,
                    to: b,
                    g: 1.0 / DIODE_ON_OHMS,
                    emf: vf,
                }),
                (EdgeKind::Diode { vz, .. }, DiodeState::Breakdown) => stamps.push(Stamp {
                    from: b,
                    to: a,
                    g: 1.0 / DIODE_ON_OHMS,
                    emf: vz.unwrap_or(0.0),
                }),
            }
        }

        // Unknown nodes with no stamp in the current state are floating
        // (attached only through off diodes): exclude them from the system.
        let mut attached = vec![false; n];
        for stamp in &stamps {
            if stamp.from < n {
                attached[stamp.from] = true;
            }
            if stamp.to < n {
                attached[stamp.to] = true;
            }
        }
        let solved_nodes: Vec<usize> = (0..n).filter(|&i| attached[i]).collect();
        let dense_index: HashMap<usize, usize> = solved_nodes
            .iter()
            .enumerate()
            .map(|(dense, &node)| (node, dense))
            .collect();
        let dim = solved_nodes.len();

        let mut matrix = vec![vec![0.0f64; dim]; dim];
        let mut rhs: Vec<f64> = solved_nodes
            .iter()
            .map(|&node| -sink_injections.get(unknown[node]).copied().unwrap_or(0.0))
            .collect();
        for stamp in &stamps {
            // i = g (V_from - V_to - emf), leaving `from`, entering `to`.
            let from_dense = (stamp.from < n).then(|| dense_index[&stamp.from]);
            let to_dense = (stamp.to < n).then(|| dense_index[&stamp.to]);
            match (from_dense, to_dense) {
                (Some(f), Some(t)) => {
                    matrix[f][f] += stamp.g;
                    matrix[t][t] += stamp.g;
                    matrix[f][t] -= stamp.g;
                    matrix[t][f] -= stamp.g;
                    rhs[f] += stamp.g * stamp.emf;
                    rhs[t] -= stamp.g * stamp.emf;
                }
                (Some(f), None) => {
                    matrix[f][f] += stamp.g;
                    rhs[f] += stamp.g * (voltage_of_fixed(stamp.to) + stamp.emf);
                }
                (None, Some(t)) => {
                    matrix[t][t] += stamp.g;
                    rhs[t] += stamp.g * (voltage_of_fixed(stamp.from) - stamp.emf);
                }
                (None, None) => {}
            }
        }

        let dense_solution = gauss_solve(matrix, rhs)?;
        solution = vec![f64::NAN; n];
        for (&node, value) in solved_nodes.iter().zip(&dense_solution) {
            solution[node] = *value;
        }

        // Re-evaluate diode states from the solved voltages.
        let mut next_states = states.clone();
        for (idx, edge) in edges.iter().enumerate() {
            let EdgeKind::Diode { vf, vz } = edge.kind else {
                continue;
            };
            let va = node_voltage(&edge.net_a, &solution);
            let vb = node_voltage(&edge.net_b, &solution);
            next_states[idx] = if va - vb > vf + 1e-9 {
                DiodeState::Forward
            } else if vz.map(|vz| vb - va > vz + 1e-9).unwrap_or(false) {
                DiodeState::Breakdown
            } else {
                DiodeState::Off
            };
        }
        if next_states == states {
            let voltages: HashMap<String, f64> = nets
                .iter()
                .map(|name| (name.clone(), node_voltage(name, &solution)))
                .collect();
            return Some((voltages, states));
        }
        states = next_states;
    }
    None // state oscillation: no fixpoint found
}

/// Dense Gaussian elimination with partial pivoting.
fn gauss_solve(mut matrix: Vec<Vec<f64>>, rhs: Vec<f64>) -> Option<Vec<f64>> {
    let n = matrix.len();
    for (row, b) in matrix.iter_mut().zip(&rhs) {
        row.push(*b);
    }
    for col in 0..n {
        let pivot = (col..n).max_by(|&x, &y| {
            matrix[x][col]
                .abs()
                .partial_cmp(&matrix[y][col].abs())
                .unwrap_or(std::cmp::Ordering::Equal)
        })?;
        if matrix[pivot][col].abs() < 1e-15 {
            return None;
        }
        matrix.swap(col, pivot);
        let (pivot_rows, rest) = matrix.split_at_mut(col + 1);
        let pivot_row = &pivot_rows[col];
        for row in rest.iter_mut() {
            let factor = row[col] / pivot_row[col];
            if factor == 0.0 {
                continue;
            }
            for (value, pivot_value) in row[col..].iter_mut().zip(&pivot_row[col..]) {
                *value -= factor * pivot_value;
            }
        }
    }
    let mut solution = vec![0.0f64; n];
    for row in (0..n).rev() {
        let mut sum = matrix[row][n];
        for (k, v) in solution.iter().enumerate().take(n).skip(row + 1) {
            sum -= matrix[row][k] * v;
        }
        solution[row] = sum / matrix[row][row];
    }
    Some(solution)
}

/// Run the DC inference and annotate `schematic` nets in place.
pub fn annotate_static_currents(schematic: &mut Schematic) {
    // Component -> attached nets, with the number of pins on each net.
    let mut component_nets: HashMap<InstanceRef, BTreeMap<String, usize>> = HashMap::new();
    for net in schematic.nets.values() {
        for port_ref in &net.ports {
            if port_ref.instance_path.len() < 2 {
                continue;
            }
            let component_ref = InstanceRef::new(
                port_ref.module.clone(),
                port_ref.instance_path[..port_ref.instance_path.len() - 1].to_vec(),
            );
            *component_nets
                .entry(component_ref)
                .or_default()
                .entry(net.name.clone())
                .or_default() += 1;
        }
    }

    // Two-pin passives with a DC model.
    let mut edges: Vec<DcEdge> = Vec::new();
    // Nets whose non-conductive attachments are all known-open (capacitors,
    // TVS in normal operation).
    let mut open_nets: BTreeSet<String> = BTreeSet::new();
    // Nets attached to anything we cannot model (IC pins, untyped parts).
    let mut opaque_nets: BTreeSet<String> = BTreeSet::new();

    // Stable iteration order for deterministic edge lists.
    let mut component_list: Vec<(&InstanceRef, &BTreeMap<String, usize>)> =
        component_nets.iter().collect();
    component_list.sort_by_key(|(component_ref, _)| component_ref.instance_path.join("."));
    for (component_ref, nets) in component_list {
        let Some(instance) = schematic.instances.get(component_ref) else {
            continue;
        };
        if instance.kind != InstanceKind::Component {
            continue;
        }
        let refdes = instance
            .reference_designator
            .clone()
            .unwrap_or_else(|| component_ref.instance_path.join("."));
        match dc_model(instance) {
            Some(DcModel::Conductive(conductance)) if nets.len() == 2 => {
                let mut it = nets.iter();
                let (net_a, pins_a) = it.next().unwrap();
                let (net_b, pins_b) = it.next().unwrap();
                // A multi-element part bridging the same two nets (e.g. a
                // resistor array wired in parallel) contributes one element
                // per pin pair.
                let elements = (*pins_a.min(pins_b)).max(1) as f64;
                edges.push(DcEdge {
                    refdes,
                    net_a: net_a.clone(),
                    net_b: net_b.clone(),
                    conductance: conductance * elements,
                    kind: EdgeKind::Linear,
                });
            }
            Some(DcModel::Diode { vf, vz }) if nets.len() == 2 => {
                // Orientation from the SPICE net order (nets=[A, K]).
                match spice_net_order(instance) {
                    Some(order)
                        if order.len() == 2
                            && nets.contains_key(&order[0])
                            && nets.contains_key(&order[1]) =>
                    {
                        edges.push(DcEdge {
                            refdes,
                            net_a: order[0].clone(),
                            net_b: order[1].clone(),
                            conductance: 1.0 / DIODE_ON_OHMS,
                            kind: EdgeKind::Diode { vf, vz },
                        });
                    }
                    // Unknown orientation: cannot model the one-way element.
                    _ => opaque_nets.extend(nets.keys().cloned()),
                }
            }
            Some(DcModel::Open) => open_nets.extend(nets.keys().cloned()),
            // Conductive parts touching 3+ nets (resistor networks as a
            // single component) have unknown internal pin pairing: opaque.
            Some(DcModel::Conductive(_) | DcModel::Diode { .. }) if nets.len() > 2 => {
                opaque_nets.extend(nets.keys().cloned())
            }
            // A passive shorting its own pins carries no inter-net current.
            Some(DcModel::Conductive(_) | DcModel::Diode { .. }) => {}
            None => opaque_nets.extend(nets.keys().cloned()),
        }
    }

    if edges.is_empty() && open_nets.is_empty() {
        return;
    }

    // Union-find over element edges to isolate connected subnetworks.
    let mut graph_nets: BTreeSet<&str> = BTreeSet::new();
    for edge in &edges {
        graph_nets.insert(edge.net_a.as_str());
        graph_nets.insert(edge.net_b.as_str());
    }
    let net_list: Vec<&str> = graph_nets.iter().copied().collect();
    let net_pos: HashMap<&str, usize> = net_list
        .iter()
        .enumerate()
        .map(|(i, name)| (*name, i))
        .collect();
    let mut parent: Vec<usize> = (0..net_list.len()).collect();
    fn find(parent: &mut Vec<usize>, i: usize) -> usize {
        if parent[i] != i {
            let root = find(parent, parent[i]);
            parent[i] = root;
        }
        parent[i]
    }
    for edge in &edges {
        let a = find(&mut parent, net_pos[edge.net_a.as_str()]);
        let b = find(&mut parent, net_pos[edge.net_b.as_str()]);
        parent[a] = b;
    }
    let mut groups: BTreeMap<usize, Vec<String>> = BTreeMap::new();
    for (i, name) in net_list.iter().enumerate() {
        groups
            .entry(find(&mut parent, i))
            .or_default()
            .push((*name).to_string());
    }

    let fixed: HashMap<&str, f64> = schematic
        .nets
        .values()
        .filter_map(|net| fixed_voltage(net).map(|v| (net.name.as_str(), v)))
        .collect();
    let sink_injections: HashMap<&str, f64> = schematic
        .nets
        .values()
        .map(|net| (net.name.as_str(), declared_amps(net, "current_sink_total")))
        .collect();
    // Unknown-voltage nets that source current are active rails: their
    // voltage is set by a supply, not by the passive network, so any
    // subnetwork containing one cannot be solved from declared data.
    let active_unfixed: BTreeSet<&str> = schematic
        .nets
        .values()
        .filter(|net| {
            !fixed.contains_key(net.name.as_str())
                && declared_amps(net, "current_source_total") > 0.0
        })
        .map(|net| net.name.as_str())
        .collect();

    // Solve every subnetwork; accumulate per-net static currents and
    // per-edge port entries.
    let mut sink_static: BTreeMap<String, f64> = BTreeMap::new();
    let mut source_static: BTreeMap<String, f64> = BTreeMap::new();
    let mut port_entries: BTreeMap<String, Vec<(String, bool, f64)>> = BTreeMap::new();
    let mut uninferable: BTreeSet<String> = BTreeSet::new();

    for nets in groups.values() {
        let group_edges: Vec<&DcEdge> = edges
            .iter()
            .filter(|e| nets.contains(&e.net_a) || nets.contains(&e.net_b))
            .collect();
        let has_active_unfixed = nets.iter().any(|net| active_unfixed.contains(net.as_str()));
        let solved = if has_active_unfixed {
            None
        } else {
            solve_component(nets, &fixed, &sink_injections, &group_edges)
        };
        match solved {
            Some((voltages, states)) => {
                for (edge, state) in group_edges.iter().zip(&states) {
                    let (va, vb) = (voltages[&edge.net_a], voltages[&edge.net_b]);
                    let current = edge_current(edge, *state, va, vb);
                    if current.abs() < CURRENT_EPS {
                        continue;
                    }
                    // Current flows a -> b when positive: it leaves net_a
                    // (sink attachment there) and enters net_b (source).
                    let (from, to, amps) = if current > 0.0 {
                        (&edge.net_a, &edge.net_b, current)
                    } else {
                        (&edge.net_b, &edge.net_a, -current)
                    };
                    *sink_static.entry(from.clone()).or_default() += amps;
                    *source_static.entry(to.clone()).or_default() += amps;
                    port_entries.entry(from.clone()).or_default().push((
                        edge.refdes.clone(),
                        true,
                        amps,
                    ));
                    port_entries.entry(to.clone()).or_default().push((
                        edge.refdes.clone(),
                        false,
                        amps,
                    ));
                }
                // Solved nets with no measurable current are known-zero.
                for net in nets {
                    sink_static.entry(net.clone()).or_default();
                    source_static.entry(net.clone()).or_default();
                }
            }
            None => uninferable.extend(nets.iter().cloned()),
        }
    }

    // Open-only nets: every attachment is a known passive with zero DC
    // current, so the static current is known to be zero.
    for net_name in &open_nets {
        if !opaque_nets.contains(net_name)
            && !graph_nets.contains(net_name.as_str())
            && !uninferable.contains(net_name)
        {
            sink_static.entry(net_name.clone()).or_default();
            source_static.entry(net_name.clone()).or_default();
        }
    }

    // Write results back onto the nets.
    for net in schematic.nets.values_mut() {
        if uninferable.contains(&net.name) {
            net.properties.insert(
                "current_static_uninferable".to_string(),
                AttributeValue::Boolean(true),
            );
            continue;
        }
        let (Some(sink), Some(source)) = (sink_static.get(&net.name), source_static.get(&net.name))
        else {
            continue;
        };
        net.properties.insert(
            "current_sink_static".to_string(),
            AttributeValue::String(format_amps(*sink)),
        );
        net.properties.insert(
            "current_source_static".to_string(),
            AttributeValue::String(format_amps(*source)),
        );

        if let Some(entries) = port_entries.get(&net.name) {
            let mut ports_json = match net.properties.get("current_ports") {
                Some(AttributeValue::Json(JsonValue::Array(existing))) => existing.clone(),
                _ => Vec::new(),
            };
            for (refdes, is_sink, amps) in entries {
                let mut map = JsonMap::new();
                map.insert(
                    "port".to_string(),
                    JsonValue::String(format!("component:{refdes}")),
                );
                map.insert(
                    "role".to_string(),
                    JsonValue::String(if *is_sink { "sink" } else { "source" }.to_string()),
                );
                map.insert(
                    "amps".to_string(),
                    JsonNumber::from_f64((amps * 1e9).round() / 1e9)
                        .map(JsonValue::Number)
                        .unwrap_or(JsonValue::Null),
                );
                ports_json.push(JsonValue::Object(map));
            }
            net.properties.insert(
                "current_ports".to_string(),
                AttributeValue::Json(JsonValue::Array(ports_json)),
            );
        }
    }
}
