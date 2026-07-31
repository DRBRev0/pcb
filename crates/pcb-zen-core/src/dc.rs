//! Static (DC worst-case) current inference over declared passives.
//!
//! Typed two-pin passives link nets with a known DC impedance: resistors
//! contribute `1/R`, inductors and ferrite beads are near-shorts, and
//! capacitors are open (their `jCw` impedance is infinite at DC, so their
//! current is known to be zero). Combined with declared net voltages
//! (`Power(voltage=...)`, `Ground` = 0V) and io()-declared currents, this
//! lets the ERC compute currents through simple resistive structures — a
//! voltage divider needs no hand-written `sink_current` — and warn when a
//! resistive path has no voltage reference to infer from.
//!
//! Results land as net properties:
//! - `current_sink_static` / `current_source_static`: amps the resistive
//!   network draws from / feeds into the net ("0A" marks a known-zero net,
//!   e.g. capacitor-only attachments);
//! - `current_static_uninferable`: set when the net belongs to a resistive
//!   subnetwork with no voltage reference;
//! - `current_ports` gains `{"port": "component:<refdes>", ...}` entries so
//!   layout-level flow analysis can inject at the passive's pads.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use pcb_sch::{AttributeValue, InstanceKind, InstanceRef, Schematic};
use serde_json::{Map as JsonMap, Number as JsonNumber, Value as JsonValue};

/// Below this magnitude a computed current is considered zero (1 nA).
const CURRENT_EPS: f64 = 1e-9;
/// DC resistance modelling an inductor / ferrite bead (1 mOhm).
const SHORT_OHMS: f64 = 1e-3;

#[derive(Debug, Clone, Copy, PartialEq)]
enum DcModel {
    /// Conductance in siemens.
    Conductive(f64),
    /// No DC current (capacitors).
    Open,
}

struct DcEdge {
    refdes: String,
    net_a: String,
    net_b: String,
    conductance: f64,
}

fn attr_nominal(value: &AttributeValue) -> Option<f64> {
    use rust_decimal::prelude::ToPrimitive;
    value.physical().and_then(|p| p.nominal.to_f64())
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
        "capacitor" => Some(DcModel::Open),
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

/// Solve one connected resistive component with Dirichlet (fixed-voltage)
/// nodes. Returns node voltages, or `None` if no node is fixed.
fn solve_component(
    nets: &[String],
    fixed: &HashMap<&str, f64>,
    sink_injections: &HashMap<&str, f64>,
    edges: &[&DcEdge],
) -> Option<HashMap<String, f64>> {
    let index: HashMap<&str, usize> = nets
        .iter()
        .enumerate()
        .map(|(i, name)| (name.as_str(), i))
        .collect();
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
    let mut voltages: HashMap<String, f64> = fixed
        .iter()
        .filter(|(name, _)| index.contains_key(*name))
        .map(|(name, v)| ((*name).to_string(), *v))
        .collect();
    if n == 0 {
        return Some(voltages);
    }

    // Nodal equations for unknown nodes: sum_j g_ij (V_i - V_j) = -sink_i.
    // Declared sinks are worst-case actual draws and inject at their node;
    // declared sources are capacities, never flows (nets that source current
    // without a declared voltage exclude their subnetwork before this).
    let mut matrix = vec![vec![0.0f64; n]; n];
    let mut rhs: Vec<f64> = unknown
        .iter()
        .map(|name| -sink_injections.get(name).copied().unwrap_or(0.0))
        .collect();
    for edge in edges {
        let (a, b, g) = (edge.net_a.as_str(), edge.net_b.as_str(), edge.conductance);
        match (unknown_index.get(a), unknown_index.get(b)) {
            (Some(&ia), Some(&ib)) => {
                matrix[ia][ia] += g;
                matrix[ib][ib] += g;
                matrix[ia][ib] -= g;
                matrix[ib][ia] -= g;
            }
            (Some(&ia), None) => {
                matrix[ia][ia] += g;
                rhs[ia] += g * fixed[b];
            }
            (None, Some(&ib)) => {
                matrix[ib][ib] += g;
                rhs[ib] += g * fixed[a];
            }
            (None, None) => {}
        }
    }

    // Gaussian elimination with partial pivoting.
    let mut aug: Vec<Vec<f64>> = matrix
        .into_iter()
        .zip(&rhs)
        .map(|(mut row, b)| {
            row.push(*b);
            row
        })
        .collect();
    for col in 0..n {
        let pivot = (col..n).max_by(|&x, &y| {
            aug[x][col]
                .abs()
                .partial_cmp(&aug[y][col].abs())
                .unwrap_or(std::cmp::Ordering::Equal)
        })?;
        if aug[pivot][col].abs() < 1e-15 {
            return None;
        }
        aug.swap(col, pivot);
        let (pivot_rows, rest) = aug.split_at_mut(col + 1);
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
        let mut sum = aug[row][n];
        for (k, v) in solution.iter().enumerate().take(n).skip(row + 1) {
            sum -= aug[row][k] * v;
        }
        solution[row] = sum / aug[row][row];
    }
    for (name, v) in unknown.iter().zip(solution) {
        voltages.insert((*name).to_string(), v);
    }
    Some(voltages)
}

/// Run the DC inference and annotate `schematic` nets in place.
pub fn annotate_static_currents(schematic: &mut Schematic) {
    // Component -> distinct attached nets.
    let mut component_nets: HashMap<InstanceRef, BTreeSet<String>> = HashMap::new();
    for net in schematic.nets.values() {
        for port_ref in &net.ports {
            if port_ref.instance_path.len() < 2 {
                continue;
            }
            let component_ref = InstanceRef::new(
                port_ref.module.clone(),
                port_ref.instance_path[..port_ref.instance_path.len() - 1].to_vec(),
            );
            component_nets
                .entry(component_ref)
                .or_default()
                .insert(net.name.clone());
        }
    }

    // Two-pin passives with a DC model.
    let mut edges: Vec<DcEdge> = Vec::new();
    // Nets whose non-conductive attachments are all capacitors.
    let mut capacitor_nets: BTreeSet<String> = BTreeSet::new();
    // Nets attached to anything we cannot model (IC pins, untyped parts).
    let mut opaque_nets: BTreeSet<String> = BTreeSet::new();

    // Stable iteration order for deterministic edge lists.
    let mut component_list: Vec<(&InstanceRef, &BTreeSet<String>)> =
        component_nets.iter().collect();
    component_list.sort_by_key(|(component_ref, _)| component_ref.instance_path.join("."));
    for (component_ref, nets) in component_list {
        let Some(instance) = schematic.instances.get(component_ref) else {
            continue;
        };
        if instance.kind != InstanceKind::Component {
            continue;
        }
        let model = dc_model(instance);
        match model {
            Some(DcModel::Conductive(conductance)) if nets.len() == 2 => {
                let mut it = nets.iter();
                let net_a = it.next().unwrap().clone();
                let net_b = it.next().unwrap().clone();
                edges.push(DcEdge {
                    refdes: instance
                        .reference_designator
                        .clone()
                        .unwrap_or_else(|| component_ref.instance_path.join(".")),
                    net_a,
                    net_b,
                    conductance,
                });
            }
            Some(DcModel::Open) => capacitor_nets.extend(nets.iter().cloned()),
            // A passive shorting its own pins carries no inter-net current.
            Some(DcModel::Conductive(_)) => {}
            None => opaque_nets.extend(nets.iter().cloned()),
        }
    }

    if edges.is_empty() && capacitor_nets.is_empty() {
        return;
    }

    // Union-find over conductive edges to isolate connected subnetworks.
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
    // voltage is set by a supply, not by the resistive network, so any
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
    let mut any_solved = false;

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
            Some(voltages) => {
                any_solved = true;
                for edge in &group_edges {
                    let (va, vb) = (voltages[&edge.net_a], voltages[&edge.net_b]);
                    let current = (va - vb) * edge.conductance;
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

    // Capacitor-only nets: every attachment is a known passive, so the
    // static current is known to be zero.
    for net_name in &capacitor_nets {
        if !opaque_nets.contains(net_name)
            && !graph_nets.contains(net_name.as_str())
            && !uninferable.contains(net_name)
        {
            any_solved = true;
            sink_static.entry(net_name.clone()).or_default();
            source_static.entry(net_name.clone()).or_default();
        }
    }
    let _ = any_solved;

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
