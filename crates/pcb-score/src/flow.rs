//! Per-branch electrical current flow on a net's copper graph.
//!
//! Models the routed net as a resistive network (track conductance
//! proportional to width/length, vias and pads near-ideal), injects the
//! declared per-port currents at the pads of the declaring module subtree,
//! and solves the node-voltage system to get each track segment's share of
//! the current. Used by `trace_current_capacity` to judge every segment
//! against the current it actually carries instead of the net total.

use std::collections::HashMap;

use pcb_sch::{InstanceKind, Schematic};

use crate::board::{BoardModel, Point};

const EPS: f64 = 0.01;
/// Near-ideal conductance for vias/pad bridges, in the same arbitrary units
/// as track conductances (width_mm / length_mm). High enough to be
/// negligible, low enough to keep the system well-conditioned.
const BRIDGE_CONDUCTANCE: f64 = 1e4;
/// Refuse to solve unreasonably large nets (dense solver is O(n^3)).
const MAX_NODES: usize = 1500;

/// Currents flowing through each track of a net, in amperes, indexed like
/// the `tracks` slice passed to [`solve_net_flow`].
pub struct NetFlow {
    pub track_amps: Vec<f64>,
}

/// A current injection point: board position, layer, signed amps
/// (positive = current enters the copper here).
pub struct Injection {
    pub at: Point,
    pub layer: String,
    pub amps: f64,
}

fn pad_copper_layer(pad: &crate::board::Pad) -> String {
    pad.layers
        .iter()
        .find(|l| l.ends_with(".Cu"))
        .cloned()
        .unwrap_or_else(|| "F.Cu".to_string())
}

/// Map the netlist's `current_ports` of `net_name` onto board pads.
///
/// Each port label is a module path (`"ldo.VIN"` declares the io `VIN` of
/// module instance `ldo`); the physical attachment points are the pads on
/// this net belonging to components *inside* that module instance. The
/// port's current is split equally across those pads. Returns `None` when
/// any port cannot be mapped to at least one pad (the caller then falls
/// back to the conservative model).
pub fn map_port_currents(
    board: &BoardModel,
    schematic: &Schematic,
    net_name: &str,
    ports: &[crate::classify::PortCurrent],
) -> Option<Vec<Injection>> {
    let net = schematic.nets.get(net_name)?;

    // Component pin refs on this net: (module path segments, refdes).
    let mut pin_owners: Vec<(Vec<String>, String)> = Vec::new();
    for port_ref in &net.ports {
        if port_ref.instance_path.len() < 2 {
            continue;
        }
        // Last segment is the pin name, the rest identifies the component.
        let component_path = &port_ref.instance_path[..port_ref.instance_path.len() - 1];
        let component_ref =
            pcb_sch::InstanceRef::new(port_ref.module.clone(), component_path.to_vec());
        let Some(instance) = schematic.instances.get(&component_ref) else {
            continue;
        };
        if instance.kind != InstanceKind::Component {
            continue;
        }
        let Some(refdes) = &instance.reference_designator else {
            continue;
        };
        pin_owners.push((component_path.to_vec(), refdes.clone()));
    }
    if pin_owners.is_empty() {
        return None;
    }

    let net_id = board
        .nets
        .iter()
        .find(|(_, name)| name.as_str() == net_name)
        .map(|(&id, _)| id)?;

    let mut injections: Vec<Injection> = Vec::new();
    for port in ports {
        let mut pads: Vec<(Point, String)> = Vec::new();
        if let Some(refdes) = port.port.strip_prefix("component:") {
            // Statically inferred entry: inject at that component's pads.
            if let Some(footprint) = board.footprints.iter().find(|f| f.reference == refdes) {
                for pad in footprint.pads.iter().filter(|p| p.net == Some(net_id)) {
                    pads.push((pad.at, pad_copper_layer(pad)));
                }
            }
        } else {
            // "a.b.PARAM" -> module instance path ["a", "b"]; a root-level
            // port ("PARAM") owns the whole design. The physical attachment
            // points are the pads of components inside that module subtree.
            let module_path: Vec<&str> = {
                let mut segments: Vec<&str> = port.port.split('.').collect();
                segments.pop();
                segments
            };
            for (component_path, refdes) in &pin_owners {
                let in_subtree = component_path.len() > module_path.len()
                    && component_path
                        .iter()
                        .zip(module_path.iter())
                        .all(|(a, b)| a == b);
                if !in_subtree {
                    continue;
                }
                if let Some(footprint) = board.footprints.iter().find(|f| &f.reference == refdes) {
                    for pad in footprint.pads.iter().filter(|p| p.net == Some(net_id)) {
                        pads.push((pad.at, pad_copper_layer(pad)));
                    }
                }
            }
        }
        if pads.is_empty() {
            return None;
        }
        let share = port.amps / pads.len() as f64;
        let sign = if port.is_sink { -1.0 } else { 1.0 };
        for (at, layer) in pads {
            injections.push(Injection {
                at,
                layer,
                amps: sign * share,
            });
        }
    }
    Some(injections)
}

/// Solve the current distribution over `tracks` (all belonging to one net)
/// given injections. Returns `None` when the model cannot be solved
/// (imbalanced or unlocatable injections, disconnected graph, too large).
pub fn solve_net_flow(board: &BoardModel, net: i64, injections: &[Injection]) -> Option<NetFlow> {
    let tracks: Vec<usize> = board
        .tracks
        .iter()
        .enumerate()
        .filter(|(_, t)| t.net == net)
        .map(|(i, _)| i)
        .collect();
    if tracks.is_empty() || injections.is_empty() {
        return None;
    }

    // Node ids keyed by (rounded position, layer index).
    let layer_index: HashMap<&str, u16> = board
        .copper_layers
        .iter()
        .enumerate()
        .map(|(i, l)| (l.as_str(), i as u16))
        .collect();
    let mut nodes: HashMap<(i64, i64, u16), usize> = HashMap::new();
    let key = |p: Point, layer: u16| {
        (
            (p.x / EPS).round() as i64,
            (p.y / EPS).round() as i64,
            layer,
        )
    };
    let node_of = |p: Point, layer: u16, nodes: &mut HashMap<(i64, i64, u16), usize>| {
        let n = nodes.len();
        *nodes.entry(key(p, layer)).or_insert(n)
    };

    // Edges: (a, b, conductance).
    let mut edges: Vec<(usize, usize, f64)> = Vec::new();
    for &idx in &tracks {
        let track = &board.tracks[idx];
        let layer = *layer_index.get(track.layer.as_str())?;
        let a = node_of(track.start, layer, &mut nodes);
        let b = node_of(track.end, layer, &mut nodes);
        let g = track.width / track.length().max(EPS);
        edges.push((a, b, g));
    }
    // Vias bridge every copper layer they span at their position.
    for via in board.vias.iter().filter(|v| v.net == net) {
        let spanned: Vec<u16> = board
            .copper_layers
            .iter()
            .enumerate()
            .filter(|(_, l)| crate::net_graph::via_spans_layer(via, l, &board.copper_layers))
            .map(|(i, _)| i as u16)
            .collect();
        for pair in spanned.windows(2) {
            let a = node_of(via.at, pair[0], &mut nodes);
            let b = node_of(via.at, pair[1], &mut nodes);
            edges.push((a, b, BRIDGE_CONDUCTANCE));
        }
    }
    // Pads: through-hole pads bridge all layers; every pad also bridges to
    // any node within its reach so tracks ending on the pad surface connect.
    let mut pad_nodes: Vec<(usize, Point, f64)> = Vec::new();
    for footprint in &board.footprints {
        for pad in footprint.pads.iter().filter(|p| p.net == Some(net)) {
            let reach = pad.size.0.max(pad.size.1) / 2.0;
            let layers: Vec<u16> = if pad.kind == "thru_hole" {
                (0..board.copper_layers.len() as u16).collect()
            } else {
                pad.layers
                    .iter()
                    .filter_map(|l| layer_index.get(l.as_str()).copied())
                    .collect()
            };
            let mut prev: Option<usize> = None;
            for layer in layers {
                let node = node_of(pad.at, layer, &mut nodes);
                pad_nodes.push((node, pad.at, reach));
                if let Some(prev) = prev {
                    edges.push((prev, node, BRIDGE_CONDUCTANCE));
                }
                prev = Some(node);
            }
        }
    }
    // Bridge pads to nearby track endpoints on any layer the pad occupies
    // (a track may stop at the pad edge rather than its exact center).
    {
        let existing: Vec<((i64, i64, u16), usize)> = nodes.iter().map(|(k, v)| (*k, *v)).collect();
        for ((kx, ky, _), node) in existing {
            let p = Point {
                x: kx as f64 * EPS,
                y: ky as f64 * EPS,
            };
            for (pad_node, pad_at, reach) in &pad_nodes {
                if node != *pad_node && p.dist(pad_at) <= reach.max(EPS) + EPS {
                    edges.push((*pad_node, node, BRIDGE_CONDUCTANCE));
                }
            }
        }
    }

    if nodes.len() > MAX_NODES {
        return None;
    }
    let n = nodes.len();

    // Injection vector; locate each injection's node (snap to nearest node
    // within 2*EPS on the right layer, else fail).
    let mut current = vec![0.0f64; n];
    for injection in injections {
        let layer = *layer_index.get(injection.layer.as_str())?;
        let target = key(injection.at, layer);
        let node = nodes.get(&target).copied().or_else(|| {
            nodes
                .iter()
                .filter(|((_, _, l), _)| *l == layer)
                .map(|((x, y, _), &node)| {
                    let p = Point {
                        x: *x as f64 * EPS,
                        y: *y as f64 * EPS,
                    };
                    (injection.at.dist(&p), node)
                })
                .filter(|(d, _)| *d <= 1.0)
                .min_by(|a, b| a.0.partial_cmp(&b.0).unwrap_or(std::cmp::Ordering::Equal))
                .map(|(_, node)| node)
        })?;
        current[node] += injection.amps;
    }
    // The system only has a solution if injections sum to ~zero; distribute
    // any residual (declared source headroom) across source nodes.
    let residual: f64 = current.iter().sum();
    if residual.abs() > 1e-9 {
        let positive: f64 = current.iter().filter(|c| **c > 0.0).sum();
        if positive <= residual.abs() || positive <= 0.0 {
            return None;
        }
        for c in current.iter_mut().filter(|c| **c > 0.0) {
            *c -= residual * (*c / positive);
        }
    }

    // Dense Laplacian solve with node n-1 grounded.
    let mut matrix = vec![vec![0.0f64; n]; n];
    for (a, b, g) in &edges {
        if a == b {
            continue;
        }
        matrix[*a][*a] += g;
        matrix[*b][*b] += g;
        matrix[*a][*b] -= g;
        matrix[*b][*a] -= g;
    }
    let dim = n - 1;
    let mut aug: Vec<Vec<f64>> = (0..dim)
        .map(|i| {
            let mut row: Vec<f64> = matrix[i][..dim].to_vec();
            row.push(current[i]);
            row
        })
        .collect();
    // Gaussian elimination with partial pivoting.
    for col in 0..dim {
        let pivot = (col..dim)
            .max_by(|&a, &b| {
                aug[a][col]
                    .abs()
                    .partial_cmp(&aug[b][col].abs())
                    .unwrap_or(std::cmp::Ordering::Equal)
            })
            .unwrap();
        if aug[pivot][col].abs() < 1e-12 {
            // Singular: disconnected copper island carrying an injection.
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
    let mut voltage = vec![0.0f64; n];
    for row in (0..dim).rev() {
        let mut sum = aug[row][dim];
        for (k, v) in voltage.iter().enumerate().take(dim).skip(row + 1) {
            sum -= aug[row][k] * v;
        }
        voltage[row] = sum / aug[row][row];
    }

    // Track currents from voltage differences (track edges come first, in
    // `tracks` order).
    let track_amps: Vec<f64> = edges[..tracks.len()]
        .iter()
        .map(|(a, b, g)| ((voltage[*a] - voltage[*b]) * g).abs())
        .collect();
    Some(NetFlow { track_amps })
}

/// Convenience: solved per-track amps for a net, keyed by global track index.
pub fn per_track_currents(
    board: &BoardModel,
    schematic: &Schematic,
    net_id: i64,
    net_name: &str,
    ports: &[crate::classify::PortCurrent],
) -> Option<HashMap<usize, f64>> {
    let has_sink = ports.iter().any(|p| p.is_sink);
    let has_source = ports.iter().any(|p| !p.is_sink);
    if !has_sink || !has_source {
        // Without both ends declared there is no closed circuit to solve.
        return None;
    }
    let injections = map_port_currents(board, schematic, net_name, ports)?;
    let flow = solve_net_flow(board, net_id, &injections)?;
    let indices: Vec<usize> = board
        .tracks
        .iter()
        .enumerate()
        .filter(|(_, t)| t.net == net_id)
        .map(|(i, _)| i)
        .collect();
    Some(indices.into_iter().zip(flow.track_amps).collect())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::board::Track;

    fn board_with_tracks(tracks: Vec<Track>) -> BoardModel {
        let mut board = BoardModel::default();
        board.copper_layers = vec!["F.Cu".to_string(), "B.Cu".to_string()];
        board.nets.insert(1, "N".to_string());
        board.tracks = tracks;
        board
    }

    fn track(x0: f64, y0: f64, x1: f64, y1: f64, width: f64) -> Track {
        Track {
            start: Point { x: x0, y: y0 },
            end: Point { x: x1, y: y1 },
            width,
            layer: "F.Cu".to_string(),
            net: 1,
        }
    }

    #[test]
    fn series_path_carries_full_current() {
        let board = board_with_tracks(vec![
            track(0.0, 0.0, 5.0, 0.0, 0.3),
            track(5.0, 0.0, 10.0, 0.0, 0.3),
        ]);
        let injections = [
            Injection {
                at: Point { x: 0.0, y: 0.0 },
                layer: "F.Cu".into(),
                amps: 2.0,
            },
            Injection {
                at: Point { x: 10.0, y: 0.0 },
                layer: "F.Cu".into(),
                amps: -2.0,
            },
        ];
        let flow = solve_net_flow(&board, 1, &injections).unwrap();
        for amps in &flow.track_amps {
            assert!((amps - 2.0).abs() < 1e-6, "got {amps}");
        }
    }

    #[test]
    fn parallel_paths_split_by_conductance() {
        // Two parallel branches of equal length, one twice as wide: currents
        // split 2:1.
        let board = board_with_tracks(vec![
            track(0.0, 0.0, 10.0, 0.0, 0.4),   // wide branch
            track(0.0, 0.0, 0.0, 3.0, 10.0),   // fat feeder to the narrow branch
            track(0.0, 3.0, 10.0, 3.0, 0.2),   // narrow branch
            track(10.0, 3.0, 10.0, 0.0, 10.0), // fat return
        ]);
        let injections = [
            Injection {
                at: Point { x: 0.0, y: 0.0 },
                layer: "F.Cu".into(),
                amps: 3.0,
            },
            Injection {
                at: Point { x: 10.0, y: 0.0 },
                layer: "F.Cu".into(),
                amps: -3.0,
            },
        ];
        let flow = solve_net_flow(&board, 1, &injections).unwrap();
        // Feeder resistance is negligible; expect ~2A wide / ~1A narrow.
        assert!(
            (flow.track_amps[0] - 2.0).abs() < 0.1,
            "wide {}",
            flow.track_amps[0]
        );
        assert!(
            (flow.track_amps[2] - 1.0).abs() < 0.1,
            "narrow {}",
            flow.track_amps[2]
        );
    }

    #[test]
    fn disconnected_injection_fails() {
        let board = board_with_tracks(vec![track(0.0, 0.0, 5.0, 0.0, 0.3)]);
        let injections = [
            Injection {
                at: Point { x: 0.0, y: 0.0 },
                layer: "F.Cu".into(),
                amps: 1.0,
            },
            Injection {
                at: Point { x: 50.0, y: 50.0 },
                layer: "F.Cu".into(),
                amps: -1.0,
            },
        ];
        assert!(solve_net_flow(&board, 1, &injections).is_none());
    }
}
