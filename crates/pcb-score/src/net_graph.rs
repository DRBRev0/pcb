//! Per-net copper connectivity graph and derived routing statistics.
//!
//! Connectivity is computed from tracks, arcs, vias, pads and filled zone
//! polygons with a small snap tolerance. Complexity is quadratic per net,
//! which is fine at net scale.

use std::collections::{BTreeMap, BTreeSet};

use crate::board::{ArcTrack, BoardModel, Pad, Point, Track, Zone};

/// Snap tolerance for endpoint coincidence, in mm.
const EPS: f64 = 0.01;

#[derive(Debug, Clone)]
pub struct NetStats {
    pub net: i64,
    pub name: String,
    /// Total routed copper length (tracks + arcs), mm.
    pub routed_length: f64,
    pub via_count: usize,
    pub layers_used: BTreeSet<String>,
    pub pad_count: usize,
    /// All pads joined through copper (tracks/arcs/vias/zones).
    pub connected: bool,
    /// Connected components among this net's pads.
    pub pad_components: usize,
    /// Euclidean MST lower bound over pad centers, mm.
    pub mst_length: f64,
    /// Track endpoints of degree 1 that land on no pad/via/zone.
    pub stub_count: usize,
    pub stub_length: f64,
    pub segment_count: usize,
    /// Consecutive same-layer segments doubling back (> 135 deg turn).
    pub direction_reversals: usize,
    /// Roughly 90 deg course changes between connected segments.
    pub right_angle_corners: usize,
    /// Junctions where copper meets at less than 30 deg (acid traps).
    pub acute_junctions: usize,
    /// Pairs of touching, collinear, same-width segments that could merge.
    pub mergeable_pairs: usize,
    /// Whether the net owns at least one filled zone polygon.
    pub has_zone: bool,
}

impl NetStats {
    /// Routed length / MST lower bound; `None` for unroutable/trivial nets.
    pub fn detour(&self) -> Option<f64> {
        (self.connected && self.pad_count >= 2 && self.mst_length > 1e-9)
            .then(|| self.routed_length / self.mst_length)
    }
}

struct UnionFind {
    parent: Vec<usize>,
}

impl UnionFind {
    fn new(n: usize) -> Self {
        Self {
            parent: (0..n).collect(),
        }
    }
    fn find(&mut self, i: usize) -> usize {
        if self.parent[i] != i {
            let root = self.find(self.parent[i]);
            self.parent[i] = root;
        }
        self.parent[i]
    }
    fn union(&mut self, a: usize, b: usize) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra != rb {
            self.parent[ra] = rb;
        }
    }
}

enum Element<'a> {
    Track(&'a Track),
    Arc(&'a ArcTrack),
    Via(&'a crate::board::Via),
    Pad(&'a Pad),
    ZonePoly(&'a Zone, usize),
}

fn dist_point_segment(p: Point, a: Point, b: Point) -> f64 {
    let (dx, dy) = (b.x - a.x, b.y - a.y);
    let len2 = dx * dx + dy * dy;
    if len2 < 1e-18 {
        return p.dist(&a);
    }
    let t = (((p.x - a.x) * dx + (p.y - a.y) * dy) / len2).clamp(0.0, 1.0);
    p.dist(&Point {
        x: a.x + t * dx,
        y: a.y + t * dy,
    })
}

pub fn point_in_polygon(p: Point, polygon: &[Point]) -> bool {
    let mut inside = false;
    let n = polygon.len();
    if n < 3 {
        return false;
    }
    let mut j = n - 1;
    for i in 0..n {
        let (pi, pj) = (polygon[i], polygon[j]);
        if ((pi.y > p.y) != (pj.y > p.y))
            && (p.x < (pj.x - pi.x) * (p.y - pi.y) / (pj.y - pi.y) + pi.x)
        {
            inside = !inside;
        }
        j = i;
    }
    inside
}

fn track_endpoints(e: &Element) -> Vec<(Point, String)> {
    match e {
        Element::Track(t) => vec![(t.start, t.layer.clone()), (t.end, t.layer.clone())],
        Element::Arc(a) => vec![(a.start, a.layer.clone()), (a.end, a.layer.clone())],
        _ => Vec::new(),
    }
}

fn elements_touch(a: &Element, b: &Element, copper_layers: &[String]) -> bool {
    use Element::*;
    match (a, b) {
        (Track(_) | Arc(_), Track(_) | Arc(_)) => {
            let (ea, eb) = (track_endpoints(a), track_endpoints(b));
            // Endpoint-to-endpoint or endpoint-on-segment (T junction).
            for (p, layer) in &ea {
                for (q, other_layer) in &eb {
                    if layer == other_layer && p.dist(q) <= EPS {
                        return true;
                    }
                }
                if let Track(t) = b
                    && &t.layer == layer
                    && dist_point_segment(*p, t.start, t.end) <= (t.width / 2.0).max(EPS)
                {
                    return true;
                }
            }
            for (q, layer) in &eb {
                if let Track(t) = a
                    && &t.layer == layer
                    && dist_point_segment(*q, t.start, t.end) <= (t.width / 2.0).max(EPS)
                {
                    return true;
                }
            }
            false
        }
        (Track(_) | Arc(_), Via(v)) | (Via(v), Track(_) | Arc(_)) => {
            let track = if matches!(a, Via(_)) { b } else { a };
            let reach = (v.size / 2.0).max(EPS);
            track_endpoints(track).iter().any(|(p, layer)| {
                via_spans_layer(v, layer, copper_layers) && p.dist(&v.at) <= reach
            })
        }
        (Track(_) | Arc(_), Pad(pad)) | (Pad(pad), Track(_) | Arc(_)) => {
            let track = if matches!(a, Pad(_)) { b } else { a };
            let reach = pad.reach().max(EPS);
            track_endpoints(track)
                .iter()
                .any(|(p, layer)| pad.on_copper(copper_layers, layer) && p.dist(&pad.at) <= reach)
        }
        (Via(v), Pad(pad)) | (Pad(pad), Via(v)) => {
            pad.at.dist(&v.at) <= (pad.reach() + v.size / 2.0).max(EPS)
                && v.layers.iter().any(|l| pad.on_copper(copper_layers, l))
        }
        (Via(v1), Via(v2)) => v1.at.dist(&v2.at) <= (v1.size + v2.size) / 2.0,
        (ZonePoly(zone, idx), other) | (other, ZonePoly(zone, idx)) => {
            let poly = &zone.filled_polygons[*idx];
            match other {
                Track(t) => {
                    t.layer == poly.layer
                        && (point_in_polygon(t.start, &poly.points)
                            || point_in_polygon(t.end, &poly.points))
                }
                Arc(arc) => {
                    arc.layer == poly.layer
                        && (point_in_polygon(arc.start, &poly.points)
                            || point_in_polygon(arc.end, &poly.points))
                }
                Via(v) => {
                    via_spans_layer(v, &poly.layer, copper_layers)
                        && point_in_polygon(v.at, &poly.points)
                }
                Pad(pad) => {
                    pad.on_copper(copper_layers, &poly.layer)
                        && point_in_polygon(pad.at, &poly.points)
                }
                ZonePoly(other_zone, other_idx) => {
                    // Same-layer overlapping fills of the same net: sample.
                    let other_poly = &other_zone.filled_polygons[*other_idx];
                    poly.layer == other_poly.layer
                        && other_poly
                            .points
                            .iter()
                            .any(|p| point_in_polygon(*p, &poly.points))
                }
            }
        }
        _ => false,
    }
}

/// A via spans a layer if the layer sits between its start/end copper layers.
pub fn via_spans_layer(via: &crate::board::Via, layer: &str, copper_layers: &[String]) -> bool {
    if via.layers.iter().any(|l| l == layer) {
        return true;
    }
    let idx = |name: &str| copper_layers.iter().position(|l| l == name);
    let (Some(first), Some(last)) = (
        via.layers.first().and_then(|l| idx(l)),
        via.layers.last().and_then(|l| idx(l)),
    ) else {
        return false;
    };
    let (lo, hi) = (first.min(last), first.max(last));
    idx(layer).is_some_and(|i| i >= lo && i <= hi)
}

/// Euclidean MST length over the given points (Prim's algorithm).
fn mst_length(points: &[Point]) -> f64 {
    let n = points.len();
    if n < 2 {
        return 0.0;
    }
    let mut in_tree = vec![false; n];
    let mut best = vec![f64::INFINITY; n];
    in_tree[0] = true;
    for i in 1..n {
        best[i] = points[0].dist(&points[i]);
    }
    let mut total = 0.0;
    for _ in 1..n {
        let mut next = None;
        let mut next_dist = f64::INFINITY;
        for i in 0..n {
            if !in_tree[i] && best[i] < next_dist {
                next = Some(i);
                next_dist = best[i];
            }
        }
        let Some(next) = next else { break };
        in_tree[next] = true;
        total += next_dist;
        for i in 0..n {
            if !in_tree[i] {
                best[i] = best[i].min(points[next].dist(&points[i]));
            }
        }
    }
    total
}

pub fn compute_net_stats(board: &BoardModel) -> BTreeMap<i64, NetStats> {
    let mut result = BTreeMap::new();

    for net_id in board.used_net_ids() {
        let tracks: Vec<&Track> = board.tracks.iter().filter(|t| t.net == net_id).collect();
        let arcs: Vec<&ArcTrack> = board.arcs.iter().filter(|a| a.net == net_id).collect();
        let vias: Vec<&crate::board::Via> = board.vias.iter().filter(|v| v.net == net_id).collect();
        let pads: Vec<&Pad> = board
            .footprints
            .iter()
            .flat_map(|f| f.pads.iter())
            .filter(|p| p.net == Some(net_id))
            .collect();
        let zones: Vec<&Zone> = board
            .zones
            .iter()
            .filter(|z| z.net == net_id && !z.filled_polygons.is_empty())
            .collect();

        if tracks.is_empty()
            && arcs.is_empty()
            && vias.is_empty()
            && pads.is_empty()
            && zones.is_empty()
        {
            continue;
        }

        let mut elements: Vec<Element> = Vec::new();
        elements.extend(tracks.iter().map(|t| Element::Track(t)));
        elements.extend(arcs.iter().map(|a| Element::Arc(a)));
        elements.extend(vias.iter().map(|v| Element::Via(v)));
        elements.extend(pads.iter().map(|p| Element::Pad(p)));
        for zone in &zones {
            for idx in 0..zone.filled_polygons.len() {
                elements.push(Element::ZonePoly(zone, idx));
            }
        }

        let mut uf = UnionFind::new(elements.len());
        for i in 0..elements.len() {
            for j in (i + 1)..elements.len() {
                if elements_touch(&elements[i], &elements[j], &board.copper_layers) {
                    uf.union(i, j);
                }
            }
        }

        let pad_offset = tracks.len() + arcs.len() + vias.len();
        let pad_roots: BTreeSet<usize> = (0..pads.len()).map(|k| uf.find(pad_offset + k)).collect();
        let pad_components = pad_roots.len();
        let connected = pad_components <= 1;

        let routed_length: f64 = tracks.iter().map(|t| t.length()).sum::<f64>()
            + arcs.iter().map(|a| a.length()).sum::<f64>();

        let mut layers_used: BTreeSet<String> = BTreeSet::new();
        layers_used.extend(tracks.iter().map(|t| t.layer.clone()));
        layers_used.extend(arcs.iter().map(|a| a.layer.clone()));

        // Endpoint degree map for stubs, reversals and mergeable pairs.
        let mut stub_count = 0;
        let mut stub_length = 0.0;
        let mut direction_reversals = 0;
        let mut right_angle_corners = 0;
        let mut acute_junctions = 0;
        let mut mergeable_pairs = 0;
        for (i, t) in tracks.iter().enumerate() {
            for (endpoint, other_point) in [(t.start, t.end), (t.end, t.start)] {
                let mut attached_track: Vec<usize> = Vec::new();
                for (j, u) in tracks.iter().enumerate() {
                    if i == j || u.layer != t.layer {
                        continue;
                    }
                    if endpoint.dist(&u.start) <= EPS
                        || endpoint.dist(&u.end) <= EPS
                        || dist_point_segment(endpoint, u.start, u.end) <= (u.width / 2.0).max(EPS)
                    {
                        attached_track.push(j);
                    }
                }
                let on_terminal = pads.iter().any(|p| {
                    p.on_copper(&board.copper_layers, &t.layer)
                        && endpoint.dist(&p.at) <= p.reach().max(EPS)
                }) || vias.iter().any(|v| {
                    via_spans_layer(v, &t.layer, &board.copper_layers)
                        && endpoint.dist(&v.at) <= (v.size / 2.0).max(EPS)
                }) || zones.iter().any(|z| {
                    z.filled_polygons.iter().any(|poly| {
                        poly.layer == t.layer && point_in_polygon(endpoint, &poly.points)
                    })
                });

                if attached_track.is_empty() && !on_terminal {
                    stub_count += 1;
                    stub_length += t.length();
                }

                // Direction change analysis against each attached segment.
                for &j in &attached_track {
                    if j <= i {
                        continue;
                    }
                    let u = tracks[j];
                    let (d1x, d1y) = (other_point.x - endpoint.x, other_point.y - endpoint.y);
                    let far = if endpoint.dist(&u.start) <= EPS {
                        u.end
                    } else {
                        u.start
                    };
                    let (d2x, d2y) = (far.x - endpoint.x, far.y - endpoint.y);
                    let (l1, l2) = (d1x.hypot(d1y), d2x.hypot(d2y));
                    if l1 < 1e-9 || l2 < 1e-9 {
                        continue;
                    }
                    let cos = (d1x * d2x + d1y * d2y) / (l1 * l2);
                    // Both directions point away from the joint, so the course
                    // change angle is PI - acos(cos): straight-through gives
                    // cos = -1, doubling back gives cos = +1.
                    if cos > (45.0f64).to_radians().cos() {
                        // Course change sharper than 135 deg: doubling back.
                        direction_reversals += 1;
                    }
                    if cos.abs() < (80.0f64).to_radians().cos() {
                        // Course change of roughly 90 deg (80..100 deg).
                        right_angle_corners += 1;
                    }
                    if cos > (30.0f64).to_radians().cos() {
                        // Copper angle below 30 deg at the junction.
                        acute_junctions += 1;
                    }
                    let cross = (d1x * d2y - d1y * d2x).abs();
                    if cross <= 1e-6 * l1 * l2 && cos < 0.0 && (t.width - u.width).abs() < 1e-9 {
                        mergeable_pairs += 1;
                    }
                }
            }
        }

        let pad_points: Vec<Point> = pads.iter().map(|p| p.at).collect();

        result.insert(
            net_id,
            NetStats {
                net: net_id,
                name: board.net_name(net_id).to_string(),
                routed_length,
                via_count: vias.len(),
                layers_used,
                pad_count: pads.len(),
                connected,
                pad_components: pad_components.max(1),
                mst_length: mst_length(&pad_points),
                stub_count,
                stub_length,
                segment_count: tracks.len() + arcs.len(),
                direction_reversals,
                right_angle_corners,
                acute_junctions,
                mergeable_pairs,
                has_zone: !zones.is_empty(),
            },
        );
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::board::BoardModel;

    fn board(extra: &str) -> BoardModel {
        let src = format!(
            r#"(kicad_pcb
  (layers (0 "F.Cu" signal) (2 "B.Cu" signal))
  (net 0 "")
  (net 1 "SIG")
  (footprint "lib:A" (layer "F.Cu") (at 0 0)
    (pad "1" smd rect (at 0 0) (size 1 1) (layers "F.Cu") (net 1 "SIG")))
  (footprint "lib:B" (layer "F.Cu") (at 10 0)
    (pad "1" smd rect (at 0 0) (size 1 1) (layers "F.Cu") (net 1 "SIG")))
  {extra}
)"#
        );
        BoardModel::parse(&src).unwrap()
    }

    #[test]
    fn unrouted_net_is_disconnected() {
        let stats = compute_net_stats(&board(""));
        let sig = &stats[&1];
        assert!(!sig.connected);
        assert_eq!(sig.pad_components, 2);
        assert!((sig.mst_length - 10.0).abs() < 1e-9);
    }

    #[test]
    fn straight_route_connects_and_has_detour_1() {
        let stats = compute_net_stats(&board(
            r#"(segment (start 0 0) (end 10 0) (width 0.25) (layer "F.Cu") (net 1))"#,
        ));
        let sig = &stats[&1];
        assert!(sig.connected);
        assert!((sig.detour().unwrap() - 1.0).abs() < 1e-9);
        assert_eq!(sig.stub_count, 0);
    }

    #[test]
    fn l_route_detour() {
        let stats = compute_net_stats(&board(
            r#"(segment (start 0 0) (end 0 5) (width 0.25) (layer "F.Cu") (net 1))
               (segment (start 0 5) (end 10 5) (width 0.25) (layer "F.Cu") (net 1))
               (segment (start 10 5) (end 10 0) (width 0.25) (layer "F.Cu") (net 1))"#,
        ));
        let sig = &stats[&1];
        assert!(sig.connected);
        assert!((sig.detour().unwrap() - 2.0).abs() < 1e-9);
    }

    #[test]
    fn via_connects_layers() {
        let stats = compute_net_stats(&board(
            r#"(segment (start 0 0) (end 5 0) (width 0.25) (layer "F.Cu") (net 1))
               (via (at 5 0) (size 0.6) (drill 0.3) (layers "F.Cu" "B.Cu") (net 1))
               (segment (start 5 0) (end 10 0) (width 0.25) (layer "B.Cu") (net 1))
               (via (at 10 0) (size 0.6) (drill 0.3) (layers "F.Cu" "B.Cu") (net 1))"#,
        ));
        let sig = &stats[&1];
        assert!(sig.connected);
        assert_eq!(sig.via_count, 2);
        assert_eq!(sig.layers_used.len(), 2);
    }

    #[test]
    fn dangling_track_is_a_stub() {
        let stats = compute_net_stats(&board(
            r#"(segment (start 0 0) (end 10 0) (width 0.25) (layer "F.Cu") (net 1))
               (segment (start 5 0) (end 5 3) (width 0.25) (layer "F.Cu") (net 1))"#,
        ));
        let sig = &stats[&1];
        assert!(sig.connected);
        assert_eq!(sig.stub_count, 1);
        assert!((sig.stub_length - 3.0).abs() < 1e-9);
    }

    #[test]
    fn zone_connects_pads() {
        let stats = compute_net_stats(&board(
            r#"(zone (net 1) (net_name "SIG") (layer "F.Cu")
                 (filled_polygon (layer "F.Cu")
                   (pts (xy -2 -2) (xy 12 -2) (xy 12 2) (xy -2 2))))"#,
        ));
        let sig = &stats[&1];
        assert!(sig.connected);
        assert!(sig.has_zone);
    }
}
