//! Typed geometry model of a `.kicad_pcb`, parsed with `pcb-sexpr`.
//!
//! Only the objects routing analysis needs are extracted: copper layers,
//! nets, tracks/arcs/vias, zones (with filled polygons), footprints with
//! absolute pad positions, the board outline and the stackup.

use std::collections::BTreeMap;

use anyhow::{Context, Result};
use pcb_sexpr::{Sexpr, SexprKind, find_child_list};

#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Point {
    pub x: f64,
    pub y: f64,
}

impl Point {
    pub fn dist(&self, other: &Point) -> f64 {
        (self.x - other.x).hypot(self.y - other.y)
    }
}

#[derive(Debug, Clone)]
pub struct Track {
    pub start: Point,
    pub end: Point,
    pub width: f64,
    pub layer: String,
    pub net: i64,
}

impl Track {
    pub fn length(&self) -> f64 {
        self.start.dist(&self.end)
    }
}

#[derive(Debug, Clone)]
pub struct ArcTrack {
    pub start: Point,
    pub mid: Point,
    pub end: Point,
    pub width: f64,
    pub layer: String,
    pub net: i64,
}

impl ArcTrack {
    /// Arc length from the three points (circumcircle); falls back to the
    /// chord length for degenerate (collinear) arcs.
    pub fn length(&self) -> f64 {
        let (a, b, c) = (self.start, self.mid, self.end);
        let d = 2.0 * (a.x * (b.y - c.y) + b.x * (c.y - a.y) + c.x * (a.y - b.y));
        if d.abs() < 1e-12 {
            return a.dist(&c);
        }
        let ux = ((a.x * a.x + a.y * a.y) * (b.y - c.y)
            + (b.x * b.x + b.y * b.y) * (c.y - a.y)
            + (c.x * c.x + c.y * c.y) * (a.y - b.y))
            / d;
        let uy = ((a.x * a.x + a.y * a.y) * (c.x - b.x)
            + (b.x * b.x + b.y * b.y) * (a.x - c.x)
            + (c.x * c.x + c.y * c.y) * (b.x - a.x))
            / d;
        let center = Point { x: ux, y: uy };
        let r = center.dist(&a);
        if r < 1e-9 {
            return a.dist(&c);
        }
        let angle = |p: Point| (p.y - center.y).atan2(p.x - center.x);
        let (aa, am, ac) = (angle(a), angle(b), angle(c));
        // Sweep from start to end passing through mid.
        let norm = |x: f64| x.rem_euclid(std::f64::consts::TAU);
        let sweep_ccw = norm(ac - aa);
        let mid_ccw = norm(am - aa);
        let sweep = if mid_ccw <= sweep_ccw {
            sweep_ccw
        } else {
            std::f64::consts::TAU - sweep_ccw
        };
        r * sweep
    }
}

#[derive(Debug, Clone)]
pub struct Via {
    pub at: Point,
    pub size: f64,
    pub drill: f64,
    /// Copper layer span, e.g. ["F.Cu", "B.Cu"].
    pub layers: Vec<String>,
    pub net: i64,
    /// "via", "blind" or "micro".
    pub kind: String,
}

#[derive(Debug, Clone)]
pub struct ZonePolygon {
    pub layer: String,
    pub points: Vec<Point>,
}

#[derive(Debug, Clone)]
pub struct Zone {
    pub net: i64,
    pub net_name: String,
    pub layers: Vec<String>,
    pub filled_polygons: Vec<ZonePolygon>,
}

#[derive(Debug, Clone)]
pub struct Pad {
    pub number: String,
    /// "smd", "thru_hole", "np_thru_hole", "connect".
    pub kind: String,
    /// Absolute board position of the pad center.
    pub at: Point,
    pub size: (f64, f64),
    pub drill: Option<f64>,
    pub layers: Vec<String>,
    pub net: Option<i64>,
    pub net_name: Option<String>,
}

impl Pad {
    pub fn on_copper(&self, copper_layers: &[String], layer: &str) -> bool {
        self.layers.iter().any(|l| {
            l == layer
                || (l == "*.Cu" && copper_layers.iter().any(|c| c == layer))
                || (l == "F.Cu" && layer == "F.Cu")
                || (l == "B.Cu" && layer == "B.Cu")
        })
    }

    /// Radius of the circle circumscribing the pad, used as a connection
    /// tolerance for track endpoints landing on the pad.
    pub fn reach(&self) -> f64 {
        (self.size.0.hypot(self.size.1)) / 2.0
    }
}

#[derive(Debug, Clone)]
pub struct Footprint {
    pub reference: String,
    pub footprint_id: String,
    pub layer: String,
    pub at: Point,
    pub rotation_deg: f64,
    pub pads: Vec<Pad>,
    /// Courtyard bounding box half-extents when present (approximated from
    /// pad extents otherwise).
    pub bbox_half: (f64, f64),
}

#[derive(Debug, Clone)]
pub struct OutlineSegment {
    pub start: Point,
    pub end: Point,
}

#[derive(Debug, Clone)]
pub struct StackupLayer {
    pub name: String,
    /// "copper", "core", "prepreg", or other dielectric/technical types.
    pub kind: String,
    pub thickness_mm: Option<f64>,
    pub epsilon_r: Option<f64>,
}

#[derive(Debug, Clone, Default)]
pub struct BoardModel {
    /// Copper layer names in stack order (front to back).
    pub copper_layers: Vec<String>,
    pub nets: BTreeMap<i64, String>,
    pub tracks: Vec<Track>,
    pub arcs: Vec<ArcTrack>,
    pub vias: Vec<Via>,
    pub zones: Vec<Zone>,
    pub footprints: Vec<Footprint>,
    pub outline: Vec<OutlineSegment>,
    pub stackup: Vec<StackupLayer>,
}

impl BoardModel {
    pub fn parse(source: &str) -> Result<Self> {
        let root = pcb_sexpr::parse(source).context("failed to parse .kicad_pcb")?;
        let items = root.as_list().context(".kicad_pcb root is not a list")?;
        anyhow::ensure!(
            items.first().and_then(Sexpr::as_sym) == Some("kicad_pcb"),
            "not a kicad_pcb file"
        );

        let mut model = BoardModel::default();
        for node in items.iter().skip(1) {
            let Some(children) = node.as_list() else {
                continue;
            };
            let Some(tag) = children.first().and_then(Sexpr::as_sym) else {
                continue;
            };
            match tag {
                "layers" => model.parse_layers(children),
                "net" => {
                    if let (Some(id), Some(name)) = (
                        children.get(1).and_then(Sexpr::as_int),
                        children.get(2).and_then(Sexpr::as_atom),
                    ) {
                        model.nets.insert(id, name.to_string());
                    }
                }
                "segment" => {
                    if let Some(track) = parse_segment(children) {
                        model.tracks.push(track);
                    }
                }
                "arc" => {
                    if let Some(arc) = parse_arc(children) {
                        model.arcs.push(arc);
                    }
                }
                "via" => {
                    if let Some(via) = parse_via(children) {
                        model.vias.push(via);
                    }
                }
                "zone" => {
                    if let Some(zone) = parse_zone(children) {
                        model.zones.push(zone);
                    }
                }
                "footprint" => {
                    if let Some(footprint) = parse_footprint(children) {
                        model.footprints.push(footprint);
                    }
                }
                "gr_line" | "gr_rect" | "gr_arc" | "gr_circle" | "gr_poly" => {
                    model.parse_outline_graphic(tag, children);
                }
                "setup" => model.parse_setup(children),
                _ => {}
            }
        }
        Ok(model)
    }

    fn parse_layers(&mut self, children: &[Sexpr]) {
        for entry in children.iter().skip(1) {
            let Some(fields) = entry.as_list() else {
                continue;
            };
            let name = fields.get(1).and_then(Sexpr::as_atom);
            let kind = fields.get(2).and_then(Sexpr::as_sym);
            if let (Some(name), Some(kind)) = (name, kind)
                && matches!(kind, "signal" | "power" | "mixed")
                && name.ends_with(".Cu")
            {
                self.copper_layers.push(name.to_string());
            }
        }
    }

    fn parse_outline_graphic(&mut self, tag: &str, children: &[Sexpr]) {
        let layer = find_child_list(children, "layer")
            .and_then(|l| l.get(1))
            .and_then(Sexpr::as_atom);
        if layer != Some("Edge.Cuts") {
            return;
        }
        match tag {
            "gr_line" => {
                if let (Some(start), Some(end)) =
                    (point_of(children, "start"), point_of(children, "end"))
                {
                    self.outline.push(OutlineSegment { start, end });
                }
            }
            "gr_rect" => {
                if let (Some(a), Some(c)) = (point_of(children, "start"), point_of(children, "end"))
                {
                    let b = Point { x: c.x, y: a.y };
                    let d = Point { x: a.x, y: c.y };
                    self.outline.extend([
                        OutlineSegment { start: a, end: b },
                        OutlineSegment { start: b, end: c },
                        OutlineSegment { start: c, end: d },
                        OutlineSegment { start: d, end: a },
                    ]);
                }
            }
            "gr_arc" => {
                // Linearize with the chord; good enough for clearance metrics.
                if let (Some(start), Some(mid), Some(end)) = (
                    point_of(children, "start"),
                    point_of(children, "mid"),
                    point_of(children, "end"),
                ) {
                    self.outline.push(OutlineSegment { start, end: mid });
                    self.outline.push(OutlineSegment { start: mid, end });
                }
            }
            "gr_circle" => {
                if let (Some(center), Some(rim)) =
                    (point_of(children, "center"), point_of(children, "end"))
                {
                    let r = center.dist(&rim);
                    let n = 16;
                    let mut prev = Point {
                        x: center.x + r,
                        y: center.y,
                    };
                    for i in 1..=n {
                        let theta = std::f64::consts::TAU * (i as f64) / (n as f64);
                        let next = Point {
                            x: center.x + r * theta.cos(),
                            y: center.y + r * theta.sin(),
                        };
                        self.outline.push(OutlineSegment {
                            start: prev,
                            end: next,
                        });
                        prev = next;
                    }
                }
            }
            "gr_poly" => {
                if let Some(pts) = find_child_list(children, "pts") {
                    let points = xy_points(pts);
                    for pair in points.windows(2) {
                        self.outline.push(OutlineSegment {
                            start: pair[0],
                            end: pair[1],
                        });
                    }
                    if points.len() > 2 {
                        self.outline.push(OutlineSegment {
                            start: points[points.len() - 1],
                            end: points[0],
                        });
                    }
                }
            }
            _ => {}
        }
    }

    fn parse_setup(&mut self, children: &[Sexpr]) {
        let Some(stackup) = find_child_list(children, "stackup") else {
            return;
        };
        for entry in stackup.iter().skip(1) {
            let Some(fields) = entry.as_list() else {
                continue;
            };
            if fields.first().and_then(Sexpr::as_sym) != Some("layer") {
                continue;
            }
            let Some(name) = fields.get(1).and_then(Sexpr::as_atom) else {
                continue;
            };
            let kind = find_child_list(fields, "type")
                .and_then(|t| t.get(1))
                .and_then(Sexpr::as_atom)
                .unwrap_or("")
                .to_string();
            let thickness_mm = find_child_list(fields, "thickness")
                .and_then(|t| t.get(1))
                .and_then(number);
            let epsilon_r = find_child_list(fields, "epsilon_r")
                .and_then(|t| t.get(1))
                .and_then(number);
            self.stackup.push(StackupLayer {
                name: name.to_string(),
                kind: if kind.is_empty() {
                    if name.ends_with(".Cu") {
                        "copper".to_string()
                    } else {
                        String::new()
                    }
                } else {
                    kind
                },
                thickness_mm,
                epsilon_r,
            });
        }
    }

    pub fn net_name(&self, net: i64) -> &str {
        self.nets.get(&net).map(String::as_str).unwrap_or("")
    }

    /// Nets that have at least one copper object or pad.
    pub fn used_net_ids(&self) -> Vec<i64> {
        let mut ids: Vec<i64> = self
            .nets
            .keys()
            .copied()
            .filter(|&id| id != 0 && !self.net_name(id).is_empty())
            .collect();
        ids.sort_unstable();
        ids
    }

    /// Bounding box of the board outline, if any.
    pub fn outline_bbox(&self) -> Option<(Point, Point)> {
        let mut min = Point {
            x: f64::INFINITY,
            y: f64::INFINITY,
        };
        let mut max = Point {
            x: f64::NEG_INFINITY,
            y: f64::NEG_INFINITY,
        };
        for seg in &self.outline {
            for p in [seg.start, seg.end] {
                min.x = min.x.min(p.x);
                min.y = min.y.min(p.y);
                max.x = max.x.max(p.x);
                max.y = max.y.max(p.y);
            }
        }
        (min.x.is_finite() && max.x.is_finite()).then_some((min, max))
    }
}

fn number(node: &Sexpr) -> Option<f64> {
    match node.kind {
        SexprKind::Int(i) => Some(i as f64),
        SexprKind::F64(f) => Some(f),
        _ => node.as_atom().and_then(|s| s.parse().ok()),
    }
}

fn point_of(children: &[Sexpr], name: &str) -> Option<Point> {
    let list = find_child_list(children, name)?;
    Some(Point {
        x: number(list.get(1)?)?,
        y: number(list.get(2)?)?,
    })
}

fn scalar_of(children: &[Sexpr], name: &str) -> Option<f64> {
    find_child_list(children, name)?.get(1).and_then(number)
}

fn net_of(children: &[Sexpr]) -> Option<i64> {
    find_child_list(children, "net")?
        .get(1)
        .and_then(Sexpr::as_int)
}

fn layer_of(children: &[Sexpr]) -> Option<String> {
    find_child_list(children, "layer")?
        .get(1)
        .and_then(Sexpr::as_atom)
        .map(str::to_string)
}

fn xy_points(pts: &[Sexpr]) -> Vec<Point> {
    pts.iter()
        .skip(1)
        .filter_map(|p| {
            let fields = p.as_list()?;
            if fields.first().and_then(Sexpr::as_sym) != Some("xy") {
                return None;
            }
            Some(Point {
                x: number(fields.get(1)?)?,
                y: number(fields.get(2)?)?,
            })
        })
        .collect()
}

fn parse_segment(children: &[Sexpr]) -> Option<Track> {
    Some(Track {
        start: point_of(children, "start")?,
        end: point_of(children, "end")?,
        width: scalar_of(children, "width")?,
        layer: layer_of(children)?,
        net: net_of(children)?,
    })
}

fn parse_arc(children: &[Sexpr]) -> Option<ArcTrack> {
    Some(ArcTrack {
        start: point_of(children, "start")?,
        mid: point_of(children, "mid")?,
        end: point_of(children, "end")?,
        width: scalar_of(children, "width")?,
        layer: layer_of(children)?,
        net: net_of(children)?,
    })
}

fn parse_via(children: &[Sexpr]) -> Option<Via> {
    let kind = children
        .get(1)
        .and_then(Sexpr::as_sym)
        .filter(|s| matches!(*s, "blind" | "micro"))
        .unwrap_or("via")
        .to_string();
    let layers = find_child_list(children, "layers")
        .map(|l| {
            l.iter()
                .skip(1)
                .filter_map(|s| s.as_atom().map(str::to_string))
                .collect()
        })
        .unwrap_or_default();
    Some(Via {
        at: point_of(children, "at")?,
        size: scalar_of(children, "size").unwrap_or(0.0),
        drill: scalar_of(children, "drill").unwrap_or(0.0),
        layers,
        net: net_of(children)?,
        kind,
    })
}

fn parse_zone(children: &[Sexpr]) -> Option<Zone> {
    let net = net_of(children)?;
    let net_name = find_child_list(children, "net_name")
        .and_then(|l| l.get(1))
        .and_then(Sexpr::as_atom)
        .unwrap_or("")
        .to_string();
    // Zones use either (layer "F.Cu") or (layers "F.Cu" "B.Cu").
    let mut layers: Vec<String> = Vec::new();
    if let Some(layer) = layer_of(children) {
        layers.push(layer);
    }
    if let Some(list) = find_child_list(children, "layers") {
        layers.extend(
            list.iter()
                .skip(1)
                .filter_map(|s| s.as_atom().map(str::to_string)),
        );
    }

    let mut filled_polygons = Vec::new();
    for node in children {
        let Some(fields) = node.as_list() else {
            continue;
        };
        if fields.first().and_then(Sexpr::as_sym) != Some("filled_polygon") {
            continue;
        }
        let Some(layer) = find_child_list(fields, "layer")
            .and_then(|l| l.get(1))
            .and_then(Sexpr::as_atom)
        else {
            continue;
        };
        let Some(pts) = find_child_list(fields, "pts") else {
            continue;
        };
        filled_polygons.push(ZonePolygon {
            layer: layer.to_string(),
            points: xy_points(pts),
        });
    }

    Some(Zone {
        net,
        net_name,
        layers,
        filled_polygons,
    })
}

fn parse_footprint(children: &[Sexpr]) -> Option<Footprint> {
    let footprint_id = children
        .get(1)
        .and_then(Sexpr::as_atom)
        .unwrap_or("")
        .to_string();
    let layer = layer_of(children).unwrap_or_default();
    let at_list = find_child_list(children, "at")?;
    let at = Point {
        x: number(at_list.get(1)?)?,
        y: number(at_list.get(2)?)?,
    };
    let rotation_deg = at_list.get(3).and_then(number).unwrap_or(0.0);
    let is_back = layer.starts_with("B.");

    let mut reference = String::new();
    let mut pads = Vec::new();
    for node in children {
        let Some(fields) = node.as_list() else {
            continue;
        };
        match fields.first().and_then(Sexpr::as_sym) {
            Some("property") => {
                if fields.get(1).and_then(Sexpr::as_atom) == Some("Reference")
                    && let Some(value) = fields.get(2).and_then(Sexpr::as_atom)
                {
                    reference = value.to_string();
                }
            }
            Some("pad") => {
                if let Some(pad) = parse_pad(fields, at, rotation_deg, is_back) {
                    pads.push(pad);
                }
            }
            _ => {}
        }
    }

    // Approximate the footprint extent from pad extents around the origin.
    let mut half = (0.0f64, 0.0f64);
    for pad in &pads {
        let dx = (pad.at.x - at.x).abs() + pad.size.0 / 2.0;
        let dy = (pad.at.y - at.y).abs() + pad.size.1 / 2.0;
        half.0 = half.0.max(dx);
        half.1 = half.1.max(dy);
    }

    Some(Footprint {
        reference,
        footprint_id,
        layer,
        at,
        rotation_deg,
        pads,
        bbox_half: half,
    })
}

fn parse_pad(fields: &[Sexpr], fp_at: Point, fp_rot_deg: f64, is_back: bool) -> Option<Pad> {
    let number_str = fields.get(1).and_then(Sexpr::as_atom)?.to_string();
    let kind = fields
        .get(2)
        .and_then(Sexpr::as_sym)
        .unwrap_or("smd")
        .to_string();
    let at_list = find_child_list(fields, "at")?;
    let local = Point {
        x: number(at_list.get(1)?)?,
        y: number(at_list.get(2)?)?,
    };
    let size_list = find_child_list(fields, "size");
    let size = size_list
        .map(|s| {
            (
                s.get(1).and_then(number).unwrap_or(0.0),
                s.get(2).and_then(number).unwrap_or(0.0),
            )
        })
        .unwrap_or((0.0, 0.0));
    let drill = find_child_list(fields, "drill").and_then(|d| d.iter().skip(1).find_map(number));
    let layers = find_child_list(fields, "layers")
        .map(|l| {
            l.iter()
                .skip(1)
                .filter_map(|s| s.as_atom().map(str::to_string))
                .collect()
        })
        .unwrap_or_default();
    let (net, net_name) = match find_child_list(fields, "net") {
        Some(list) => (
            list.get(1).and_then(Sexpr::as_int),
            list.get(2).and_then(Sexpr::as_atom).map(str::to_string),
        ),
        None => (None, None),
    };

    // p_board = fp_at + R(fp_rot) * (mirror_y(p_local) if back else p_local)
    let px = local.x;
    let mut py = local.y;
    if is_back {
        py = -py;
    }
    let theta = fp_rot_deg.to_radians();
    let (s, c) = theta.sin_cos();
    let at = Point {
        x: fp_at.x + c * px - s * py,
        y: fp_at.y + s * px + c * py,
    };

    Some(Pad {
        number: number_str,
        kind,
        at,
        size,
        drill,
        layers,
        net,
        net_name,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    const MINI: &str = r#"(kicad_pcb
  (version 20241229)
  (layers
    (0 "F.Cu" signal)
    (2 "B.Cu" signal)
    (25 "Edge.Cuts" user)
  )
  (net 0 "")
  (net 1 "SIG")
  (footprint "lib:R"
    (layer "F.Cu")
    (at 10 10 90)
    (property "Reference" "R1" (at 0 0) (layer "F.SilkS"))
    (pad "1" smd rect (at -1 0) (size 1 1) (layers "F.Cu") (net 1 "SIG"))
    (pad "2" smd rect (at 1 0) (size 1 1) (layers "F.Cu") (net 1 "SIG"))
  )
  (segment (start 10 9) (end 20 9) (width 0.25) (layer "F.Cu") (net 1))
  (via (at 20 9) (size 0.6) (drill 0.3) (layers "F.Cu" "B.Cu") (net 1))
  (gr_rect (start 0 0) (end 30 30) (layer "Edge.Cuts"))
)"#;

    #[test]
    fn parses_minimal_board() {
        let model = BoardModel::parse(MINI).unwrap();
        assert_eq!(model.copper_layers, vec!["F.Cu", "B.Cu"]);
        assert_eq!(model.nets.get(&1).map(String::as_str), Some("SIG"));
        assert_eq!(model.tracks.len(), 1);
        assert_eq!(model.vias.len(), 1);
        assert_eq!(model.outline.len(), 4);
        let fp = &model.footprints[0];
        assert_eq!(fp.reference, "R1");
        // 90 deg rotation: local (-1, 0) -> board (10, 9); local (1, 0) -> (10, 11)
        assert!((fp.pads[0].at.x - 10.0).abs() < 1e-9);
        assert!((fp.pads[0].at.y - 9.0).abs() < 1e-9);
        assert!((fp.pads[1].at.y - 11.0).abs() < 1e-9);
        let bbox = model.outline_bbox().unwrap();
        assert_eq!((bbox.0.x, bbox.1.x), (0.0, 30.0));
    }
}
