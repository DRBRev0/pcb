//! Stackup geometry helpers: layer z-positions, dielectric spans and
//! reference plane discovery (declarative: a plane is a copper layer carrying
//! a filled zone of a `Ground`/`Power`-kind net).

use std::collections::{BTreeMap, BTreeSet};

use crate::board::BoardModel;
use crate::classify::NetInfo;

#[derive(Debug, Clone)]
pub struct StackupGeometry {
    /// Copper layer name -> (z_top_mm, thickness_mm), z measured from the
    /// board top going down.
    pub copper_z: BTreeMap<String, (f64, f64)>,
    /// Mean relative permittivity of the dielectric stack, if known.
    pub mean_epsilon_r: Option<f64>,
    /// Total board thickness.
    pub total_thickness_mm: Option<f64>,
}

impl StackupGeometry {
    pub fn from_board(board: &BoardModel) -> Option<Self> {
        if board.stackup.is_empty() {
            return None;
        }
        let mut copper_z = BTreeMap::new();
        let mut z = 0.0f64;
        let mut er_values = Vec::new();
        for layer in &board.stackup {
            let thickness = layer.thickness_mm.unwrap_or(0.0);
            if layer.kind == "copper" {
                copper_z.insert(layer.name.clone(), (z, thickness));
            } else if let Some(er) = layer.epsilon_r {
                er_values.push(er);
            }
            z += thickness;
        }
        if copper_z.is_empty() {
            return None;
        }
        let mean_epsilon_r =
            (!er_values.is_empty()).then(|| er_values.iter().sum::<f64>() / er_values.len() as f64);
        Some(Self {
            copper_z,
            mean_epsilon_r,
            total_thickness_mm: (z > 0.0).then_some(z),
        })
    }

    /// Vertical dielectric distance between two copper layers (edge to edge).
    pub fn dielectric_span(&self, a: &str, b: &str) -> Option<f64> {
        let (za, ta) = self.copper_z.get(a)?;
        let (zb, tb) = self.copper_z.get(b)?;
        let (top, bottom) = if za < zb {
            (za + ta, *zb)
        } else {
            (zb + tb, *za)
        };
        let span = bottom - top;
        (span > 0.0).then_some(span)
    }

    pub fn copper_thickness(&self, layer: &str) -> Option<f64> {
        self.copper_z
            .get(layer)
            .map(|(_, t)| *t)
            .filter(|t| *t > 0.0)
    }
}

/// Copper layers that act as reference planes: they carry at least one filled
/// zone belonging to a Ground/Power net (declared kinds only).
pub fn plane_layers(
    board: &BoardModel,
    net_classes: Option<&BTreeMap<String, NetInfo>>,
) -> BTreeSet<String> {
    let mut planes = BTreeSet::new();
    for zone in &board.zones {
        if zone.filled_polygons.is_empty() {
            continue;
        }
        let net_name = board.net_name(zone.net);
        let is_reference = match net_classes {
            Some(classes) => classes
                .get(net_name)
                .map(|info| info.is_ground || info.is_power)
                .unwrap_or(false),
            // Without a netlist we cannot classify; report no planes rather
            // than guessing from names.
            None => false,
        };
        if is_reference {
            for poly in &zone.filled_polygons {
                planes.insert(poly.layer.clone());
            }
        }
    }
    planes
}

/// For a signal layer, the nearest reference plane (by stack order) and its
/// dielectric distance.
pub fn nearest_plane<'a>(
    layer: &str,
    planes: &'a BTreeSet<String>,
    geometry: &StackupGeometry,
) -> Option<(&'a String, f64)> {
    planes
        .iter()
        .filter(|plane| plane.as_str() != layer)
        .filter_map(|plane| geometry.dielectric_span(layer, plane).map(|d| (plane, d)))
        .min_by(|a, b| a.1.partial_cmp(&b.1).unwrap_or(std::cmp::Ordering::Equal))
}
