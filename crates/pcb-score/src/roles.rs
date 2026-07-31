//! Component role identification from the typed netlist.
//!
//! Roles come exclusively from the declared `type` attribute of components
//! (stdlib generics set it: "tvs", "connector", "capacitor", ...). No
//! refdes/MPN/footprint-name heuristics: components without a declared type
//! simply have no role, and role-dependent metrics report N/A notes.

use std::collections::BTreeMap;

use pcb_sch::{InstanceKind, Schematic};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Role {
    Tvs,
    Connector,
    Capacitor,
    Resistor,
    Inductor,
    FerriteBead,
    Led,
    Crystal,
    Other,
}

impl Role {
    fn parse(s: &str) -> Role {
        match s {
            "tvs" => Role::Tvs,
            "connector" => Role::Connector,
            "capacitor" => Role::Capacitor,
            "resistor" => Role::Resistor,
            "inductor" => Role::Inductor,
            "ferrite_bead" => Role::FerriteBead,
            "led" => Role::Led,
            "crystal" => Role::Crystal,
            _ => Role::Other,
        }
    }
}

/// Map reference designator -> declared role, for components that declare a
/// `type` attribute in the netlist.
pub fn component_roles(schematic: &Schematic) -> BTreeMap<String, Role> {
    let mut roles = BTreeMap::new();
    for instance in schematic.instances.values() {
        if instance.kind != InstanceKind::Component {
            continue;
        }
        let Some(refdes) = &instance.reference_designator else {
            continue;
        };
        let Some(type_attr) = instance.attributes.get("type").and_then(|v| v.string()) else {
            continue;
        };
        roles.insert(refdes.clone(), Role::parse(type_attr));
    }
    roles
}
