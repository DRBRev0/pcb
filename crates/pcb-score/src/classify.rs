//! Declarative net classification from the Zener netlist.
//!
//! Classification uses ONLY declared data — net kinds (`Power`/`Ground`),
//! `signal` classes, impedance targets, per-io current declarations — never
//! net-name heuristics. Nets without declarations stay unclassified and the
//! metrics that need a class treat them as not applicable.

use std::collections::BTreeMap;

use pcb_sch::{AttributeValue, Schematic};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SignalClass {
    Static,
    Digital,
    Clock,
    HighSpeed,
    SwitchingPower,
    Analog,
    Rf,
}

impl SignalClass {
    pub fn parse(s: &str) -> Option<Self> {
        match s {
            "static" => Some(Self::Static),
            "digital" => Some(Self::Digital),
            "clock" => Some(Self::Clock),
            "high_speed" => Some(Self::HighSpeed),
            "switching_power" => Some(Self::SwitchingPower),
            "analog" => Some(Self::Analog),
            "rf" => Some(Self::Rf),
            _ => None,
        }
    }

    /// Nets that inject noise into neighbours.
    pub fn is_aggressor(self) -> bool {
        matches!(
            self,
            Self::Digital | Self::Clock | Self::HighSpeed | Self::SwitchingPower
        )
    }

    /// Nets that are sensitive to injected noise.
    pub fn is_victim(self) -> bool {
        matches!(
            self,
            Self::Analog | Self::Rf | Self::HighSpeed | Self::Clock
        )
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ClassSource {
    /// `signal` declared on the net or its driving io().
    Declared,
    /// Implied by the `Power`/`Ground` net kind.
    ImpliedPowerGround,
    /// Implied by a declared impedance target.
    ImpliedImpedance,
}

#[derive(Debug, Clone)]
pub struct PortCurrent {
    pub port: String,
    pub is_sink: bool,
    pub amps: f64,
}

#[derive(Debug, Clone, Default)]
pub struct NetInfo {
    pub class: Option<SignalClass>,
    pub class_source: Option<ClassSource>,
    pub is_power: bool,
    pub is_ground: bool,
    pub impedance_ohms: Option<f64>,
    pub differential_impedance_ohms: Option<f64>,
    /// Peer net name for DiffPair members, with this net's role ("p"/"n").
    pub diff_pair_peer: Option<String>,
    pub diff_pair_role: Option<String>,
    pub sink_total_amps: Option<f64>,
    pub source_total_amps: Option<f64>,
    pub current_ports: Vec<PortCurrent>,
    /// Length-matching group this net belongs to, if declared.
    pub matched_group: Option<String>,
}

impl NetInfo {
    /// High-speed for SI purposes: declared clock/high_speed/rf, or any
    /// impedance-controlled net.
    pub fn is_high_speed(&self) -> bool {
        matches!(
            self.class,
            Some(SignalClass::Clock | SignalClass::HighSpeed | SignalClass::Rf)
        ) || self.impedance_ohms.is_some()
            || self.differential_impedance_ohms.is_some()
    }
}

fn physical_ohms(value: &AttributeValue) -> Option<f64> {
    use rust_decimal::prelude::ToPrimitive;
    let physical = value.physical()?;
    (physical.unit == pcb_sch::PhysicalUnit::Ohms.into())
        .then(|| physical.nominal.to_f64())
        .flatten()
}

fn physical_amps(value: &AttributeValue) -> Option<f64> {
    use rust_decimal::prelude::ToPrimitive;
    let physical = value.physical()?;
    (physical.unit == pcb_sch::PhysicalUnit::Amperes.into())
        .then(|| physical.nominal.to_f64())
        .flatten()
}

/// Build per-net classification, keyed by net name (matching `.kicad_pcb`
/// net names, which the layout generator derives from the schematic).
pub fn classify_nets(schematic: &Schematic) -> BTreeMap<String, NetInfo> {
    // Net id -> name, to resolve diff pair peers.
    let id_to_name: BTreeMap<u64, &str> = schematic
        .nets
        .values()
        .map(|net| (net.id, net.name.as_str()))
        .collect();

    let mut result = BTreeMap::new();
    for (name, net) in &schematic.nets {
        let mut info = NetInfo {
            is_power: net.kind == "Power",
            is_ground: net.kind == "Ground",
            ..Default::default()
        };

        for (key, value) in &net.properties {
            match key.as_str() {
                "signal" => {
                    if let Some(s) = value.string()
                        && let Some(class) = SignalClass::parse(s)
                    {
                        info.class = Some(class);
                        info.class_source = Some(ClassSource::Declared);
                    }
                }
                "impedance" => info.impedance_ohms = physical_ohms(value),
                "differential_impedance" => info.differential_impedance_ohms = physical_ohms(value),
                "diff_pair_peer" => {
                    if let AttributeValue::Number(id) = value {
                        info.diff_pair_peer =
                            id_to_name.get(&(*id as u64)).map(|peer| peer.to_string());
                    }
                }
                "diff_pair_role" => info.diff_pair_role = value.string().map(str::to_string),
                "matched_group" => info.matched_group = value.string().map(str::to_string),
                "current_sink_total" => info.sink_total_amps = physical_amps(value),
                "current_source_total" => info.source_total_amps = physical_amps(value),
                "current_ports" => {
                    if let AttributeValue::Json(serde_json::Value::Array(entries)) = value {
                        for entry in entries {
                            let (Some(port), Some(role), Some(amps)) = (
                                entry.get("port").and_then(|v| v.as_str()),
                                entry.get("role").and_then(|v| v.as_str()),
                                entry.get("amps").and_then(|v| v.as_f64()),
                            ) else {
                                continue;
                            };
                            info.current_ports.push(PortCurrent {
                                port: port.to_string(),
                                is_sink: role == "sink",
                                amps,
                            });
                        }
                    }
                }
                _ => {}
            }
        }

        // Implied classes, weakest last: Power/Ground are static; an
        // impedance target implies at least high_speed.
        if info.class.is_none() {
            if info.is_power || info.is_ground {
                info.class = Some(SignalClass::Static);
                info.class_source = Some(ClassSource::ImpliedPowerGround);
            } else if info.impedance_ohms.is_some() || info.differential_impedance_ohms.is_some() {
                info.class = Some(SignalClass::HighSpeed);
                info.class_source = Some(ClassSource::ImpliedImpedance);
            }
        }

        result.insert(name.clone(), info);
    }
    result
}
