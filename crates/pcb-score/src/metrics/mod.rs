//! Metric passes, grouped by category.
//!
//! Each pass consumes the shared [`ScoreContext`] and produces a
//! [`CategoryResult`]. Metrics that lack their required inputs report
//! themselves as not applicable (excluded from the score, with a note)
//! rather than scoring free points or penalties.

pub mod aesthetics;
pub mod crosstalk;
pub mod dfm;
pub mod drc;
pub mod emi;
pub mod esd;
pub mod placement;
pub mod power;
pub mod routing;
pub mod si;
pub mod thermal;

use std::collections::BTreeMap;

use serde::{Deserialize, Serialize};

use crate::board::BoardModel;
use crate::model::CategoryResult;
use crate::net_graph::NetStats;

/// Per-category weights of the composite quality score. Overridable by the
/// caller; metrics inside a category carry their own relative weights.
#[derive(Debug, Clone, Serialize, Deserialize)]
#[serde(default)]
pub struct Weights {
    pub drc: f64,
    pub routing_efficiency: f64,
    pub signal_integrity: f64,
    pub crosstalk: f64,
    pub emi: f64,
    pub power_integrity: f64,
    pub esd: f64,
    pub thermal: f64,
    pub dfm: f64,
    pub placement: f64,
    pub aesthetics: f64,
}

impl Default for Weights {
    fn default() -> Self {
        Self {
            drc: 10.0,
            routing_efficiency: 20.0,
            signal_integrity: 20.0,
            crosstalk: 12.0,
            emi: 10.0,
            power_integrity: 10.0,
            esd: 5.0,
            thermal: 4.0,
            dfm: 5.0,
            placement: 2.0,
            aesthetics: 2.0,
        }
    }
}

/// Shared inputs for all metric passes.
pub struct ScoreContext<'a> {
    pub board: &'a BoardModel,
    pub net_stats: &'a BTreeMap<i64, NetStats>,
    pub drc: Option<&'a pcb_kicad::drc::DrcReport>,
    pub netlist: Option<&'a pcb_sch::Schematic>,
    /// Declarative classification of nets, keyed by net name; present only
    /// when a netlist is available.
    pub net_classes: Option<&'a BTreeMap<String, crate::classify::NetInfo>>,
    /// Declared component roles keyed by reference designator; present only
    /// when a netlist is available.
    pub roles: Option<&'a BTreeMap<String, crate::roles::Role>>,
    pub weights: &'a Weights,
}

/// A family of metrics producing one category of the report.
pub trait ScorePass {
    fn id(&self) -> &'static str;
    fn run(&self, ctx: &ScoreContext) -> CategoryResult;
}

/// All passes, in report order.
pub fn all_passes() -> Vec<Box<dyn ScorePass>> {
    vec![
        Box::new(drc::DrcPass),
        Box::new(routing::RoutingPass),
        Box::new(si::SiPass),
        Box::new(crosstalk::CrosstalkPass),
        Box::new(emi::EmiPass),
        Box::new(power::PowerPass),
        Box::new(esd::EsdPass),
        Box::new(thermal::ThermalPass),
        Box::new(dfm::DfmPass),
        Box::new(placement::PlacementPass),
        Box::new(aesthetics::AestheticsPass),
    ]
}
