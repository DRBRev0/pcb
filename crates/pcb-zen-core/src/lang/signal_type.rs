use allocative::Allocative;
use serde::{Deserialize, Serialize};
use starlark::values::{Freeze, Trace};

/// Declared switching/sensitivity class of a net, used by routing analysis to
/// classify crosstalk aggressors and victims without name heuristics.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize, Trace, Freeze, Allocative)]
#[serde(rename_all = "snake_case")]
pub enum SignalType {
    Static,
    Digital,
    Clock,
    HighSpeed,
    SwitchingPower,
    Analog,
    Rf,
}

pub const SIGNAL_TYPE_NAMES: &[&str] = &[
    "static",
    "digital",
    "clock",
    "high_speed",
    "switching_power",
    "analog",
    "rf",
];

impl std::str::FromStr for SignalType {
    type Err = anyhow::Error;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "static" => Ok(Self::Static),
            "digital" => Ok(Self::Digital),
            "clock" => Ok(Self::Clock),
            "high_speed" => Ok(Self::HighSpeed),
            "switching_power" => Ok(Self::SwitchingPower),
            "analog" => Ok(Self::Analog),
            "rf" => Ok(Self::Rf),
            _ => anyhow::bail!("`signal` must be one of {}", SIGNAL_TYPE_NAMES.join(", ")),
        }
    }
}

impl SignalType {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Static => "static",
            Self::Digital => "digital",
            Self::Clock => "clock",
            Self::HighSpeed => "high_speed",
            Self::SwitchingPower => "switching_power",
            Self::Analog => "analog",
            Self::Rf => "rf",
        }
    }

    pub fn parse_optional(signal: Option<&str>) -> anyhow::Result<Option<Self>> {
        signal.map(str::parse).transpose()
    }
}

impl std::fmt::Display for SignalType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str((*self).as_str())
    }
}
