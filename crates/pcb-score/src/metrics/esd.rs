//! ESD protection metrics. Roles are fully declarative: TVS components are
//! `type="tvs"` (stdlib `Tvs.zen` generic), connectors `type="connector"`.

use crate::board::Footprint;
use crate::model::{CategoryResult, MetricResult, WorstEntry};
use crate::net_graph::point_in_polygon;
use crate::norm;
use crate::roles::Role;

use super::{ScoreContext, ScorePass};

pub struct EsdPass;

const IDS: [&str; 5] = [
    "tvs_proximity",
    "protection_topology",
    "esd_return_path",
    "unprotected_connector_lines",
    "guard_structures",
];

impl ScorePass for EsdPass {
    fn id(&self) -> &'static str {
        "esd"
    }

    fn run(&self, ctx: &ScoreContext) -> CategoryResult {
        let mut metrics = Vec::new();
        let weight = ctx.weights.esd;

        let (Some(classes), Some(roles)) = (ctx.net_classes, ctx.roles) else {
            for id in IDS {
                metrics.push(MetricResult::not_applicable(
                    id,
                    1.0,
                    "netlist unavailable: declarative roles required",
                ));
            }
            return CategoryResult::new("esd", "ESD protection", weight, metrics);
        };

        let tvs: Vec<&Footprint> = ctx
            .board
            .footprints
            .iter()
            .filter(|f| roles.get(&f.reference) == Some(&Role::Tvs))
            .collect();
        let connectors: Vec<&Footprint> = ctx
            .board
            .footprints
            .iter()
            .filter(|f| roles.get(&f.reference) == Some(&Role::Connector))
            .collect();

        if tvs.is_empty() {
            for id in IDS {
                metrics.push(MetricResult::not_applicable(
                    id,
                    1.0,
                    "no TVS components declared (type=\"tvs\")",
                ));
            }
            return CategoryResult::new("esd", "ESD protection", weight, metrics);
        }
        if connectors.is_empty() {
            for id in IDS {
                metrics.push(MetricResult::not_applicable(
                    id,
                    1.0,
                    "no connectors declared (type=\"connector\")",
                ));
            }
            return CategoryResult::new("esd", "ESD protection", weight, metrics);
        }

        // Protected lines: nets shared by a connector pad and a TVS pad.
        struct ProtectedLine {
            net_name: String,
            connector_pad: crate::board::Point,
            tvs_pad: crate::board::Point,
            other_pads: Vec<crate::board::Point>,
        }
        let mut lines: Vec<ProtectedLine> = Vec::new();
        for connector in &connectors {
            for pad in &connector.pads {
                let Some(net_name) = pad.net_name.as_deref() else {
                    continue;
                };
                let Some(info) = classes.get(net_name) else {
                    continue;
                };
                // Ground pads are the return path, not a protected line;
                // power entries stay in scope (they get TVS protection too).
                if info.is_ground {
                    continue;
                }
                for tvs_fp in &tvs {
                    let Some(tvs_pad) = tvs_fp
                        .pads
                        .iter()
                        .find(|p| p.net_name.as_deref() == Some(net_name))
                    else {
                        continue;
                    };
                    // Pads of any third component on the same net (the
                    // protected side).
                    let other_pads: Vec<crate::board::Point> = ctx
                        .board
                        .footprints
                        .iter()
                        .filter(|f| {
                            f.reference != tvs_fp.reference && f.reference != connector.reference
                        })
                        .flat_map(|f| f.pads.iter())
                        .filter(|p| p.net_name.as_deref() == Some(net_name))
                        .map(|p| p.at)
                        .collect();
                    lines.push(ProtectedLine {
                        net_name: net_name.to_string(),
                        connector_pad: pad.at,
                        tvs_pad: tvs_pad.at,
                        other_pads,
                    });
                }
            }
        }

        // tvs_proximity: connector pad to TVS pad distance.
        if lines.is_empty() {
            metrics.push(MetricResult::not_applicable(
                "tvs_proximity",
                2.0,
                "no nets shared by a connector pad and a TVS pad",
            ));
        } else {
            let mut sum = 0.0;
            let mut worst = Vec::new();
            for line in &lines {
                let d = line.connector_pad.dist(&line.tvs_pad);
                sum += d;
                worst.push(WorstEntry {
                    label: line.net_name.clone(),
                    value: d,
                });
            }
            let mean = sum / lines.len() as f64;
            metrics.push(
                MetricResult::new("tvs_proximity", mean, "mm", norm::decay(mean, 5.0), 2.0)
                    .with_worst(worst, true),
            );
        }

        // protection_topology: the TVS must sit closer to the connector than
        // the components it protects.
        {
            let judged: Vec<(&ProtectedLine, bool)> = lines
                .iter()
                .filter(|line| !line.other_pads.is_empty())
                .map(|line| {
                    let tvs_d = line.connector_pad.dist(&line.tvs_pad);
                    let protected_ok = line
                        .other_pads
                        .iter()
                        .all(|p| line.connector_pad.dist(p) >= tvs_d);
                    (line, protected_ok)
                })
                .collect();
            if judged.is_empty() {
                metrics.push(MetricResult::not_applicable(
                    "protection_topology",
                    2.0,
                    "protected nets reach no third component",
                ));
            } else {
                let ok = judged.iter().filter(|(_, ok)| *ok).count();
                let ratio = ok as f64 / judged.len() as f64;
                let worst: Vec<WorstEntry> = judged
                    .iter()
                    .filter(|(_, ok)| !*ok)
                    .map(|(line, _)| WorstEntry {
                        label: line.net_name.clone(),
                        value: line.connector_pad.dist(&line.tvs_pad),
                    })
                    .collect();
                metrics.push(
                    MetricResult::new(
                        "protection_topology",
                        ratio,
                        "ratio",
                        norm::ratio_clamp(ratio),
                        2.0,
                    )
                    .with_worst(worst, true),
                );
            }
        }

        // esd_return_path: each TVS ground pad needs a low-inductance path to
        // the ground plane (via within 1 mm or pad inside a ground fill).
        {
            let mut checked = 0usize;
            let mut ok = 0usize;
            let mut worst = Vec::new();
            for tvs_fp in &tvs {
                for pad in &tvs_fp.pads {
                    let Some(info) = pad.net_name.as_deref().and_then(|n| classes.get(n)) else {
                        continue;
                    };
                    if !info.is_ground {
                        continue;
                    }
                    checked += 1;
                    let Some(net_id) = pad.net else { continue };
                    let in_zone = ctx
                        .board
                        .zones
                        .iter()
                        .filter(|z| z.net == net_id)
                        .flat_map(|z| z.filled_polygons.iter())
                        .any(|poly| point_in_polygon(pad.at, &poly.points));
                    let nearest_via = ctx
                        .board
                        .vias
                        .iter()
                        .filter(|v| v.net == net_id)
                        .map(|v| v.at.dist(&pad.at))
                        .fold(f64::INFINITY, f64::min);
                    if in_zone || nearest_via <= 1.0 {
                        ok += 1;
                    } else {
                        worst.push(WorstEntry {
                            label: tvs_fp.reference.clone(),
                            value: if nearest_via.is_finite() {
                                nearest_via
                            } else {
                                99.0
                            },
                        });
                    }
                }
            }
            if checked == 0 {
                metrics.push(MetricResult::not_applicable(
                    "esd_return_path",
                    2.0,
                    "TVS components have no ground pads",
                ));
            } else {
                let ratio = ok as f64 / checked as f64;
                metrics.push(
                    MetricResult::new(
                        "esd_return_path",
                        ratio,
                        "ratio",
                        norm::ratio_clamp(ratio),
                        2.0,
                    )
                    .with_worst(worst, true),
                );
            }
        }

        // unprotected_connector_lines: signal pads on connectors without any
        // TVS on their net. Counts only because TVS exist in the design
        // (protection intent is visible).
        {
            let mut signal_pads = 0usize;
            let mut protected = 0usize;
            let mut worst = Vec::new();
            for connector in &connectors {
                for pad in &connector.pads {
                    let Some(net_name) = pad.net_name.as_deref() else {
                        continue;
                    };
                    let Some(info) = classes.get(net_name) else {
                        continue;
                    };
                    if info.is_ground || info.is_power {
                        continue;
                    }
                    signal_pads += 1;
                    let has_tvs = tvs.iter().any(|f| {
                        f.pads
                            .iter()
                            .any(|p| p.net_name.as_deref() == Some(net_name))
                    });
                    if has_tvs {
                        protected += 1;
                    } else {
                        worst.push(WorstEntry {
                            label: net_name.to_string(),
                            value: 0.0,
                        });
                    }
                }
            }
            if signal_pads == 0 {
                metrics.push(MetricResult::not_applicable(
                    "unprotected_connector_lines",
                    1.0,
                    "connectors expose no signal pads",
                ));
            } else {
                let ratio = protected as f64 / signal_pads as f64;
                metrics.push(
                    MetricResult::new(
                        "unprotected_connector_lines",
                        ratio,
                        "ratio",
                        norm::ratio_clamp(ratio),
                        1.0,
                    )
                    .with_worst(worst, false),
                );
            }
        }

        // guard_structures: ground fill presence around each connector.
        {
            let ground_polys: Vec<&crate::board::ZonePolygon> = ctx
                .board
                .zones
                .iter()
                .filter(|z| {
                    classes
                        .get(ctx.board.net_name(z.net))
                        .map(|info| info.is_ground)
                        .unwrap_or(false)
                })
                .flat_map(|z| z.filled_polygons.iter())
                .collect();
            if ground_polys.is_empty() {
                metrics.push(MetricResult::not_applicable(
                    "guard_structures",
                    1.0,
                    "no ground fills present",
                ));
            } else {
                let mut ok = 0usize;
                for connector in &connectors {
                    let r = connector.bbox_half.0.max(connector.bbox_half.1) + 1.0;
                    // Sample 8 points on a ring around the connector.
                    let guarded = (0..8).filter(|k| {
                        let theta = std::f64::consts::TAU * (*k as f64) / 8.0;
                        let p = crate::board::Point {
                            x: connector.at.x + r * theta.cos(),
                            y: connector.at.y + r * theta.sin(),
                        };
                        ground_polys
                            .iter()
                            .any(|poly| point_in_polygon(p, &poly.points))
                    });
                    if guarded.count() >= 4 {
                        ok += 1;
                    }
                }
                let ratio = ok as f64 / connectors.len() as f64;
                metrics.push(MetricResult::new(
                    "guard_structures",
                    ratio,
                    "ratio",
                    norm::ratio_clamp(ratio),
                    1.0,
                ));
            }
        }

        CategoryResult::new("esd", "ESD protection", weight, metrics)
    }
}
