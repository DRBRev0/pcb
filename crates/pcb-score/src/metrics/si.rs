//! Signal integrity metrics. High-speed nets are selected declaratively
//! (`signal` class or impedance target); metrics degrade to N/A when the
//! required declarations, netlist or stackup data are missing.

use std::collections::BTreeMap;

use crate::board::{Point, Track};
use crate::classify::NetInfo;
use crate::impedance;
use crate::model::{CategoryResult, MetricResult, WorstEntry};
use crate::norm;
use crate::stackup::{StackupGeometry, nearest_plane, plane_layers};

use super::{ScoreContext, ScorePass};

pub struct SiPass;

/// Board net ids of nets classified high-speed, with their netlist info.
fn high_speed_nets<'a>(
    ctx: &'a ScoreContext,
    classes: &'a BTreeMap<String, NetInfo>,
) -> Vec<(i64, &'a str, &'a NetInfo)> {
    ctx.board
        .nets
        .iter()
        .filter_map(|(&id, name)| {
            classes
                .get(name)
                .filter(|info| info.is_high_speed())
                .map(|info| (id, name.as_str(), info))
        })
        .collect()
}

fn net_tracks<'a>(ctx: &'a ScoreContext, net: i64) -> Vec<&'a Track> {
    ctx.board.tracks.iter().filter(|t| t.net == net).collect()
}

fn routed_length(ctx: &ScoreContext, net: i64) -> f64 {
    ctx.net_stats
        .get(&net)
        .map(|s| s.routed_length)
        .unwrap_or(0.0)
}

/// Coupled overlap between the P and N sides of a differential pair:
/// (coupled_length, gap samples).
fn pair_coupling(p_tracks: &[&Track], n_tracks: &[&Track]) -> (f64, Vec<(f64, f64)>) {
    let mut coupled = 0.0;
    let mut samples = Vec::new();
    for p in p_tracks {
        for n in n_tracks {
            if p.layer != n.layer {
                continue;
            }
            if let Some((overlap, sep)) = crate::spatial::parallel_overlap(p, n) {
                coupled += overlap;
                samples.push((overlap, sep));
            }
        }
    }
    (coupled, samples)
}

impl ScorePass for SiPass {
    fn id(&self) -> &'static str {
        "signal_integrity"
    }

    fn run(&self, ctx: &ScoreContext) -> CategoryResult {
        let mut metrics = Vec::new();
        let weight = ctx.weights.signal_integrity;

        let Some(classes) = ctx.net_classes else {
            let note = "netlist unavailable: declarative net classification required";
            for id in [
                "impedance_compliance",
                "diffpair_skew",
                "diffpair_gap_consistency",
                "diffpair_decoupled_length",
                "stub_length_hs",
                "via_stub_proxy",
                "reference_plane_continuity",
                "reference_change_stitching",
                "length_matching_groups",
                "corner_discipline_hs",
            ] {
                metrics.push(MetricResult::not_applicable(id, 1.0, note));
            }
            return CategoryResult::new("signal_integrity", "Signal integrity", weight, metrics);
        };

        let hs_nets = high_speed_nets(ctx, classes);
        let geometry = StackupGeometry::from_board(ctx.board);
        let planes = plane_layers(ctx.board, Some(classes));

        // impedance_compliance: length-weighted |Z - Ztarget| / Ztarget over
        // single-ended impedance-target nets.
        {
            let targets: Vec<&(i64, &str, &NetInfo)> = hs_nets
                .iter()
                .filter(|(_, _, info)| info.impedance_ohms.is_some())
                .collect();
            let usable = geometry
                .as_ref()
                .filter(|g| g.mean_epsilon_r.is_some() && !planes.is_empty());
            if targets.is_empty() {
                metrics.push(MetricResult::not_applicable(
                    "impedance_compliance",
                    4.0,
                    "no single-ended impedance targets declared",
                ));
            } else if let Some(geometry) = usable {
                let er = geometry.mean_epsilon_r.unwrap();
                let mut err_weighted = 0.0;
                let mut len_sum = 0.0;
                let mut worst: Vec<WorstEntry> = Vec::new();
                for (id, name, info) in targets.iter().copied() {
                    let target = info.impedance_ohms.unwrap();
                    let mut net_err = 0.0;
                    let mut net_len = 0.0;
                    for track in net_tracks(ctx, *id) {
                        let Some((_, h)) = nearest_plane(&track.layer, &planes, geometry) else {
                            continue;
                        };
                        let t = geometry.copper_thickness(&track.layer).unwrap_or(0.035);
                        let outer = track.layer == "F.Cu" || track.layer == "B.Cu";
                        let z = if outer {
                            impedance::microstrip_z0(track.width, h, t, er)
                        } else {
                            impedance::stripline_z0(track.width, 2.0 * h + t, t, er)
                        };
                        if let Some(z) = z {
                            let err = (z - target).abs() / target;
                            net_err += err * track.length();
                            net_len += track.length();
                        }
                    }
                    if net_len > 1e-9 {
                        err_weighted += net_err;
                        len_sum += net_len;
                        worst.push(WorstEntry {
                            label: (*name).to_string(),
                            value: net_err / net_len,
                        });
                    }
                }
                if len_sum > 1e-9 {
                    let mean_err = err_weighted / len_sum;
                    metrics.push(
                        MetricResult::new(
                            "impedance_compliance",
                            mean_err,
                            "rel_err",
                            norm::target_band(mean_err, 0.0, 0.05, 0.0, 0.15),
                            4.0,
                        )
                        .with_worst(worst, true),
                    );
                } else {
                    metrics.push(MetricResult::not_applicable(
                        "impedance_compliance",
                        4.0,
                        "impedance-target nets have no routed tracks near a reference plane",
                    ));
                }
            } else {
                metrics.push(MetricResult::not_applicable(
                    "impedance_compliance",
                    4.0,
                    "stackup dielectric data or reference planes missing",
                ));
            }
        }

        // Differential pair metrics from declared DiffPair identity.
        {
            // Pairs keyed by (p_name, n_name), visiting each once via role "p".
            let mut skew_worst = Vec::new();
            let mut gap_ratio_sum = 0.0;
            let mut gap_pairs = 0usize;
            let mut decoupled_total = 0.0;
            let mut pair_count = 0usize;
            for (id, name, info) in &hs_nets {
                if info.diff_pair_role.as_deref() != Some("p") {
                    continue;
                }
                let Some(peer_name) = &info.diff_pair_peer else {
                    continue;
                };
                let Some((&peer_id, _)) = ctx
                    .board
                    .nets
                    .iter()
                    .find(|(_, n)| n.as_str() == peer_name.as_str())
                else {
                    continue;
                };
                pair_count += 1;
                let len_p = routed_length(ctx, *id);
                let len_n = routed_length(ctx, peer_id);
                if len_p > 1e-9 || len_n > 1e-9 {
                    skew_worst.push(WorstEntry {
                        label: format!("{name}/{peer_name}"),
                        value: (len_p - len_n).abs(),
                    });
                }

                let p_tracks = net_tracks(ctx, *id);
                let n_tracks = net_tracks(ctx, peer_id);
                let (coupled, samples) = pair_coupling(&p_tracks, &n_tracks);
                let route_len = len_p.min(len_n);
                if route_len > 1e-9 {
                    decoupled_total += (route_len - coupled).max(0.0);
                }
                if !samples.is_empty() {
                    // Consistency against the pair's own median gap.
                    let mut gaps: Vec<f64> = samples.iter().map(|(_, gap)| *gap).collect();
                    gaps.sort_by(|a, b| a.partial_cmp(b).unwrap_or(std::cmp::Ordering::Equal));
                    let median = gaps[gaps.len() / 2];
                    let total: f64 = samples.iter().map(|(len, _)| len).sum();
                    let consistent: f64 = samples
                        .iter()
                        .filter(|(_, gap)| (gap - median).abs() <= 0.2 * median.max(1e-6))
                        .map(|(len, _)| len)
                        .sum();
                    if total > 1e-9 {
                        gap_ratio_sum += consistent / total;
                        gap_pairs += 1;
                    }
                }
            }

            if pair_count == 0 {
                for id in [
                    "diffpair_skew",
                    "diffpair_gap_consistency",
                    "diffpair_decoupled_length",
                ] {
                    metrics.push(MetricResult::not_applicable(
                        id,
                        2.0,
                        "no differential pairs declared (DiffPair interfaces)",
                    ));
                }
            } else {
                let max_skew = skew_worst.iter().map(|w| w.value).fold(0.0f64, f64::max);
                metrics.push(
                    MetricResult::new(
                        "diffpair_skew",
                        max_skew,
                        "mm",
                        norm::decay(max_skew, 0.5),
                        3.0,
                    )
                    .with_worst(skew_worst, true),
                );
                if gap_pairs > 0 {
                    let ratio = gap_ratio_sum / gap_pairs as f64;
                    metrics.push(MetricResult::new(
                        "diffpair_gap_consistency",
                        ratio,
                        "ratio",
                        norm::ratio_clamp(ratio),
                        2.0,
                    ));
                } else {
                    metrics.push(MetricResult::not_applicable(
                        "diffpair_gap_consistency",
                        2.0,
                        "declared pairs have no coupled routing yet",
                    ));
                }
                metrics.push(MetricResult::new(
                    "diffpair_decoupled_length",
                    decoupled_total,
                    "mm",
                    norm::decay(decoupled_total, 2.0),
                    2.0,
                ));
            }
        }

        // stub_length_hs: dangling copper on high-speed nets.
        if hs_nets.is_empty() {
            metrics.push(MetricResult::not_applicable(
                "stub_length_hs",
                2.0,
                "no high-speed nets declared",
            ));
        } else {
            let mut total = 0.0;
            let mut worst = Vec::new();
            for (id, name, _) in &hs_nets {
                if let Some(stats) = ctx.net_stats.get(id)
                    && stats.stub_length > 0.0
                {
                    total += stats.stub_length;
                    worst.push(WorstEntry {
                        label: (*name).to_string(),
                        value: stats.stub_length,
                    });
                }
            }
            metrics.push(
                MetricResult::new("stub_length_hs", total, "mm", norm::decay(total, 1.0), 3.0)
                    .with_worst(worst, true),
            );
        }

        // via_stub_proxy: unused barrel depth of through vias on HS nets.
        {
            let multi_layer = ctx.board.copper_layers.len() > 2;
            let usable = geometry.as_ref().and_then(|g| g.total_thickness_mm);
            if hs_nets.is_empty() || !multi_layer {
                metrics.push(MetricResult::not_applicable(
                    "via_stub_proxy",
                    1.0,
                    "needs high-speed nets and more than two copper layers",
                ));
            } else if let Some(total_thickness) = usable {
                let geometry = geometry.as_ref().unwrap();
                let mut stub_total = 0.0;
                let mut via_count = 0usize;
                for (id, _, _) in &hs_nets {
                    let layers_used: Vec<&String> = ctx
                        .net_stats
                        .get(id)
                        .map(|s| s.layers_used.iter().collect())
                        .unwrap_or_default();
                    for via in ctx.board.vias.iter().filter(|v| v.net == *id) {
                        if via.kind != "via" {
                            continue; // blind/micro vias have no full barrel
                        }
                        via_count += 1;
                        // Depth of the deepest/shallowest used layer.
                        let z_used: Vec<f64> = layers_used
                            .iter()
                            .filter_map(|l| geometry.copper_z.get(l.as_str()).map(|(z, _)| *z))
                            .collect();
                        if z_used.is_empty() {
                            continue;
                        }
                        let deepest = z_used.iter().cloned().fold(f64::MIN, f64::max);
                        let shallowest = z_used.iter().cloned().fold(f64::MAX, f64::min);
                        let unused = shallowest + (total_thickness - deepest).max(0.0);
                        stub_total += unused.max(0.0);
                    }
                }
                if via_count == 0 {
                    metrics.push(MetricResult::not_applicable(
                        "via_stub_proxy",
                        1.0,
                        "no through vias on high-speed nets",
                    ));
                } else {
                    let mean = stub_total / via_count as f64;
                    metrics.push(MetricResult::new(
                        "via_stub_proxy",
                        mean,
                        "mm",
                        norm::decay(mean, 0.3),
                        1.0,
                    ));
                }
            } else {
                metrics.push(MetricResult::not_applicable(
                    "via_stub_proxy",
                    1.0,
                    "stackup thickness data missing",
                ));
            }
        }

        // reference_plane_continuity: fraction of HS routed length with a
        // reference plane fill on another layer directly underneath.
        {
            let reference_zones: Vec<&crate::board::ZonePolygon> = ctx
                .board
                .zones
                .iter()
                .filter(|z| {
                    classes
                        .get(ctx.board.net_name(z.net))
                        .map(|info| info.is_ground || info.is_power)
                        .unwrap_or(false)
                })
                .flat_map(|z| z.filled_polygons.iter())
                .collect();
            if hs_nets.is_empty() {
                metrics.push(MetricResult::not_applicable(
                    "reference_plane_continuity",
                    3.0,
                    "no high-speed nets declared",
                ));
            } else if reference_zones.is_empty() {
                metrics.push(MetricResult::not_applicable(
                    "reference_plane_continuity",
                    3.0,
                    "no ground/power plane fills present",
                ));
            } else {
                let mut covered = 0.0;
                let mut total = 0.0;
                let mut worst: BTreeMap<String, f64> = BTreeMap::new();
                for (id, name, _) in &hs_nets {
                    for track in net_tracks(ctx, *id) {
                        let length = track.length();
                        if length < 1e-9 {
                            continue;
                        }
                        let samples = (length / 1.0).ceil().max(1.0) as usize;
                        let mut track_covered = 0usize;
                        for k in 0..=samples {
                            let t = k as f64 / samples as f64;
                            let p = Point {
                                x: track.start.x + t * (track.end.x - track.start.x),
                                y: track.start.y + t * (track.end.y - track.start.y),
                            };
                            let has_ref = reference_zones.iter().any(|poly| {
                                poly.layer != track.layer
                                    && crate::net_graph::point_in_polygon(p, &poly.points)
                            });
                            if has_ref {
                                track_covered += 1;
                            }
                        }
                        let frac = track_covered as f64 / (samples + 1) as f64;
                        covered += frac * length;
                        total += length;
                        let uncovered = (1.0 - frac) * length;
                        if uncovered > 0.01 {
                            *worst.entry((*name).to_string()).or_default() += uncovered;
                        }
                    }
                }
                if total > 1e-9 {
                    let ratio = covered / total;
                    let worst: Vec<WorstEntry> = worst
                        .into_iter()
                        .map(|(label, value)| WorstEntry { label, value })
                        .collect();
                    metrics.push(
                        MetricResult::new(
                            "reference_plane_continuity",
                            ratio,
                            "ratio",
                            norm::ratio_clamp(ratio),
                            3.0,
                        )
                        .with_worst(worst, true),
                    );
                } else {
                    metrics.push(MetricResult::not_applicable(
                        "reference_plane_continuity",
                        3.0,
                        "high-speed nets have no routed tracks yet",
                    ));
                }
            }
        }

        // reference_change_stitching: ground stitching via within 1 mm of each
        // high-speed layer-change via.
        {
            let ground_vias: Vec<&crate::board::Via> = ctx
                .board
                .vias
                .iter()
                .filter(|v| {
                    classes
                        .get(ctx.board.net_name(v.net))
                        .map(|info| info.is_ground)
                        .unwrap_or(false)
                })
                .collect();
            let hs_vias: Vec<(&str, &crate::board::Via)> = hs_nets
                .iter()
                .flat_map(|(id, name, _)| {
                    ctx.board
                        .vias
                        .iter()
                        .filter(move |v| v.net == *id)
                        .map(move |v| (*name, v))
                })
                .collect();
            if hs_vias.is_empty() {
                metrics.push(MetricResult::not_applicable(
                    "reference_change_stitching",
                    2.0,
                    "no layer changes on high-speed nets",
                ));
            } else {
                let mut ok = 0usize;
                let mut worst = Vec::new();
                for (name, via) in &hs_vias {
                    let nearest = ground_vias
                        .iter()
                        .map(|g| g.at.dist(&via.at))
                        .fold(f64::INFINITY, f64::min);
                    if nearest <= 1.0 {
                        ok += 1;
                    } else {
                        worst.push(WorstEntry {
                            label: (*name).to_string(),
                            value: if nearest.is_finite() { nearest } else { 99.0 },
                        });
                    }
                }
                let ratio = ok as f64 / hs_vias.len() as f64;
                metrics.push(
                    MetricResult::new(
                        "reference_change_stitching",
                        ratio,
                        "ratio",
                        norm::ratio_clamp(ratio),
                        2.0,
                    )
                    .with_worst(worst, true),
                );
            }
        }

        // length_matching_groups: routed-length spread within each declared
        // `matched_group` (worst max-min skew across groups).
        {
            let mut groups: BTreeMap<&str, Vec<(&str, f64)>> = BTreeMap::new();
            for (&id, name) in &ctx.board.nets {
                if let Some(group) = classes
                    .get(name)
                    .and_then(|info| info.matched_group.as_deref())
                {
                    groups
                        .entry(group)
                        .or_default()
                        .push((name.as_str(), routed_length(ctx, id)));
                }
            }
            groups.retain(|_, nets| nets.len() >= 2);
            if groups.is_empty() {
                metrics.push(MetricResult::not_applicable(
                    "length_matching_groups",
                    2.0,
                    "no matched groups declared (io(..., matched_group=...))",
                ));
            } else {
                let mut worst_skew = 0.0f64;
                let mut worst = Vec::new();
                for (group, nets) in &groups {
                    let routed: Vec<f64> = nets
                        .iter()
                        .map(|(_, len)| *len)
                        .filter(|len| *len > 1e-9)
                        .collect();
                    if routed.len() < 2 {
                        // Group not routed yet; the connectivity gate covers it.
                        continue;
                    }
                    let max = routed.iter().cloned().fold(0.0f64, f64::max);
                    let min = routed.iter().cloned().fold(f64::INFINITY, f64::min);
                    let skew = max - min;
                    worst_skew = worst_skew.max(skew);
                    worst.push(WorstEntry {
                        label: (*group).to_string(),
                        value: skew,
                    });
                }
                if worst.is_empty() {
                    metrics.push(MetricResult::not_applicable(
                        "length_matching_groups",
                        2.0,
                        "declared matched groups have no routed nets yet",
                    ));
                } else {
                    metrics.push(
                        MetricResult::new(
                            "length_matching_groups",
                            worst_skew,
                            "mm",
                            norm::decay(worst_skew, 2.0),
                            2.0,
                        )
                        .with_worst(worst, true),
                    );
                }
            }
        }

        // corner_discipline_hs: right-angle corners on high-speed nets.
        if hs_nets.is_empty() {
            metrics.push(MetricResult::not_applicable(
                "corner_discipline_hs",
                1.0,
                "no high-speed nets declared",
            ));
        } else {
            let mut corners = 0usize;
            let mut worst = Vec::new();
            for (id, name, _) in &hs_nets {
                if let Some(stats) = ctx.net_stats.get(id)
                    && stats.right_angle_corners > 0
                {
                    corners += stats.right_angle_corners;
                    worst.push(WorstEntry {
                        label: (*name).to_string(),
                        value: stats.right_angle_corners as f64,
                    });
                }
            }
            metrics.push(
                MetricResult::new(
                    "corner_discipline_hs",
                    corners as f64,
                    "count",
                    norm::decay(corners as f64, 5.0),
                    1.0,
                )
                .with_worst(worst, true),
            );
        }

        CategoryResult::new("signal_integrity", "Signal integrity", weight, metrics)
    }
}
