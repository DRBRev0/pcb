//! Uniform-grid spatial index over track segments, used to prune the
//! quadratic pair scans in crosstalk/coupling metrics.

use std::collections::HashMap;

use crate::board::{BoardModel, Point, Track};

const CELL_MM: f64 = 2.0;

/// Index of track indices (into `BoardModel::tracks`) bucketed by grid cell,
/// per layer.
pub struct SegmentIndex<'a> {
    board: &'a BoardModel,
    cells: HashMap<(i64, i64, u16), Vec<usize>>,
    layer_ids: HashMap<&'a str, u16>,
}

fn cell_range(a: f64, b: f64, pad: f64) -> (i64, i64) {
    let lo = ((a.min(b) - pad) / CELL_MM).floor() as i64;
    let hi = ((a.max(b) + pad) / CELL_MM).floor() as i64;
    (lo, hi)
}

impl<'a> SegmentIndex<'a> {
    pub fn build(board: &'a BoardModel) -> Self {
        let mut layer_ids = HashMap::new();
        for (i, layer) in board.copper_layers.iter().enumerate() {
            layer_ids.insert(layer.as_str(), i as u16);
        }
        let mut cells: HashMap<(i64, i64, u16), Vec<usize>> = HashMap::new();
        for (idx, track) in board.tracks.iter().enumerate() {
            let Some(&layer) = layer_ids.get(track.layer.as_str()) else {
                continue;
            };
            let (x0, x1) = cell_range(track.start.x, track.end.x, track.width);
            let (y0, y1) = cell_range(track.start.y, track.end.y, track.width);
            for cx in x0..=x1 {
                for cy in y0..=y1 {
                    cells.entry((cx, cy, layer)).or_default().push(idx);
                }
            }
        }
        Self {
            board,
            cells,
            layer_ids,
        }
    }

    /// Candidate neighbour segments of `track` on `layer` within `radius`.
    /// Deduplicated, sorted, excluding `idx` itself.
    pub fn neighbours(&self, idx: usize, layer: &str, radius: f64) -> Vec<usize> {
        let track = &self.board.tracks[idx];
        let Some(&layer_id) = self.layer_ids.get(layer) else {
            return Vec::new();
        };
        let (x0, x1) = cell_range(track.start.x, track.end.x, radius + track.width);
        let (y0, y1) = cell_range(track.start.y, track.end.y, radius + track.width);
        let mut out = Vec::new();
        for cx in x0..=x1 {
            for cy in y0..=y1 {
                if let Some(bucket) = self.cells.get(&(cx, cy, layer_id)) {
                    out.extend(bucket.iter().copied().filter(|&j| j != idx));
                }
            }
        }
        out.sort_unstable();
        out.dedup();
        out
    }
}

/// Parallel overlap between two segments: the length over which their
/// projections overlap, and the mean separation over that overlap. Returns
/// `None` when the segments are not roughly parallel (>15 deg) or do not
/// overlap.
pub fn parallel_overlap(a: &Track, b: &Track) -> Option<(f64, f64)> {
    let da = Point {
        x: a.end.x - a.start.x,
        y: a.end.y - a.start.y,
    };
    let db = Point {
        x: b.end.x - b.start.x,
        y: b.end.y - b.start.y,
    };
    let (la, lb) = (da.x.hypot(da.y), db.x.hypot(db.y));
    if la < 1e-9 || lb < 1e-9 {
        return None;
    }
    let cos = ((da.x * db.x + da.y * db.y) / (la * lb)).abs();
    if cos < (15.0f64).to_radians().cos() {
        return None;
    }

    // Project b's endpoints onto a's axis.
    let (ux, uy) = (da.x / la, da.y / la);
    let proj = |p: Point| (p.x - a.start.x) * ux + (p.y - a.start.y) * uy;
    let (tb0, tb1) = (proj(b.start), proj(b.end));
    let (bmin, bmax) = (tb0.min(tb1), tb0.max(tb1));
    let lo = bmin.max(0.0);
    let hi = bmax.min(la);
    let overlap = hi - lo;
    if overlap <= 1e-6 {
        return None;
    }

    // Perpendicular distance from b's midpoint (over the overlap) to a's axis.
    let mid_t = (lo + hi) / 2.0;
    // Point on b whose projection is mid_t (linear interpolation on b).
    let denom = tb1 - tb0;
    let s = if denom.abs() < 1e-9 {
        0.5
    } else {
        ((mid_t - tb0) / denom).clamp(0.0, 1.0)
    };
    let bp = Point {
        x: b.start.x + s * (b.end.x - b.start.x),
        y: b.start.y + s * (b.end.y - b.start.y),
    };
    let perp = ((bp.x - a.start.x) * -uy + (bp.y - a.start.y) * ux).abs();
    Some((overlap, perp))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn track(x0: f64, y0: f64, x1: f64, y1: f64) -> Track {
        Track {
            start: Point { x: x0, y: y0 },
            end: Point { x: x1, y: y1 },
            width: 0.2,
            layer: "F.Cu".to_string(),
            net: 1,
        }
    }

    #[test]
    fn overlap_of_parallel_segments() {
        let a = track(0.0, 0.0, 10.0, 0.0);
        let b = track(2.0, 0.5, 8.0, 0.5);
        let (overlap, sep) = parallel_overlap(&a, &b).unwrap();
        assert!((overlap - 6.0).abs() < 1e-9);
        assert!((sep - 0.5).abs() < 1e-9);
    }

    #[test]
    fn perpendicular_segments_do_not_couple() {
        let a = track(0.0, 0.0, 10.0, 0.0);
        let b = track(5.0, -3.0, 5.0, 3.0);
        assert!(parallel_overlap(&a, &b).is_none());
    }
}
