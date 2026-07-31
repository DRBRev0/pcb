//! Normalization primitives mapping raw metric values into [0, 1].
//!
//! Every function here is monotone in its input so that scores stay
//! comparable across iterations of the same board.

/// Exponential decay: 1.0 at x = 0, ~0.37 at x = tau. For "less is better"
/// unbounded counts/lengths.
pub fn decay(x: f64, tau: f64) -> f64 {
    if x <= 0.0 {
        return 1.0;
    }
    (-x / tau).exp()
}

/// Clamp a ratio into [0, 1].
pub fn ratio_clamp(x: f64) -> f64 {
    x.clamp(0.0, 1.0)
}

/// Trapezoid band: 1.0 inside [lo, hi], falling linearly to 0.0 at
/// lo - soft_lo / hi + soft_hi. Pass 0.0 softness for a hard edge.
pub fn target_band(x: f64, lo: f64, hi: f64, soft_lo: f64, soft_hi: f64) -> f64 {
    if x >= lo && x <= hi {
        1.0
    } else if x < lo {
        if soft_lo <= 0.0 {
            0.0
        } else {
            ((x - (lo - soft_lo)) / soft_lo).clamp(0.0, 1.0)
        }
    } else if soft_hi <= 0.0 {
        0.0
    } else {
        (((hi + soft_hi) - x) / soft_hi).clamp(0.0, 1.0)
    }
}

/// Harmonic falloff on counts: 1.0 at 0, 0.5 at n0.
pub fn inv_count(n: f64, n0: f64) -> f64 {
    if n <= 0.0 {
        return 1.0;
    }
    1.0 / (1.0 + n / n0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn decay_monotone() {
        assert_eq!(decay(0.0, 5.0), 1.0);
        assert!(decay(1.0, 5.0) > decay(2.0, 5.0));
        assert!((decay(5.0, 5.0) - (-1.0f64).exp()).abs() < 1e-12);
    }

    #[test]
    fn target_band_shape() {
        assert_eq!(target_band(1.1, 1.0, 1.25, 0.0, 1.25), 1.0);
        assert_eq!(target_band(2.5, 1.0, 1.25, 0.0, 1.25), 0.0);
        let mid = target_band(1.875, 1.0, 1.25, 0.0, 1.25);
        assert!((mid - 0.5).abs() < 1e-9);
        assert_eq!(target_band(0.5, 1.0, 1.25, 0.0, 1.25), 0.0);
    }

    #[test]
    fn inv_count_shape() {
        assert_eq!(inv_count(0.0, 2.0), 1.0);
        assert!((inv_count(2.0, 2.0) - 0.5).abs() < 1e-12);
    }
}
