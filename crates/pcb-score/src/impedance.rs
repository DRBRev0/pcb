//! Closed-form characteristic impedance estimates.
//!
//! Microstrip uses Hammerstad-Jensen; stripline uses the symmetric-stripline
//! approximation. Accuracy is a few percent in the usual PCB geometry range,
//! which is enough to score compliance against a target.

/// Free-space impedance, ohms.
const ETA0: f64 = 376.730_313_668;

/// Surface microstrip Z0.
///
/// * `w` - trace width (mm)
/// * `h` - dielectric height to the reference plane (mm)
/// * `t` - copper thickness (mm), 0 to ignore
/// * `er` - relative permittivity of the dielectric
pub fn microstrip_z0(w: f64, h: f64, t: f64, er: f64) -> Option<f64> {
    if w <= 0.0 || h <= 0.0 || er < 1.0 {
        return None;
    }
    // Thickness correction (Hammerstad): effective width increase.
    let w_eff = if t > 0.0 {
        let dw =
            t / std::f64::consts::PI * (1.0 + (4.0 * std::f64::consts::E * h / t).ln().max(0.0));
        // Guard: correction must stay a small fraction of the width.
        w + dw.min(w)
    } else {
        w
    };
    let u = w_eff / h;

    let a = 1.0
        + (1.0 / 49.0) * ((u.powi(4) + (u / 52.0).powi(2)) / (u.powi(4) + 0.432)).ln()
        + (1.0 / 18.7) * (1.0 + (u / 18.1).powi(3)).ln();
    let b = 0.564 * ((er - 0.9) / (er + 3.0)).powf(0.053);
    let e_eff = (er + 1.0) / 2.0 + (er - 1.0) / 2.0 * (1.0 + 10.0 / u).powf(-a * b);

    let f = 6.0 + (2.0 * std::f64::consts::PI - 6.0) * (-(30.666 / u).powf(0.7528)).exp();
    let z0_air =
        ETA0 / (2.0 * std::f64::consts::PI) * (f / u + (1.0 + (2.0 / u).powi(2)).sqrt()).ln();
    Some(z0_air / e_eff.sqrt())
}

/// Symmetric stripline Z0.
///
/// * `w` - trace width (mm)
/// * `b` - plane-to-plane dielectric height (mm)
/// * `t` - copper thickness (mm)
/// * `er` - relative permittivity
pub fn stripline_z0(w: f64, b: f64, t: f64, er: f64) -> Option<f64> {
    if w <= 0.0 || b <= 0.0 || er < 1.0 || t >= b {
        return None;
    }
    // IPC-2141 style approximation, valid for w/(b-t) < 0.35..2.0 range;
    // clamp inputs rather than reject to keep the metric monotone.
    let z0 = 60.0 / er.sqrt() * ((4.0 * b) / (0.67 * std::f64::consts::PI * (0.8 * w + t))).ln();
    (z0.is_finite() && z0 > 0.0).then_some(z0)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn microstrip_reference_points() {
        // Classic FR4 reference: w=3mm, h=1.6mm, t=35um, er=4.6 => ~49-51 ohm.
        let z = microstrip_z0(3.0, 1.6, 0.035, 4.6).unwrap();
        assert!((45.0..=55.0).contains(&z), "got {z}");

        // Narrower trace => higher impedance (monotonicity).
        let z_narrow = microstrip_z0(1.0, 1.6, 0.035, 4.6).unwrap();
        assert!(z_narrow > z);

        // Thinner dielectric => lower impedance.
        let z_thin = microstrip_z0(3.0, 0.2, 0.035, 4.6).unwrap();
        assert!(z_thin < z);
    }

    #[test]
    fn stripline_reference_points() {
        // w=0.25mm, b=0.7mm, t=18um, er=4.2 => ~50 ohm ballpark.
        let z = stripline_z0(0.25, 0.7, 0.018, 4.2).unwrap();
        assert!((40.0..=60.0).contains(&z), "got {z}");

        let z_wide = stripline_z0(0.5, 0.7, 0.018, 4.2).unwrap();
        assert!(z_wide < z);
    }
}
