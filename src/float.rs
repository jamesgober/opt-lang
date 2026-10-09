//! Exact IEEE 754 helpers that `core` does not provide on the MSRV.
//!
//! `core` has the correctly rounded `+ - * / %` and `as` conversions, but not
//! `trunc`, `floor`, `ceil`, `round`, `round_ties_even`, or `sqrt` (those live in
//! `std` on Rust 1.85). The constant folder must give bit-for-bit the result the
//! reference interpreter gives (which uses `std`), with or without `std`, so these
//! are written once here from the bit representation: rounding by clearing
//! fraction bits, and the square root by an exact integer square root of the
//! significand. Every function is checked against `std` in the unit tests.
//!
//! None of these is called with a NaN by the folder (a NaN operand or result is
//! never folded), but each is still total: a NaN input comes back unchanged.

/// The fields of one IEEE binary format, so `f32` and `f64` share one
/// implementation.
pub(crate) trait Ieee: Copy {
    /// Significand bits stored (52 or 23).
    const FRAC: u32;
    /// Exponent bias (1023 or 127).
    const BIAS: i32;
    /// The all-ones exponent field (2047 or 255).
    const EXP_MAX: u64;
    fn bits(self) -> u64;
    fn from_raw(bits: u64) -> Self;
}

impl Ieee for f64 {
    const FRAC: u32 = 52;
    const BIAS: i32 = 1023;
    const EXP_MAX: u64 = 0x7ff;
    fn bits(self) -> u64 {
        self.to_bits()
    }
    fn from_raw(bits: u64) -> Self {
        f64::from_bits(bits)
    }
}

impl Ieee for f32 {
    const FRAC: u32 = 23;
    const BIAS: i32 = 127;
    const EXP_MAX: u64 = 0xff;
    fn bits(self) -> u64 {
        u64::from(self.to_bits())
    }
    fn from_raw(bits: u64) -> Self {
        f32::from_bits(bits as u32)
    }
}

const fn sign_bit<F: Ieee>() -> u64 {
    1u64 << (F::FRAC + exp_width::<F>())
}

const fn exp_width<F: Ieee>() -> u32 {
    if F::FRAC == 52 { 11 } else { 8 }
}

/// The unbiased exponent field of `bits`. Zero and subnormals give `-BIAS` (they
/// are below 1 in magnitude); infinities and NaNs give `BIAS + 1`.
fn exponent<F: Ieee>(bits: u64) -> i32 {
    ((bits >> F::FRAC) & F::EXP_MAX) as i32 - F::BIAS
}

/// Rounds toward zero, keeping the sign (so `trunc(-0.5)` is `-0.0`).
pub(crate) fn trunc<F: Ieee>(x: F) -> F {
    let bits = x.bits();
    let e = exponent::<F>(bits);
    if e >= F::FRAC as i32 {
        // Already integral, or infinite, or NaN.
        return x;
    }
    if e < 0 {
        return F::from_raw(bits & sign_bit::<F>());
    }
    let mask = (1u64 << (F::FRAC as i32 - e)) - 1;
    F::from_raw(bits & !mask)
}

macro_rules! rounding {
    ($t:ty, $floor:ident, $ceil:ident, $round:ident, $even:ident) => {
        /// Rounds toward negative infinity.
        pub(crate) fn $floor(x: $t) -> $t {
            let t = trunc(x);
            // `x - t` is exact, and `t - 1` is exact below 2^FRAC (where any
            // value with a fraction lives).
            if x < t { t - 1.0 } else { t }
        }

        /// Rounds toward positive infinity.
        pub(crate) fn $ceil(x: $t) -> $t {
            let t = trunc(x);
            if x > t { t + 1.0 } else { t }
        }

        /// Rounds to nearest, ties away from zero.
        pub(crate) fn $round(x: $t) -> $t {
            let t = trunc(x);
            let d = x - t;
            if d >= 0.5 {
                t + 1.0
            } else if d <= -0.5 {
                t - 1.0
            } else {
                t
            }
        }

        /// Rounds to nearest, ties to even.
        pub(crate) fn $even(x: $t) -> $t {
            let t = trunc(x);
            let d = x - t;
            let away = if !(-0.5..=0.5).contains(&d) {
                true
            } else if d == 0.5 || d == -0.5 {
                // `t` is an integer below 2^FRAC in magnitude: the cast is exact.
                (t as i64) & 1 == 1
            } else {
                false
            };
            if !away {
                t
            } else if d > 0.0 {
                t + 1.0
            } else {
                t - 1.0
            }
        }
    };
}

rounding!(f64, floor64, ceil64, round64, round_even64);
rounding!(f32, floor32, ceil32, round32, round_even32);

/// The integer square root of `n` (the largest `r` with `r * r <= n`).
fn isqrt(n: u128) -> u128 {
    // Bit-by-bit (restoring) square root: 64 iterations, exact.
    let mut rem = n;
    let mut root = 0u128;
    let mut bit = 1u128 << 126;
    while bit > n {
        bit >>= 2;
    }
    while bit != 0 {
        if rem >= root + bit {
            rem -= root + bit;
            root = (root >> 1) + bit;
        } else {
            root >>= 1;
        }
        bit >>= 2;
    }
    root
}

/// The correctly rounded square root. Negative non-zero inputs give a NaN (the
/// folder never folds those; see the module docs).
pub(crate) fn sqrt<F: Ieee>(x: F) -> F {
    let bits = x.bits();
    let sign = bits & sign_bit::<F>();
    let mag = bits & !sign_bit::<F>();
    let exp_field = (mag >> F::FRAC) & F::EXP_MAX;
    if mag == 0 {
        // sqrt(+0) = +0, sqrt(-0) = -0.
        return x;
    }
    if exp_field == F::EXP_MAX {
        // +inf stays; NaN stays; -inf is invalid.
        return if sign != 0 && mag == F::EXP_MAX << F::FRAC {
            F::from_raw((F::EXP_MAX << F::FRAC) | (1 << (F::FRAC - 1)))
        } else {
            x
        };
    }
    if sign != 0 {
        return F::from_raw((F::EXP_MAX << F::FRAC) | (1 << (F::FRAC - 1)));
    }
    let frac_mask = (1u64 << F::FRAC) - 1;
    // x = m * 2^e with m an integer whose leading bit is bit FRAC.
    let (mut m, mut e) = if exp_field == 0 {
        // Subnormal: normalize the significand.
        let f = mag & frac_mask;
        let shift = f.leading_zeros() - (63 - F::FRAC);
        (f << shift, 1 - F::BIAS - F::FRAC as i32 - shift as i32)
    } else {
        (
            (mag & frac_mask) | (1u64 << F::FRAC),
            exp_field as i32 - F::BIAS - F::FRAC as i32,
        )
    };
    // Bring m into [2^L, 2^(L+2)) with L even and e even, so the integer root
    // has a fixed bit length.
    let low = F::FRAC + (F::FRAC & 1); // 52 for f64, 24 for f32
    let base = low - F::FRAC; // 0 or 1
    let s = if (e - base as i32) & 1 == 0 {
        base
    } else {
        base + 1
    };
    m <<= s;
    e -= s as i32;
    // Root of m * 2^S, S even, gives FRAC + 1 + GUARD bits.
    const GUARD: u32 = 5;
    let big_s = 2 * (F::FRAC + 1 + GUARD) - low - 2;
    let n = u128::from(m) << big_s;
    let r = isqrt(n);
    let sticky = r * r != n;
    // r has exactly FRAC + 1 + GUARD bits.
    let mut mant = (r >> GUARD) as u64;
    let rest = (r & ((1u128 << GUARD) - 1)) as u64;
    let half = 1u64 << (GUARD - 1);
    if rest > half || (rest == half && (sticky || mant & 1 == 1)) {
        mant += 1;
    }
    // value = mant * 2^q
    let mut q = GUARD as i32 + (e - big_s as i32) / 2;
    if mant >> (F::FRAC + 1) != 0 {
        mant >>= 1;
        q += 1;
    }
    // The result of a positive finite square root is always normal.
    let biased = (q + F::FRAC as i32 + F::BIAS) as u64;
    F::from_raw((biased << F::FRAC) | (mant & frac_mask))
}

/// IEEE 754 `remainder`, exactly as the reference interpreter computes it (after
/// fdlibm's `__ieee754_remainder`).
pub(crate) fn ieee_remainder(x: f64, y: f64) -> f64 {
    if y == 0.0 || x.is_infinite() || x.is_nan() || y.is_nan() {
        return f64::NAN;
    }
    if y.is_infinite() {
        return x;
    }
    let abs = |v: f64| f64::from_bits(v.to_bits() & !(1u64 << 63));
    let negative = x.is_sign_negative();
    let p = abs(y);
    let mut r = if p <= f64::MAX / 2.0 { x % (p + p) } else { x };
    r = abs(r);
    if p < 2.0 * f64::MIN_POSITIVE {
        if r + r > p {
            r -= p;
            if r + r >= p {
                r -= p;
            }
        }
    } else {
        let half = 0.5 * p;
        if r > half {
            r -= p;
            if r >= half {
                r -= p;
            }
        }
    }
    if negative { -r } else { r }
}

/// OPS `min`: NaN if either operand is NaN; `min(-0, +0) = -0`.
pub(crate) fn fmin(a: f64, b: f64) -> f64 {
    if a.is_nan() || b.is_nan() {
        f64::NAN
    } else if a < b {
        a
    } else if b < a {
        b
    } else if a.is_sign_negative() {
        a
    } else {
        b
    }
}

/// OPS `max`: NaN if either operand is NaN; `max(-0, +0) = +0`.
pub(crate) fn fmax(a: f64, b: f64) -> f64 {
    if a.is_nan() || b.is_nan() {
        f64::NAN
    } else if a > b || (a == b && b.is_sign_negative()) {
        a
    } else {
        b
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use proptest::prelude::*;

    fn same64(a: f64, b: f64) -> bool {
        a.to_bits() == b.to_bits() || (a.is_nan() && b.is_nan())
    }

    fn same32(a: f32, b: f32) -> bool {
        a.to_bits() == b.to_bits() || (a.is_nan() && b.is_nan())
    }

    const EDGES64: [f64; 22] = [
        0.0,
        -0.0,
        0.5,
        -0.5,
        1.5,
        -1.5,
        2.5,
        -2.5,
        0.49999999999999994,
        -0.49999999999999994,
        4503599627370495.5,
        -4503599627370495.5,
        4503599627370496.0,
        9007199254740993.0,
        f64::MAX,
        f64::MIN,
        f64::MIN_POSITIVE,
        5e-324,
        f64::INFINITY,
        f64::NEG_INFINITY,
        1e300,
        -3.75,
    ];

    #[test]
    fn test_rounding_matches_std_on_edges() {
        for &x in &EDGES64 {
            assert!(same64(trunc(x), x.trunc()), "trunc {x}");
            assert!(same64(floor64(x), x.floor()), "floor {x}");
            assert!(same64(ceil64(x), x.ceil()), "ceil {x}");
            assert!(same64(round64(x), x.round()), "round {x}");
            assert!(same64(round_even64(x), x.round_ties_even()), "even {x}");
            let y = x as f32;
            assert!(same32(trunc(y), y.trunc()), "trunc32 {y}");
            assert!(same32(floor32(y), y.floor()), "floor32 {y}");
            assert!(same32(ceil32(y), y.ceil()), "ceil32 {y}");
            assert!(same32(round32(y), y.round()), "round32 {y}");
            assert!(same32(round_even32(y), y.round_ties_even()), "even32 {y}");
        }
    }

    #[test]
    fn test_sqrt_matches_std_on_edges() {
        for &x in &EDGES64 {
            assert!(same64(sqrt(x), x.sqrt()), "sqrt {x}");
            let y = x as f32;
            assert!(same32(sqrt(y), y.sqrt()), "sqrt32 {y}");
        }
        for k in 0..2000u64 {
            let x = k as f64;
            assert!(same64(sqrt(x), x.sqrt()), "sqrt {x}");
            let y = k as f32;
            assert!(same32(sqrt(y), y.sqrt()), "sqrt32 {y}");
        }
    }

    #[test]
    fn test_nan_inputs_are_total() {
        assert!(trunc(f64::NAN).is_nan());
        assert!(sqrt(f64::NAN).is_nan());
        assert!(sqrt(-1.0f64).is_nan());
        assert!(sqrt(f32::NEG_INFINITY).is_nan());
        assert!(round_even64(f64::NAN).is_nan());
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(4096))]

        #[test]
        fn prop_f64_helpers_match_std(bits in any::<u64>()) {
            let x = f64::from_bits(bits);
            prop_assert!(same64(trunc(x), x.trunc()));
            prop_assert!(same64(floor64(x), x.floor()));
            prop_assert!(same64(ceil64(x), x.ceil()));
            prop_assert!(same64(round64(x), x.round()));
            prop_assert!(same64(round_even64(x), x.round_ties_even()));
            prop_assert!(same64(sqrt(x), x.sqrt()), "{x:e}");
        }

        #[test]
        fn prop_f32_helpers_match_std(bits in any::<u32>()) {
            let x = f32::from_bits(bits);
            prop_assert!(same32(trunc(x), x.trunc()));
            prop_assert!(same32(floor32(x), x.floor()));
            prop_assert!(same32(ceil32(x), x.ceil()));
            prop_assert!(same32(round32(x), x.round()));
            prop_assert!(same32(round_even32(x), x.round_ties_even()));
            prop_assert!(same32(sqrt(x), x.sqrt()), "{x:e}");
        }

        #[test]
        fn prop_small_magnitudes_round_like_std(x in -1.0e6f64..1.0e6) {
            prop_assert!(same64(round64(x), x.round()));
            prop_assert!(same64(round_even64(x), x.round_ties_even()));
            prop_assert!(same64(floor64(x), x.floor()));
            prop_assert!(same64(ceil64(x), x.ceil()));
        }
    }
}
