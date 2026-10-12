//! Constant folding with the exact operation semantics of `specs/OPS.md`.
//!
//! Every function here gives, for constant operands, exactly what the reference
//! interpreter (`ir_lang::interp::eval_*`) computes at run time: the same result
//! bits, or the same error kind under an `error` policy, or the same trap under a
//! `trap` policy. The unit tests check this against the interpreter on every
//! operation, type, and policy, over the OPS §7 edge values and random bits.
//!
//! Two things are deliberately not folded ([`Fold::Unknown`]), so the optimized
//! program keeps computing them at run time:
//!
//! - a float **arithmetic** result that is a NaN. OPS §4 lets an operation produce
//!   any quiet NaN, and the payload a machine produces differs between targets;
//!   folding would fix one payload at compile time. Bit-level operations
//!   (`bitcast`, `select`, constants) are exact and are folded even when the bits
//!   are a NaN.
//! - `fma`, `ref_to_ptr`, `ptr_to_int`, and `int_to_ptr`: there is no exact
//!   `fma` in `core`, and addresses are not compile-time constants.
//!
//! An operation whose policy would raise at run time is never folded into a
//! value: it folds to [`Fold::Error`] or [`Fold::Trap`], and the caller keeps the
//! raising control flow (a `check`'s error edge, or a `trap`).
//!
//! OPS v2 is covered: integer `pow` (exact repeated squaring, `0 ** 0 = 1`,
//! overflow per policy, a negative exponent is `NegativeExponent` under every
//! policy), float `pow` through ir-lang's shared [`ls_pow`](ir_lang::ls_pow)
//! (which lives in `core`, so `no_std` builds fold it too), and
//! `shift = saturate`.
//!
//! [`binary_partial`] extends folding to operations where only some operands
//! are constant: what the result is (`x ** 0`, `x * 0`), which operand it is
//! (`x ** 1`, `x + 0`), and which errors remain possible (none for `x ** 3`
//! under `wrap`; only overflow for `x ** 3` under `error`).

use ir_lang::{
    BinaryOp, CmpOp, ConvOp, DivZero, FloatToInt, InstData, OpError, Overflow, Policy, Shift, Type,
    UnaryOp,
};

use crate::float;

/// The outcome of folding one operation on constant operands.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Fold {
    /// The result bits, masked to the result type's width.
    Value(u64),
    /// The operation raises this error under an `error` policy.
    Error(OpError),
    /// The operation traps with this kind under a `trap` policy.
    Trap(OpError),
    /// Not folded (see the module docs); the operation stays.
    Unknown,
}

fn mask(ty: Type) -> u64 {
    // Folding never sees a 32-bit pointer: pointer-typed values are not folded.
    let w = ty.bits(ir_lang::PointerWidth::P64);
    if w >= 64 { u64::MAX } else { (1u64 << w) - 1 }
}

/// The integer value of `bits` read as `ty`, sign-extended for signed types.
pub(crate) fn sval(ty: Type, bits: u64) -> i128 {
    let w = ty.int_bits().unwrap_or(64);
    if ty.is_signed_int() {
        let shift = 64 - w;
        i128::from(((bits << shift) as i64) >> shift)
    } else {
        i128::from(bits & mask(ty))
    }
}

fn int_range(ty: Type) -> (i128, i128) {
    let w = ty.int_bits().unwrap_or(64);
    if ty.is_signed_int() {
        (-(1i128 << (w - 1)), (1i128 << (w - 1)) - 1)
    } else {
        (0, (1i128 << w) - 1)
    }
}

fn wrap(ty: Type, v: i128) -> u64 {
    (v as u64) & mask(ty)
}

fn overflow(policy: Policy, wrapped: u64) -> Fold {
    match policy.overflow {
        Some(Overflow::Trap) => Fold::Trap(OpError::ArithOverflow),
        Some(Overflow::Error) => Fold::Error(OpError::ArithOverflow),
        // `wrap`, or no field (never in validated IR): the wrapped bits.
        _ => Fold::Value(wrapped),
    }
}

fn div_zero(policy: Policy) -> Fold {
    match policy.div_zero {
        Some(DivZero::Trap) => Fold::Trap(OpError::DivByZero),
        _ => Fold::Error(OpError::DivByZero),
    }
}

/// An exact integer result: its bits if representable in `ty`, else the
/// `overflow` policy applied to the wrapped bits.
fn exact(ty: Type, policy: Policy, v: Option<i128>, wrapped: u64) -> Fold {
    let (lo, hi) = int_range(ty);
    match v {
        Some(v) if v >= lo && v <= hi => Fold::Value(wrap(ty, v)),
        _ => overflow(policy, wrapped),
    }
}

/// A float arithmetic result, refused when it is a NaN (see the module docs).
fn float_result(ty: Type, bits: u64) -> Fold {
    let nan = if ty == Type::F32 {
        f32::from_bits(bits as u32).is_nan()
    } else {
        f64::from_bits(bits).is_nan()
    };
    if nan {
        Fold::Unknown
    } else {
        Fold::Value(bits)
    }
}

/// Folds a unary operation on the bits `a` of type `ty`.
pub(crate) fn unary(op: UnaryOp, policy: Policy, ty: Type, a: u64) -> Fold {
    if ty.is_int() {
        let x = sval(ty, a);
        return match op {
            UnaryOp::Neg => exact(ty, policy, Some(-x), wrap(ty, 0i128.wrapping_sub(x))),
            UnaryOp::Abs => exact(ty, policy, Some(x.abs()), wrap(ty, x.abs())),
            UnaryOp::Not => Fold::Value(!a & mask(ty)),
            _ => Fold::Unknown,
        };
    }
    if ty == Type::Bool {
        return match op {
            UnaryOp::Not => Fold::Value((a & 1) ^ 1),
            _ => Fold::Unknown,
        };
    }
    if ty == Type::F32 {
        let sign = 1u64 << 31;
        let x = f32::from_bits(a as u32);
        let r = match op {
            UnaryOp::Neg => return float_result(ty, (a ^ sign) & mask(ty)),
            UnaryOp::Abs => return float_result(ty, a & !sign & mask(ty)),
            UnaryOp::Sqrt => float::sqrt(x),
            UnaryOp::Floor => float::floor32(x),
            UnaryOp::Ceil => float::ceil32(x),
            UnaryOp::Trunc => float::trunc(x),
            UnaryOp::Round => float::round32(x),
            UnaryOp::RoundEven => float::round_even32(x),
            _ => return Fold::Unknown,
        };
        return float_result(ty, u64::from(r.to_bits()));
    }
    if ty == Type::F64 {
        let sign = 1u64 << 63;
        let x = f64::from_bits(a);
        let r = match op {
            UnaryOp::Neg => return float_result(ty, a ^ sign),
            UnaryOp::Abs => return float_result(ty, a & !sign),
            UnaryOp::Sqrt => float::sqrt(x),
            UnaryOp::Floor => float::floor64(x),
            UnaryOp::Ceil => float::ceil64(x),
            UnaryOp::Trunc => float::trunc(x),
            UnaryOp::Round => float::round64(x),
            UnaryOp::RoundEven => float::round_even64(x),
            _ => return Fold::Unknown,
        };
        return float_result(ty, r.to_bits());
    }
    Fold::Unknown
}

fn int_binary(op: BinaryOp, policy: Policy, ty: Type, a: u64, b: u64) -> Fold {
    let m = mask(ty);
    let (a, b) = (a & m, b & m);
    let (x, y) = (sval(ty, a), sval(ty, b));
    let w = ty.int_bits().unwrap_or(64);
    match op {
        BinaryOp::Add => exact(ty, policy, x.checked_add(y), a.wrapping_add(b) & m),
        BinaryOp::Sub => exact(ty, policy, x.checked_sub(y), a.wrapping_sub(b) & m),
        BinaryOp::Mul => exact(ty, policy, x.checked_mul(y), a.wrapping_mul(b) & m),
        BinaryOp::Div | BinaryOp::FloorDiv => {
            if y == 0 {
                return div_zero(policy);
            }
            let mut q = x / y;
            if op == BinaryOp::FloorDiv && x % y != 0 && ((x < 0) != (y < 0)) {
                q -= 1;
            }
            exact(ty, policy, Some(q), wrap(ty, q))
        }
        BinaryOp::Rem | BinaryOp::FloorMod => {
            if y == 0 {
                return div_zero(policy);
            }
            let mut r = x % y;
            if op == BinaryOp::FloorMod && r != 0 && ((r < 0) != (y < 0)) {
                r += y;
            }
            Fold::Value(wrap(ty, r))
        }
        BinaryOp::And => Fold::Value(a & b),
        BinaryOp::Or => Fold::Value(a | b),
        BinaryOp::Xor => Fold::Value(a ^ b),
        BinaryOp::Shl | BinaryOp::Shr => {
            let n = if y < 0 || y >= i128::from(w) {
                match policy.shift {
                    Some(Shift::Mask) => (b & u64::from(w - 1)) as u32,
                    // Every bit is shifted out; an arithmetic right shift of a
                    // negative value keeps the sign. A negative amount is
                    // still an error.
                    Some(Shift::Saturate) if y >= 0 => {
                        return Fold::Value(if op == BinaryOp::Shr && x < 0 { m } else { 0 });
                    }
                    _ => return Fold::Error(OpError::ShiftOutOfRange),
                }
            } else {
                y as u32
            };
            if op == BinaryOp::Shl {
                Fold::Value(a.checked_shl(n).unwrap_or(0) & m)
            } else if ty.is_signed_int() {
                Fold::Value(wrap(ty, x >> n))
            } else {
                Fold::Value(a >> n)
            }
        }
        BinaryOp::Min => Fold::Value(if x <= y { a } else { b }),
        BinaryOp::Max => Fold::Value(if x >= y { a } else { b }),
        BinaryOp::Pow => int_pow(ty, policy, x, y, a),
        _ => Fold::Unknown,
    }
}

/// Integer `pow` (OPS v2): the exact power of `x` (bits `a`) to `e >= 0`, or
/// the `overflow` policy applied to the wrapped power. A negative exponent is
/// the `NegativeExponent` error under every policy the IR can express (only
/// `promote` would give a value), `trap` included.
fn int_pow(ty: Type, policy: Policy, x: i128, e: i128, a: u64) -> Fold {
    if e < 0 {
        return Fold::Error(OpError::NegativeExponent);
    }
    // Repeated squaring, twice over: wrapping in u64 gives the low bits of the
    // exact power (reduction mod 2^width commutes with multiplication), and
    // checked in i128 gives the exact power, or `None` once it leaves i128 (far
    // beyond every type). A square is taken only while a higher exponent bit
    // remains, so an overflowing square is always multiplied in. At most 64
    // rounds: the exponent has at most 64 bits.
    let (mut wrapped, mut wbase) = (1u64, a);
    let (mut power, mut base) = (Some(1i128), Some(x));
    let mut e = e as u128;
    loop {
        if e & 1 == 1 {
            wrapped = wrapped.wrapping_mul(wbase);
            power = match (power, base) {
                (Some(r), Some(b)) => r.checked_mul(b),
                _ => None,
            };
        }
        e >>= 1;
        if e == 0 {
            break;
        }
        wbase = wbase.wrapping_mul(wbase);
        base = base.and_then(|b| b.checked_mul(b));
    }
    exact(ty, policy, power, wrapped & mask(ty))
}

/// Folds a binary operation on the bits `a`, `b` of type `ty`. `total_cmp`
/// gives the bits of an `i8`.
pub(crate) fn binary(op: BinaryOp, policy: Policy, ty: Type, a: u64, b: u64) -> Fold {
    if ty.is_int() {
        return int_binary(op, policy, ty, a, b);
    }
    if ty == Type::Bool {
        let (a, b) = (a & 1, b & 1);
        return match op {
            BinaryOp::And => Fold::Value(a & b),
            BinaryOp::Or => Fold::Value(a | b),
            BinaryOp::Xor => Fold::Value(a ^ b),
            _ => Fold::Unknown,
        };
    }
    if ty == Type::F32 {
        let (x, y) = (f32::from_bits(a as u32), f32::from_bits(b as u32));
        let r = match op {
            BinaryOp::Add => x + y,
            BinaryOp::Sub => x - y,
            BinaryOp::Mul => x * y,
            BinaryOp::Div => x / y,
            BinaryOp::Rem => x % y,
            BinaryOp::IeeeRem => float::ieee_remainder(f64::from(x), f64::from(y)) as f32,
            BinaryOp::Min => float::fmin(f64::from(x), f64::from(y)) as f32,
            BinaryOp::Max => float::fmax(f64::from(x), f64::from(y)) as f32,
            // OPS v2: widen, compute with the shared routine, round once.
            BinaryOp::Pow => ir_lang::ls_pow(f64::from(x), f64::from(y)) as f32,
            BinaryOp::TotalCmp => {
                return Fold::Value(wrap(Type::I8, x.total_cmp(&y) as i128));
            }
            _ => return Fold::Unknown,
        };
        return float_result(ty, u64::from(r.to_bits()));
    }
    if ty == Type::F64 {
        let (x, y) = (f64::from_bits(a), f64::from_bits(b));
        let r = match op {
            BinaryOp::Add => x + y,
            BinaryOp::Sub => x - y,
            BinaryOp::Mul => x * y,
            BinaryOp::Div => x / y,
            BinaryOp::Rem => x % y,
            BinaryOp::IeeeRem => float::ieee_remainder(x, y),
            BinaryOp::Min => float::fmin(x, y),
            BinaryOp::Max => float::fmax(x, y),
            BinaryOp::Pow => ir_lang::ls_pow(x, y),
            BinaryOp::TotalCmp => {
                return Fold::Value(wrap(Type::I8, x.total_cmp(&y) as i128));
            }
            _ => return Fold::Unknown,
        };
        return float_result(ty, r.to_bits());
    }
    Fold::Unknown
}

/// Folds a comparison of the bits `a`, `b` of type `ty`; `None` for a type the
/// folder does not handle (`ptr`, `ref`).
pub(crate) fn compare(op: CmpOp, ty: Type, a: u64, b: u64) -> Option<bool> {
    if ty.is_float() {
        let (x, y) = if ty == Type::F32 {
            (
                f64::from(f32::from_bits(a as u32)),
                f64::from(f32::from_bits(b as u32)),
            )
        } else {
            (f64::from_bits(a), f64::from_bits(b))
        };
        return relation(op, x, y);
    }
    let (x, y) = if ty.is_int() {
        (sval(ty, a), sval(ty, b))
    } else if ty == Type::Bool {
        (i128::from(a & 1), i128::from(b & 1))
    } else {
        return None;
    };
    relation(op, x, y)
}

/// `x op y` (IEEE semantics for floats: every relation with NaN is false but
/// `ne`). `None` for a comparison this crate does not know.
fn relation<T: PartialOrd>(op: CmpOp, x: T, y: T) -> Option<bool> {
    Some(match op {
        CmpOp::Eq => x == y,
        CmpOp::Ne => x != y,
        CmpOp::Lt => x < y,
        CmpOp::Le => x <= y,
        CmpOp::Gt => x > y,
        CmpOp::Ge => x >= y,
        _ => return None,
    })
}

/// `2^n` as an exact `f64` (n <= 64).
fn pow2(n: u32) -> f64 {
    (1u128 << n) as f64
}

/// Folds a conversion of the bits `a` of type `from` to type `to`.
pub(crate) fn convert(op: ConvOp, policy: Policy, from: Type, to: Type, a: u64) -> Fold {
    // Addresses are never compile-time values.
    if matches!(from, Type::Ptr | Type::Ref) || matches!(to, Type::Ptr | Type::Ref) {
        return Fold::Unknown;
    }
    let tm = mask(to);
    match op {
        ConvOp::IntCast if from.is_int() && to.is_int() => {
            let v = sval(from, a);
            exact(to, policy, Some(v), wrap(to, v))
        }
        ConvOp::Zext | ConvOp::Narrow | ConvOp::Bitcast | ConvOp::BoolToInt => {
            Fold::Value(a & mask(from) & tm)
        }
        ConvOp::Sext if from.is_int() => {
            let signed = Type::int(from.int_bits().unwrap_or(64), true).unwrap_or(Type::I64);
            Fold::Value(wrap(to, sval(signed, a)))
        }
        ConvOp::IntToFloat if from.is_int() => {
            let v = sval(from, a);
            Fold::Value(if to == Type::F32 {
                u64::from((v as f32).to_bits())
            } else {
                (v as f64).to_bits()
            })
        }
        ConvOp::FloatToInt if from.is_float() && to.is_int() => {
            let x = if from == Type::F32 {
                f64::from(f32::from_bits(a as u32))
            } else {
                f64::from_bits(a)
            };
            let w = to.int_bits().unwrap_or(64);
            let (lo, hi_excl) = if to.is_signed_int() {
                (-pow2(w - 1), pow2(w - 1))
            } else {
                (0.0, pow2(w))
            };
            let t = float::trunc(x);
            if !x.is_nan() && t >= lo && t < hi_excl {
                return Fold::Value(wrap(to, t as i128));
            }
            match policy.float_to_int {
                Some(FloatToInt::Saturate) => {
                    let (min, max) = int_range(to);
                    Fold::Value(if x.is_nan() {
                        0
                    } else if x < 0.0 {
                        wrap(to, min)
                    } else {
                        wrap(to, max)
                    })
                }
                _ => Fold::Error(OpError::InvalidConversion),
            }
        }
        ConvOp::FloatCast if from.is_float() => {
            let bits = if to == Type::F64 {
                f64::from(f32::from_bits(a as u32)).to_bits()
            } else {
                u64::from((f64::from_bits(a) as f32).to_bits())
            };
            float_result(to, bits)
        }
        ConvOp::CharFromU32 => {
            if a <= 0x10_FFFF && !(0xD800..=0xDFFF).contains(&a) {
                Fold::Value(a)
            } else {
                Fold::Error(OpError::InvalidChar)
            }
        }
        _ => Fold::Unknown,
    }
}

/// The bit of OPS error `e` in an error-kind set.
pub(crate) const fn bit(e: OpError) -> u32 {
    1 << e.code()
}

/// The error kinds an operation can raise, as a bit set over OPS codes (bit `k`
/// for code `k`); empty when it cannot raise. `ty` is the type of the first
/// operand. Non-empty exactly when ir-lang's `can_error` says so (checked in
/// the tests): an `error` field, `char_from_u32`, and on signed integers `pow`
/// (a negative exponent) and `saturate` shifts (a negative amount).
pub(crate) fn error_kinds(data: &InstData, ty: Type) -> u32 {
    let mut set = 0u32;
    let mut add = |e: OpError| set |= bit(e);
    if let InstData::Binary { op, policy, .. } = data {
        if ty.is_signed_int() {
            match op {
                BinaryOp::Pow => add(OpError::NegativeExponent),
                BinaryOp::Shl | BinaryOp::Shr if policy.shift == Some(Shift::Saturate) => {
                    add(OpError::ShiftOutOfRange);
                }
                _ => {}
            }
        }
    }
    match data {
        InstData::Unary { policy, .. }
        | InstData::Binary { policy, .. }
        | InstData::Convert { policy, .. } => {
            if policy.overflow == Some(Overflow::Error) {
                add(OpError::ArithOverflow);
            }
            if policy.div_zero == Some(DivZero::Error) {
                add(OpError::DivByZero);
            }
            if policy.shift == Some(Shift::Error) {
                add(OpError::ShiftOutOfRange);
            }
            if policy.float_to_int == Some(FloatToInt::Error) {
                add(OpError::InvalidConversion);
            }
            if let InstData::Convert {
                op: ConvOp::CharFromU32,
                ..
            } = data
            {
                add(OpError::InvalidChar);
            }
        }
        _ => {}
    }
    set
}

/// What is known about an integer binary operation when only some of its
/// operands are constants.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(crate) enum Partial {
    /// Every execution has this outcome (never [`Fold::Unknown`]).
    Always(Fold),
    /// The result is always operand `k`, and the operation never raises or
    /// traps.
    Operand(usize),
    /// Not determined. A `trap` policy may still trap.
    Open {
        /// The result whenever the operation succeeds, if that is known.
        value: Option<u64>,
        /// The OPS error kinds still possible (a subset of [`error_kinds`]).
        errors: u32,
    },
}

/// Folds a binary operation as far as the known operands allow (`None`: not
/// a constant). With both known it is [`binary`]. Every rule is exact under
/// OPS for every policy, and is checked against the interpreter in the tests:
///
/// - `x + 0`, `0 + x`, `x - 0`, `x * 1`, `1 * x`, `x / 1`, `x << 0`, `x >> 0`,
///   and `x ** 1` are the other operand, and never raise or trap;
/// - `x * 0`, `0 * x`, and `x ** 0` (`0 ** 0` included) are constants;
/// - a division or remainder by a constant zero, a constant out-of-range shift
///   under `error`, a negative constant shift under `saturate`, and a negative
///   constant exponent always raise (or trap, per the policy);
/// - a `saturate` shift by a constant at least the width is `0` (left, or right
///   on an unsigned type);
/// - a division by a constant other than `0` and `-1`, a remainder by a
///   nonzero constant, and a shift by an in-range constant cannot raise;
/// - `pow` with a constant non-negative exponent cannot raise
///   `NegativeExponent`; with base `0`, `1`, or `-1` it cannot overflow, and
///   `1 ** y` is `1` whenever it succeeds.
pub(crate) fn binary_partial(
    op: BinaryOp,
    policy: Policy,
    ty: Type,
    a: Option<u64>,
    b: Option<u64>,
) -> Partial {
    let probe = InstData::Binary {
        op,
        policy,
        args: [ir_lang::Value::from_u32(0); 2],
    };
    let errors = error_kinds(&probe, ty);
    let open = Partial::Open {
        value: None,
        errors,
    };
    if let (Some(a), Some(b)) = (a, b) {
        return match binary(op, policy, ty, a, b) {
            Fold::Unknown => open,
            f => Partial::Always(f),
        };
    }
    if !ty.is_int() {
        return open;
    }
    let w = i128::from(ty.int_bits().unwrap_or(64));
    let (x, y) = (a.map(|a| sval(ty, a)), b.map(|b| sval(ty, b)));
    let safe = Partial::Open {
        value: None,
        errors: 0,
    };
    let neg_exp = bit(OpError::NegativeExponent);
    match op {
        BinaryOp::Add => match (x, y) {
            (_, Some(0)) => Partial::Operand(0),
            (Some(0), _) => Partial::Operand(1),
            _ => open,
        },
        BinaryOp::Sub if y == Some(0) => Partial::Operand(0),
        BinaryOp::Mul => match (x, y) {
            (_, Some(1)) => Partial::Operand(0),
            (Some(1), _) => Partial::Operand(1),
            (_, Some(0)) | (Some(0), _) => Partial::Always(Fold::Value(0)),
            _ => open,
        },
        BinaryOp::Div | BinaryOp::FloorDiv => match y {
            Some(0) => Partial::Always(div_zero(policy)),
            Some(1) => Partial::Operand(0),
            // Only `MIN / -1` overflows.
            Some(-1) => Partial::Open {
                value: None,
                errors: errors & bit(OpError::ArithOverflow),
            },
            Some(_) => safe,
            None => open,
        },
        BinaryOp::Rem | BinaryOp::FloorMod => match y {
            Some(0) => Partial::Always(div_zero(policy)),
            Some(_) => safe,
            None => open,
        },
        BinaryOp::Shl | BinaryOp::Shr => match y {
            Some(0) => Partial::Operand(0),
            Some(n) if (0..w).contains(&n) => safe,
            Some(n) => match policy.shift {
                Some(Shift::Mask) => safe,
                Some(Shift::Saturate) if n >= 0 => {
                    if op == BinaryOp::Shl || !ty.is_signed_int() {
                        Partial::Always(Fold::Value(0))
                    } else {
                        safe
                    }
                }
                _ => Partial::Always(Fold::Error(OpError::ShiftOutOfRange)),
            },
            None => open,
        },
        BinaryOp::Pow => match (x, y) {
            (_, Some(e)) if e < 0 => Partial::Always(Fold::Error(OpError::NegativeExponent)),
            (_, Some(0)) => Partial::Always(Fold::Value(1)),
            (_, Some(1)) => Partial::Operand(0),
            (_, Some(_)) => Partial::Open {
                value: None,
                errors: errors & !neg_exp,
            },
            // |base| <= 1 never overflows; only the exponent's sign matters.
            (Some(1), None) if errors & neg_exp == 0 => Partial::Always(Fold::Value(1)),
            (Some(1), None) => Partial::Open {
                value: Some(1),
                errors: errors & neg_exp,
            },
            (Some(0 | -1), None) => Partial::Open {
                value: None,
                errors: errors & neg_exp,
            },
            _ => open,
        },
        _ => open,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ir_lang::interp::{self, OpFault};
    use proptest::prelude::*;
    use std::vec::Vec;

    /// Our fold agrees with the interpreter's semantics: a value only where the
    /// interpreter computes that exact value, and the same error or trap.
    fn agrees(ours: Fold, theirs: Result<u64, OpFault>) -> bool {
        match (ours, theirs) {
            (Fold::Value(v), Ok(w)) => v == w,
            (Fold::Error(e), Err(OpFault::Error(f))) => e == f,
            (Fold::Trap(e), Err(OpFault::Trap(f))) => e == f,
            (Fold::Unknown, _) => true,
            _ => false,
        }
    }

    fn is_nan(ty: Type, bits: u64) -> bool {
        match ty {
            Type::F32 => f32::from_bits(bits as u32).is_nan(),
            Type::F64 => f64::from_bits(bits).is_nan(),
            _ => false,
        }
    }

    /// `Unknown` is only allowed where the module docs say so: a NaN float result.
    fn unknown_allowed(ty: Type, theirs: Result<u64, OpFault>) -> bool {
        matches!(theirs, Ok(bits) if is_nan(ty, bits))
    }

    const INT_TYPES: [Type; 8] = [
        Type::I8,
        Type::I16,
        Type::I32,
        Type::I64,
        Type::U8,
        Type::U16,
        Type::U32,
        Type::U64,
    ];

    fn int_edges(ty: Type) -> Vec<u64> {
        let (lo, hi) = int_range(ty);
        let vals = [
            0,
            1,
            -1,
            2,
            -2,
            7,
            lo,
            hi,
            lo + 1,
            hi - 1,
            63,
            64,
            65,
            31,
            32,
            8,
        ];
        vals.iter().map(|&v| wrap(ty, v)).collect()
    }

    fn float_edges(ty: Type) -> Vec<u64> {
        let vals = [
            0.0f64,
            -0.0,
            1.0,
            -1.0,
            0.5,
            -0.5,
            2.5,
            1.5,
            f64::NAN,
            f64::INFINITY,
            f64::NEG_INFINITY,
            f64::MAX,
            f64::MIN,
            f64::MIN_POSITIVE,
            5e-324,
            1e10,
            -3.75,
            9.223_372_036_854_776e18,
            -9.223_372_036_854_776e18,
            255.9,
            -128.5,
            4294967296.0,
        ];
        if ty == Type::F32 {
            vals.iter()
                .map(|&v| u64::from((v as f32).to_bits()))
                .chain([u64::from(f32::from_bits(1).to_bits())])
                .collect()
        } else {
            vals.iter().map(|v| v.to_bits()).collect()
        }
    }

    fn int_policies(op: BinaryOp) -> Vec<Policy> {
        let mut out = Vec::new();
        let req = Policy::required_binary(op, Type::I32);
        let ovs: &[Option<Overflow>] = if req.overflow {
            &[
                Some(Overflow::Error),
                Some(Overflow::Wrap),
                Some(Overflow::Trap),
            ]
        } else {
            &[None]
        };
        let dzs: &[Option<DivZero>] = if req.div_zero {
            &[Some(DivZero::Error), Some(DivZero::Trap)]
        } else {
            &[None]
        };
        let shs: &[Option<Shift>] = if req.shift {
            &[Some(Shift::Error), Some(Shift::Mask), Some(Shift::Saturate)]
        } else {
            &[None]
        };
        for &overflow in ovs {
            for &div_zero in dzs {
                for &shift in shs {
                    out.push(Policy {
                        overflow,
                        div_zero,
                        shift,
                        float_to_int: None,
                    });
                }
            }
        }
        out
    }

    #[test]
    fn test_int_binary_agrees_with_interpreter_on_edges() {
        for &ty in &INT_TYPES {
            let edges = int_edges(ty);
            for &op in BinaryOp::ALL {
                if matches!(op, BinaryOp::IeeeRem | BinaryOp::TotalCmp) {
                    continue;
                }
                for p in int_policies(op) {
                    for &a in &edges {
                        for &b in &edges {
                            let ours = binary(op, p, ty, a, b);
                            let theirs = interp::eval_binary(op, p, ty, a, b);
                            assert!(
                                agrees(ours, theirs) && ours != Fold::Unknown,
                                "{op:?} {p:?} {ty:?} {a:#x} {b:#x}: {ours:?} vs {theirs:?}"
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_float_binary_agrees_with_interpreter_on_edges() {
        for ty in [Type::F32, Type::F64] {
            let edges = float_edges(ty);
            for op in [
                BinaryOp::Add,
                BinaryOp::Sub,
                BinaryOp::Mul,
                BinaryOp::Div,
                BinaryOp::Rem,
                BinaryOp::IeeeRem,
                BinaryOp::Min,
                BinaryOp::Max,
                BinaryOp::TotalCmp,
                BinaryOp::Pow,
            ] {
                for &a in &edges {
                    for &b in &edges {
                        let ours = binary(op, Policy::NONE, ty, a, b);
                        let theirs = interp::eval_binary(op, Policy::NONE, ty, a, b);
                        assert!(agrees(ours, theirs), "{op:?} {ty:?} {a:#x} {b:#x}");
                        if ours == Fold::Unknown {
                            assert!(unknown_allowed(ty, theirs), "{op:?} {ty:?} {a:#x} {b:#x}");
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn test_unary_agrees_with_interpreter_on_edges() {
        for &ty in &INT_TYPES {
            for &a in &int_edges(ty) {
                for o in [Overflow::Error, Overflow::Wrap, Overflow::Trap] {
                    for op in [UnaryOp::Neg, UnaryOp::Abs] {
                        let p = Policy::overflow(o);
                        let ours = unary(op, p, ty, a);
                        assert!(agrees(ours, interp::eval_unary(op, p, ty, a)));
                        assert_ne!(ours, Fold::Unknown);
                    }
                }
                let ours = unary(UnaryOp::Not, Policy::NONE, ty, a);
                assert!(agrees(
                    ours,
                    interp::eval_unary(UnaryOp::Not, Policy::NONE, ty, a)
                ));
            }
        }
        for a in [0, 1] {
            let ours = unary(UnaryOp::Not, Policy::NONE, Type::Bool, a);
            assert_eq!(ours, Fold::Value(a ^ 1));
        }
        for ty in [Type::F32, Type::F64] {
            for &a in &float_edges(ty) {
                for &op in UnaryOp::ALL {
                    if op == UnaryOp::Not {
                        continue;
                    }
                    let ours = unary(op, Policy::NONE, ty, a);
                    let theirs = interp::eval_unary(op, Policy::NONE, ty, a);
                    assert!(agrees(ours, theirs), "{op:?} {ty:?} {a:#x}");
                    if ours == Fold::Unknown {
                        assert!(unknown_allowed(ty, theirs));
                    }
                }
            }
        }
    }

    #[test]
    fn test_compare_agrees_with_interpreter_on_edges() {
        for &ty in &INT_TYPES {
            let edges = int_edges(ty);
            for &op in CmpOp::ALL {
                for &a in &edges {
                    for &b in &edges {
                        assert_eq!(
                            compare(op, ty, a, b),
                            Some(interp::eval_compare(op, ty, a, b))
                        );
                    }
                }
            }
        }
        for ty in [Type::F32, Type::F64] {
            let edges = float_edges(ty);
            for &op in CmpOp::ALL {
                for &a in &edges {
                    for &b in &edges {
                        assert_eq!(
                            compare(op, ty, a, b),
                            Some(interp::eval_compare(op, ty, a, b))
                        );
                    }
                }
            }
        }
        for a in [0, 1] {
            for b in [0, 1] {
                for op in [CmpOp::Eq, CmpOp::Ne] {
                    assert_eq!(
                        compare(op, Type::Bool, a, b),
                        Some(interp::eval_compare(op, Type::Bool, a, b))
                    );
                }
            }
        }
        assert_eq!(compare(CmpOp::Eq, Type::Ptr, 0, 0), None);
    }

    fn conversions() -> Vec<(ConvOp, Type, Type)> {
        let mut out = Vec::new();
        for &from in &INT_TYPES {
            for &to in &INT_TYPES {
                let (fw, tw) = (from.int_bits().unwrap_or(0), to.int_bits().unwrap_or(0));
                if from != to {
                    out.push((ConvOp::IntCast, from, to));
                }
                if tw > fw {
                    out.push((ConvOp::Zext, from, to));
                    out.push((ConvOp::Sext, from, to));
                }
                if tw < fw {
                    out.push((ConvOp::Narrow, from, to));
                }
                if tw == fw && from != to {
                    out.push((ConvOp::Bitcast, from, to));
                }
            }
            for f in [Type::F32, Type::F64] {
                out.push((ConvOp::IntToFloat, from, f));
                out.push((ConvOp::FloatToInt, f, from));
            }
            out.push((ConvOp::BoolToInt, Type::Bool, from));
        }
        out.push((ConvOp::FloatCast, Type::F32, Type::F64));
        out.push((ConvOp::FloatCast, Type::F64, Type::F32));
        out.push((ConvOp::Bitcast, Type::F64, Type::U64));
        out.push((ConvOp::Bitcast, Type::U64, Type::F64));
        out.push((ConvOp::Bitcast, Type::F32, Type::I32));
        out.push((ConvOp::Bitcast, Type::I32, Type::F32));
        out.push((ConvOp::CharFromU32, Type::U32, Type::U32));
        out
    }

    fn conv_policies(op: ConvOp) -> Vec<Policy> {
        match op {
            ConvOp::IntCast => [Overflow::Error, Overflow::Wrap, Overflow::Trap]
                .into_iter()
                .map(Policy::overflow)
                .collect(),
            ConvOp::FloatToInt => [FloatToInt::Error, FloatToInt::Saturate]
                .into_iter()
                .map(Policy::float_to_int)
                .collect(),
            _ => std::vec![Policy::NONE],
        }
    }

    fn edges_of(ty: Type) -> Vec<u64> {
        if ty.is_float() {
            float_edges(ty)
        } else if ty == Type::Bool {
            std::vec![0, 1]
        } else {
            let mut e = int_edges(ty);
            e.extend([0xD7FF, 0xD800, 0xDFFF, 0xE000, 0x10_FFFF, 0x11_0000]);
            e.into_iter().map(|v| v & mask(ty)).collect()
        }
    }

    #[test]
    fn test_convert_agrees_with_interpreter_on_edges() {
        for (op, from, to) in conversions() {
            for p in conv_policies(op) {
                for a in edges_of(from) {
                    let ours = convert(op, p, from, to, a);
                    let theirs = interp::eval_convert(op, p, from, to, a);
                    assert!(
                        agrees(ours, theirs),
                        "{op:?} {p:?} {from:?}->{to:?} {a:#x}: {ours:?} vs {theirs:?}"
                    );
                    if ours == Fold::Unknown {
                        assert!(unknown_allowed(to, theirs), "{op:?} {from:?}->{to:?}");
                    }
                }
            }
        }
        assert_eq!(
            convert(ConvOp::PtrToInt, Policy::NONE, Type::Ptr, Type::U64, 0),
            Fold::Unknown
        );
    }

    #[test]
    fn test_error_kinds_follow_the_policy() {
        use ir_lang::{InstData, Value};
        let v = Value::from_u32(0);
        let div = InstData::Binary {
            op: BinaryOp::Div,
            policy: Policy::overflow(Overflow::Error).with_div_zero(DivZero::Error),
            args: [v, v],
        };
        assert_eq!(error_kinds(&div, Type::I64), (1 << 1) | (1 << 2));
        let ch = InstData::Convert {
            op: ConvOp::CharFromU32,
            policy: Policy::NONE,
            to: Type::U32,
            arg: v,
        };
        assert_eq!(error_kinds(&ch, Type::U32), 1 << 5);
        let wrap = InstData::Binary {
            op: BinaryOp::Add,
            policy: Policy::overflow(Overflow::Wrap),
            args: [v, v],
        };
        assert_eq!(error_kinds(&wrap, Type::I64), 0);
        let pow = InstData::Binary {
            op: BinaryOp::Pow,
            policy: Policy::overflow(Overflow::Trap),
            args: [v, v],
        };
        assert_eq!(error_kinds(&pow, Type::I32), 1 << 6);
        assert_eq!(error_kinds(&pow, Type::U32), 0);
        let sat = InstData::Binary {
            op: BinaryOp::Shr,
            policy: Policy::shift(Shift::Saturate),
            args: [v, v],
        };
        assert_eq!(error_kinds(&sat, Type::I8), 1 << 3);
        assert_eq!(error_kinds(&sat, Type::U8), 0);
    }

    /// `error_kinds` is non-empty exactly when ir-lang's placement rule says the
    /// operation can raise (so it needs a `check`), for every operation, every
    /// policy, and every operand type.
    #[test]
    fn test_error_kinds_match_can_error() {
        use ir_lang::{InstData, Value};
        let v = Value::from_u32(0);
        let all_types = INT_TYPES
            .iter()
            .copied()
            .chain([Type::F32, Type::F64, Type::Bool]);
        for ty in all_types {
            for &op in BinaryOp::ALL {
                for p in int_policies(op) {
                    let data = InstData::Binary {
                        op,
                        policy: p,
                        args: [v, v],
                    };
                    assert_eq!(
                        error_kinds(&data, ty) != 0,
                        op.can_error(p, ty),
                        "{op:?} {p:?} {ty:?}"
                    );
                }
            }
            for &op in UnaryOp::ALL {
                for o in [Overflow::Error, Overflow::Wrap, Overflow::Trap] {
                    let p = Policy::overflow(o);
                    let data = InstData::Unary {
                        op,
                        policy: p,
                        arg: v,
                    };
                    assert_eq!(error_kinds(&data, ty) != 0, op.can_error(p));
                }
            }
        }
        for (op, _, to) in conversions() {
            for p in conv_policies(op) {
                let data = InstData::Convert {
                    op,
                    policy: p,
                    to,
                    arg: v,
                };
                assert_eq!(
                    error_kinds(&data, Type::I64) != 0,
                    op.can_error(p),
                    "{op:?}"
                );
            }
        }
    }

    #[test]
    fn test_pow_and_saturate_fold_examples() {
        let wrap_p = Policy::overflow(Overflow::Wrap);
        let trap = Policy::overflow(Overflow::Trap);
        let m1 = wrap(Type::I32, -1);
        assert_eq!(
            binary(BinaryOp::Pow, wrap_p, Type::I32, 0, 0),
            Fold::Value(1)
        );
        assert_eq!(
            binary(BinaryOp::Pow, wrap_p, Type::I32, 3, 4),
            Fold::Value(81)
        );
        assert_eq!(
            binary(BinaryOp::Pow, trap, Type::I32, 2, m1),
            Fold::Error(OpError::NegativeExponent)
        );
        assert_eq!(
            binary(BinaryOp::Pow, trap, Type::I32, 2, 31),
            Fold::Trap(OpError::ArithOverflow)
        );
        assert_eq!(
            binary(BinaryOp::Pow, wrap_p, Type::U8, 2, 9),
            Fold::Value(0)
        );
        let sat = Policy::shift(Shift::Saturate);
        assert_eq!(
            binary(BinaryOp::Shr, sat, Type::I8, 0x80, 9),
            Fold::Value(0xff)
        );
        assert_eq!(
            binary(BinaryOp::Shl, sat, Type::I8, 0x7f, 72),
            Fold::Value(0)
        );
        assert_eq!(
            binary(BinaryOp::Shl, sat, Type::I8, 1, 0xff),
            Fold::Error(OpError::ShiftOutOfRange)
        );
        let two = 2.0f64.to_bits();
        assert_eq!(
            binary(
                BinaryOp::Pow,
                Policy::NONE,
                Type::F64,
                two,
                10.0f64.to_bits()
            ),
            Fold::Value(1024.0f64.to_bits())
        );
        // A NaN result is not folded (OPS lets the target choose the payload).
        let neg = (-8.0f64).to_bits();
        assert_eq!(
            binary(
                BinaryOp::Pow,
                Policy::NONE,
                Type::F64,
                neg,
                0.5f64.to_bits()
            ),
            Fold::Unknown
        );
    }

    /// Checks one partial fold against the interpreter for one hidden value.
    fn partial_agrees(
        p: Partial,
        op: BinaryOp,
        policy: Policy,
        ty: Type,
        a: u64,
        b: u64,
    ) -> Result<(), std::string::String> {
        let theirs = interp::eval_binary(op, policy, ty, a, b);
        let ok = match p {
            Partial::Always(f) => agrees(f, theirs) && f != Fold::Unknown,
            Partial::Operand(k) => theirs == Ok(if k == 0 { a } else { b }),
            Partial::Open { value, errors } => match theirs {
                Ok(r) => value.is_none_or(|v| v == r),
                Err(OpFault::Error(e)) => errors & bit(e) != 0,
                Err(_) => true,
            },
        };
        if ok {
            Ok(())
        } else {
            Err(std::format!(
                "{op:?} {policy:?} {ty:?} {a:#x} {b:#x}: {p:?} vs {theirs:?}"
            ))
        }
    }

    /// The partial fold is sound on the edge values: with one operand known,
    /// every value of the other agrees with what the fold claims.
    #[test]
    fn test_partial_agrees_with_interpreter_on_edges() {
        for &ty in &INT_TYPES {
            let edges = int_edges(ty);
            for &op in BinaryOp::ALL {
                if matches!(op, BinaryOp::IeeeRem | BinaryOp::TotalCmp) {
                    continue;
                }
                for p in int_policies(op) {
                    let none = binary_partial(op, p, ty, None, None);
                    for &k in &edges {
                        let left = binary_partial(op, p, ty, Some(k), None);
                        let right = binary_partial(op, p, ty, None, Some(k));
                        for &h in &edges {
                            partial_agrees(left, op, p, ty, k, h).unwrap();
                            partial_agrees(right, op, p, ty, h, k).unwrap();
                            partial_agrees(none, op, p, ty, h, k).unwrap();
                        }
                    }
                }
            }
        }
    }

    /// The OPS identities the passes rely on.
    #[test]
    fn test_partial_identities() {
        let wrap_p = Policy::overflow(Overflow::Wrap);
        let err = Policy::overflow(Overflow::Error);
        let one = Some(1);
        let pow = |p, ty, a, b| binary_partial(BinaryOp::Pow, p, ty, a, b);
        assert_eq!(pow(wrap_p, Type::I32, None, one), Partial::Operand(0));
        assert_eq!(
            pow(err, Type::I32, None, Some(0)),
            Partial::Always(Fold::Value(1))
        );
        assert_eq!(
            pow(wrap_p, Type::I32, None, Some(3)),
            Partial::Open {
                value: None,
                errors: 0
            }
        );
        assert_eq!(
            pow(err, Type::I32, None, Some(3)),
            Partial::Open {
                value: None,
                errors: bit(OpError::ArithOverflow)
            }
        );
        assert_eq!(
            pow(wrap_p, Type::I32, one, None),
            Partial::Open {
                value: Some(1),
                errors: bit(OpError::NegativeExponent)
            }
        );
        assert_eq!(
            pow(err, Type::U32, one, None),
            Partial::Always(Fold::Value(1))
        );
        let sat = Policy::shift(Shift::Saturate);
        assert_eq!(
            binary_partial(BinaryOp::Shl, sat, Type::I16, None, Some(40)),
            Partial::Always(Fold::Value(0))
        );
        assert_eq!(
            binary_partial(BinaryOp::Shr, sat, Type::I16, None, Some(40)),
            Partial::Open {
                value: None,
                errors: 0
            }
        );
        assert_eq!(
            binary_partial(BinaryOp::Shr, sat, Type::I16, None, Some(0xffff)),
            Partial::Always(Fold::Error(OpError::ShiftOutOfRange))
        );
    }

    fn any_int_type() -> impl Strategy<Value = Type> {
        proptest::sample::select(INT_TYPES.to_vec())
    }

    proptest! {
        #![proptest_config(ProptestConfig::with_cases(2048))]

        #[test]
        fn prop_int_binary_agrees(ty in any_int_type(), a in any::<u64>(), b in any::<u64>(), k in 0usize..64) {
            let (a, b) = (a & mask(ty), b & mask(ty));
            let ops = BinaryOp::ALL;
            let op = ops[k % ops.len()];
            prop_assume!(!matches!(op, BinaryOp::IeeeRem | BinaryOp::TotalCmp));
            for p in int_policies(op) {
                let ours = binary(op, p, ty, a, b);
                let theirs = interp::eval_binary(op, p, ty, a, b);
                prop_assert!(agrees(ours, theirs) && ours != Fold::Unknown);
            }
        }

        #[test]
        fn prop_partial_agrees(
            ty in any_int_type(),
            known in any::<u64>(),
            hidden in any::<u64>(),
            k in 0usize..64,
            left in any::<bool>(),
            small in any::<bool>(),
        ) {
            // Small known values (-1, 0, 1, 2, 3) hit the identities often.
            let known = if small { (known % 5).wrapping_sub(1) } else { known } & mask(ty);
            let hidden = hidden & mask(ty);
            let ops = BinaryOp::ALL;
            let op = ops[k % ops.len()];
            prop_assume!(!matches!(op, BinaryOp::IeeeRem | BinaryOp::TotalCmp));
            for p in int_policies(op) {
                let r = if left {
                    partial_agrees(binary_partial(op, p, ty, Some(known), None), op, p, ty, known, hidden)
                } else {
                    partial_agrees(binary_partial(op, p, ty, None, Some(known)), op, p, ty, hidden, known)
                };
                prop_assert!(r.is_ok(), "{}", r.err().unwrap_or_default());
            }
        }

        /// Integer `pow` agrees with the interpreter on small exponents and on
        /// bases near the overflow boundary, where random bits rarely land.
        #[test]
        fn prop_int_pow_agrees(ty in any_int_type(), base in -300i128..300, e in -3i128..70) {
            let (a, b) = (wrap(ty, base), wrap(ty, e));
            for p in int_policies(BinaryOp::Pow) {
                let ours = binary(BinaryOp::Pow, p, ty, a, b);
                let theirs = interp::eval_binary(BinaryOp::Pow, p, ty, a, b);
                prop_assert!(
                    agrees(ours, theirs) && ours != Fold::Unknown,
                    "{ty:?} {base} ** {e}: {ours:?} vs {theirs:?}"
                );
            }
        }

        #[test]
        fn prop_float_binary_agrees(a in any::<u64>(), b in any::<u64>(), k in 0usize..10, wide in any::<bool>()) {
            let ty = if wide { Type::F64 } else { Type::F32 };
            let (a, b) = (a & mask(ty), b & mask(ty));
            let op = [
                BinaryOp::Add, BinaryOp::Sub, BinaryOp::Mul, BinaryOp::Div, BinaryOp::Rem,
                BinaryOp::IeeeRem, BinaryOp::Min, BinaryOp::Max, BinaryOp::TotalCmp, BinaryOp::Pow,
            ][k];
            let ours = binary(op, Policy::NONE, ty, a, b);
            let theirs = interp::eval_binary(op, Policy::NONE, ty, a, b);
            prop_assert!(agrees(ours, theirs));
            if ours == Fold::Unknown {
                prop_assert!(unknown_allowed(ty, theirs));
            }
        }

        #[test]
        fn prop_float_unary_and_conversions_agree(a in any::<u64>(), k in 0usize..8, wide in any::<bool>(), t in any_int_type()) {
            let ty = if wide { Type::F64 } else { Type::F32 };
            let a = a & mask(ty);
            let op = [
                UnaryOp::Neg, UnaryOp::Abs, UnaryOp::Sqrt, UnaryOp::Floor,
                UnaryOp::Ceil, UnaryOp::Trunc, UnaryOp::Round, UnaryOp::RoundEven,
            ][k];
            let ours = unary(op, Policy::NONE, ty, a);
            let theirs = interp::eval_unary(op, Policy::NONE, ty, a);
            prop_assert!(agrees(ours, theirs));
            if ours == Fold::Unknown {
                prop_assert!(unknown_allowed(ty, theirs));
            }
            for p in conv_policies(ConvOp::FloatToInt) {
                let ours = convert(ConvOp::FloatToInt, p, ty, t, a);
                prop_assert!(agrees(ours, interp::eval_convert(ConvOp::FloatToInt, p, ty, t, a)));
                prop_assert!(ours != Fold::Unknown);
            }
            let other = if wide { Type::F32 } else { Type::F64 };
            let ours = convert(ConvOp::FloatCast, Policy::NONE, ty, other, a);
            prop_assert!(agrees(ours, interp::eval_convert(ConvOp::FloatCast, Policy::NONE, ty, other, a)));
        }

        #[test]
        fn prop_int_conversions_agree(from in any_int_type(), to in any_int_type(), a in any::<u64>()) {
            let a = a & mask(from);
            for (op, f, t) in conversions() {
                if f != from || t != to {
                    continue;
                }
                for p in conv_policies(op) {
                    let ours = convert(op, p, from, to, a);
                    prop_assert!(agrees(ours, interp::eval_convert(op, p, from, to, a)));
                    prop_assert!(ours != Fold::Unknown);
                }
            }
            for f in [Type::F32, Type::F64] {
                let ours = convert(ConvOp::IntToFloat, Policy::NONE, from, f, a);
                prop_assert!(agrees(ours, interp::eval_convert(ConvOp::IntToFloat, Policy::NONE, from, f, a)));
                prop_assert!(ours != Fold::Unknown);
            }
        }
    }
}
