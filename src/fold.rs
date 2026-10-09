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

use ir_lang::{
    BinaryOp, CmpOp, ConvOp, DivZero, FloatToInt, OpError, Overflow, Policy, Shift, Type, UnaryOp,
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
        _ => Fold::Unknown,
    }
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

/// The error kinds an operation can raise under its policy, as a bit set over
/// OPS codes (bit `k` for code `k`). Empty when it cannot raise.
pub(crate) fn error_kinds(data: &ir_lang::InstData) -> u32 {
    use ir_lang::InstData;
    let mut set = 0u32;
    let mut add = |e: OpError| set |= 1 << e.code();
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
            &[Some(Shift::Error), Some(Shift::Mask)]
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
        assert_eq!(error_kinds(&div), (1 << 1) | (1 << 2));
        let ch = InstData::Convert {
            op: ConvOp::CharFromU32,
            policy: Policy::NONE,
            to: Type::U32,
            arg: v,
        };
        assert_eq!(error_kinds(&ch), 1 << 5);
        let wrap = InstData::Binary {
            op: BinaryOp::Add,
            policy: Policy::overflow(Overflow::Wrap),
            args: [v, v],
        };
        assert_eq!(error_kinds(&wrap), 0);
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
        fn prop_float_binary_agrees(a in any::<u64>(), b in any::<u64>(), k in 0usize..9, wide in any::<bool>()) {
            let ty = if wide { Type::F64 } else { Type::F32 };
            let (a, b) = (a & mask(ty), b & mask(ty));
            let op = [
                BinaryOp::Add, BinaryOp::Sub, BinaryOp::Mul, BinaryOp::Div, BinaryOp::Rem,
                BinaryOp::IeeeRem, BinaryOp::Min, BinaryOp::Max, BinaryOp::TotalCmp,
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
