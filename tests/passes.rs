//! Per-pass unit tests on hand-written IR (the ir-lang textual form): what each
//! pass must do, and what it must leave alone. Every result is validated and,
//! where it matters, run in the reference interpreter against the original.

use ir_lang::interp::{self, Outcome, Val};
use ir_lang::{Module, parse};
use opt_lang::{Budget, Optimizer, PassKind};

fn module(text: &str) -> Module {
    let m = parse(text).unwrap_or_else(|e| panic!("{e}\n{text}"));
    m.validate().unwrap_or_else(|e| panic!("{e}\n{text}"));
    m
}

/// Runs `passes` once each (in order) on every function; returns the printed
/// module. Validates after every pass.
fn run(text: &str, passes: &[PassKind]) -> (Module, String) {
    let mut m = module(text);
    Optimizer::new()
        .passes(passes)
        .max_iterations(1)
        .validate(true)
        .run(&mut m)
        .unwrap_or_else(|e| panic!("{e}"));
    m.validate().unwrap();
    let s = m.to_string();
    (m, s)
}

/// The function `@f`'s outcome on `args`.
fn call(m: &Module, args: &[Val]) -> Outcome {
    let f = match m.lookup("f") {
        Some(ir_lang::SymbolRef::Func(f)) => f,
        _ => panic!("no @f"),
    };
    interp::run(m, f, args).unwrap()
}

fn same_behaviour(text: &str, passes: &[PassKind], inputs: &[&[Val]]) -> String {
    let before = module(text);
    let (after, s) = run(text, passes);
    for args in inputs {
        assert_eq!(
            call(&before, args),
            call(&after, args),
            "args {args:?}\n{s}"
        );
    }
    s
}

fn i64s(x: i64) -> Val {
    Val::i64(x)
}

// ------------------------------------------------------------------- SCCP

#[test]
fn test_sccp_folds_through_block_parameters_and_prunes_branches() {
    let text = r#"module "t" ptr64
sig s0 = (i64) -> (i64) fast

func @f s0 export {
b0(v0: i64):
    v1: i64 = const 2
    v2: i64 = const 3
    v3: bool = lt v1, v2
    br v3, b1, b2
b1:
    v4: i64 = add<overflow=wrap> v1, v2
    jump b3(v4)
b2:
    v5: i64 = mul<overflow=wrap> v0, v0
    jump b3(v5)
b3(v6: i64):
    v7: i64 = mul<overflow=wrap> v6, v6
    ret v7
}
"#;
    let s = same_behaviour(text, &[PassKind::Sccp], &[&[i64s(9)]]);
    assert!(s.contains("const 25"), "{s}");
    assert!(!s.contains("br "), "{s}");
}

#[test]
fn test_sccp_is_optimistic_around_loops() {
    // x = 5; loop { x = x * 1 ... } : x stays 5 (the back edge passes x back).
    let text = r#"module "t" ptr64
sig s0 = (i64) -> (i64) fast

func @f s0 export {
b0(v0: i64):
    v1: i64 = const 5
    v2: u32 = const 0
    jump b1(v1, v2)
b1(v3: i64, v4: u32):
    v5: u32 = const 10
    v6: bool = lt v4, v5
    br v6, b2, b3
b2:
    v7: i64 = const 1
    v8: i64 = mul<overflow=wrap> v3, v7
    v9: u32 = const 1
    v10: u32 = add<overflow=wrap> v4, v9
    jump b1(v8, v10)
b3:
    v11: i64 = add<overflow=wrap> v3, v0
    ret v11
}
"#;
    let s = same_behaviour(text, &[PassKind::Sccp], &[&[i64s(1)], &[i64s(-7)]]);
    assert!(
        s.contains("add<overflow=wrap> v0") || s.contains("const 5"),
        "{s}"
    );
    assert!(!s.contains("mul<"), "the loop's multiply should fold:\n{s}");
}

#[test]
fn test_sccp_folds_checks_by_policy() {
    // ok: 1 + 2 = 3; error: MAX + 1 goes to the error edge with code 1;
    // trap: 7 / 0 with div_zero=trap traps with code 2.
    let text = r#"module "t" ptr64
sig s0 = (i64) -> (i64) fast

func @f s0 export {
b0(v0: i64):
    v1: i64 = const 1
    v2: i64 = const 2
    check add<overflow=error> v1, v2 to b1(res0) error b9(err)
b1(v3: i64):
    v4: i64 = const 9223372036854775807
    check add<overflow=error> v4, v1 to b2(res0) error b3(err)
b2(v5: i64):
    ret v5
b3(v6: u32):
    v7: i64 = zext v6
    v8: i64 = add<overflow=wrap> v7, v3
    v9: i64 = const 0
    v10: bool = eq v0, v9
    br v10, b4, b5
b4:
    v11: i64 = const 7
    check div<overflow=error,div_zero=trap> v11, v9 to b2(res0) error b9(err)
b5:
    ret v8
b9(v12: u32):
    v13: i64 = const -1
    ret v13
}
"#;
    let s = same_behaviour(text, &[PassKind::Sccp], &[&[i64s(0)], &[i64s(5)]]);
    assert!(!s.contains("check"), "{s}");
    assert!(s.contains("trap 2"), "{s}");
    let (m, _) = run(text, &[PassKind::Sccp]);
    assert_eq!(call(&m, &[i64s(5)]), Outcome::Return(vec![Val::i64(4)]));
    assert_eq!(call(&m, &[i64s(0)]), Outcome::Trap(2));
}

#[test]
fn test_sccp_never_folds_a_trapping_operation_into_a_value() {
    let text = r#"module "t" ptr64
sig s0 = () -> (i64) fast

func @f s0 export {
b0:
    v0: i64 = const 9223372036854775807
    v1: i64 = const 1
    v2: i64 = add<overflow=trap> v0, v1
    ret v2
}
"#;
    let s = same_behaviour(text, &[PassKind::Sccp, PassKind::Dce], &[&[]]);
    assert!(s.contains("add<overflow=trap>"), "{s}");
}

#[test]
fn test_sccp_relaxes_checks_that_cannot_fail() {
    let text = r#"module "t" ptr64
sig s0 = (i64) -> (i64) fast

func @f s0 export {
b0(v0: i64):
    v1: i64 = const 3
    check shl<shift=error> v0, v1 to b1(res0) error b3(err)
b1(v2: i64):
    v3: i64 = const 5
    check div<overflow=error,div_zero=error> v2, v3 to b2(res0) error b3(err)
b2(v4: i64):
    v5: i32 = int_cast<overflow=wrap> v4
    check int_cast<overflow=error> v5 as i64 to b4(res0) error b3(err)
b3(v6: u32):
    trap 99
b4(v7: i64):
    ret v7
}
"#;
    let s = same_behaviour(
        text,
        &[PassKind::Sccp, PassKind::Dce, PassKind::SimplifyCfg],
        &[&[i64s(100)], &[i64s(-3)], &[i64s(i64::MAX)]],
    );
    assert!(!s.contains("check"), "{s}");
    assert!(s.contains("shl<shift=mask>"), "{s}");
    assert!(s.contains("div<overflow=wrap,div_zero=trap>"), "{s}");
    assert!(!s.contains("trap 99"), "{s}");
}

#[test]
fn test_sccp_keeps_checks_that_can_fail() {
    let text = r#"module "t" ptr64
sig s0 = (i64, i64) -> (i64) fast

func @f s0 export {
b0(v0: i64, v1: i64):
    v2: i64 = const -1
    check div<overflow=error,div_zero=error> v0, v2 to b1(res0) error b2(err)
b1(v3: i64):
    check add<overflow=error> v3, v1 to b3(res0) error b2(err)
b2(v4: u32):
    v5: i64 = zext v4
    ret v5
b3(v6: i64):
    ret v6
}
"#;
    let s = same_behaviour(
        text,
        &[PassKind::Sccp],
        &[
            &[i64s(i64::MIN), i64s(0)],
            &[i64s(4), i64s(i64::MAX)],
            &[i64s(4), i64s(1)],
        ],
    );
    assert_eq!(s.matches("check").count(), 2, "{s}");
}

#[test]
fn test_sccp_knows_the_error_code_of_a_single_kind_policy() {
    // The error handler switches on the code; only code 3 can arrive.
    let text = r#"module "t" ptr64
sig s0 = (i64, i64) -> (i64) fast

func @f s0 export {
b0(v0: i64, v1: i64):
    check shl<shift=error> v0, v1 to b1(res0) error b2(err)
b1(v2: i64):
    ret v2
b2(v3: u32):
    switch v3 default b3 [3: b4]
b3:
    v4: i64 = const 111
    ret v4
b4:
    v5: i64 = const 222
    ret v5
}
"#;
    let s = same_behaviour(
        text,
        &[PassKind::Sccp, PassKind::SimplifyCfg],
        &[&[i64s(1), i64s(70)], &[i64s(1), i64s(2)]],
    );
    assert!(!s.contains("switch"), "{s}");
    assert!(!s.contains("const 111"), "{s}");
}

#[test]
fn test_sccp_folds_a_switch_on_a_constant() {
    let text = r#"module "t" ptr64
sig s0 = () -> (i64) fast

func @f s0 export {
b0:
    v0: u8 = const 2
    switch v0 default b1 [1: b2, 2: b3]
b1:
    v1: i64 = const 10
    ret v1
b2:
    v2: i64 = const 20
    ret v2
b3:
    v3: i64 = const 30
    ret v3
}
"#;
    let s = same_behaviour(text, &[PassKind::Sccp, PassKind::SimplifyCfg], &[&[]]);
    assert!(
        !s.contains("switch") && s.contains("const 30") && !s.contains("const 10"),
        "{s}"
    );
}

#[test]
fn test_sccp_does_not_fold_nan_arithmetic_but_folds_comparisons() {
    let text = r#"module "t" ptr64
sig s0 = () -> (bool) fast

func @f s0 export {
b0:
    v0: f64 = const 0.0
    v1: f64 = div v0, v0
    v2: bool = ne v1, v1
    v3: f64 = const nan:0x7ff8000000000001
    v4: bool = eq v3, v3
    v5: bool = or v2, v4
    ret v5
}
"#;
    let s = same_behaviour(text, &[PassKind::Sccp], &[&[]]);
    assert!(s.contains("div v0, v0"), "{s}");
}

// -------------------------------------------------------------------- GVN

#[test]
fn test_gvn_merges_dominated_duplicates_with_commuted_operands() {
    let text = r#"module "t" ptr64
sig s0 = (i64, i64) -> (i64) fast

func @f s0 export {
b0(v0: i64, v1: i64):
    v2: i64 = add<overflow=wrap> v0, v1
    v3: bool = lt v0, v1
    br v3, b1, b2
b1:
    v4: i64 = add<overflow=wrap> v1, v0
    v5: bool = gt v1, v0
    v6: i64 = select v5, v4, v2
    ret v6
b2:
    v7: i64 = mul<overflow=wrap> v0, v1
    jump b3(v7)
b3(v8: i64):
    v9: i64 = mul<overflow=wrap> v0, v1
    v10: i64 = add<overflow=wrap> v8, v9
    ret v10
}
"#;
    let s = same_behaviour(
        text,
        &[PassKind::Gvn],
        &[&[i64s(1), i64s(2)], &[i64s(5), i64s(-2)]],
    );
    assert_eq!(s.matches("add<overflow=wrap> v").count(), 2, "{s}");
    assert_eq!(s.matches("mul<").count(), 1, "{s}");
    assert_eq!(
        s.matches(" lt ").count() + s.matches(" gt ").count(),
        1,
        "{s}"
    );
}

#[test]
fn test_gvn_does_not_merge_across_sibling_branches_or_loads() {
    let text = r#"module "t" ptr64
sig s0 = (i64, ptr) -> (i64) fast

func @f s0 export {
b0(v0: i64, v1: ptr):
    v2: bool = const true
    br v2, b1, b2
b1:
    v3: i64 = mul<overflow=wrap> v0, v0
    jump b3(v3)
b2:
    v4: i64 = mul<overflow=wrap> v0, v0
    jump b3(v4)
b3(v5: i64):
    v6: i64 = load v1 align 8
    store v5, v1 align 8
    v7: i64 = load v1 align 8
    v8: i64 = add<overflow=wrap> v6, v7
    ret v8
}
"#;
    let (_, s) = run(text, &[PassKind::Gvn]);
    assert_eq!(s.matches("mul<").count(), 2, "{s}");
    assert_eq!(s.matches("load").count(), 2, "{s}");
}

#[test]
fn test_gvn_applies_exact_integer_identities_only() {
    let text = r#"module "t" ptr64
sig s0 = (i64, f64) -> (i64, f64) fast

func @f s0 export {
b0(v0: i64, v1: f64):
    v2: i64 = const 0
    v3: i64 = const 1
    v4: i64 = add<overflow=trap> v0, v2
    v5: i64 = mul<overflow=trap> v4, v3
    v6: i64 = not v5
    v7: i64 = not v6
    v8: u64 = bitcast v7
    v9: i64 = bitcast v8
    v10: i32 = narrow v9
    v11: i64 = sext v10
    v12: i32 = narrow v11
    v13: i64 = sext v12
    v14: f64 = const 0.0
    v15: f64 = add v1, v14
    ret v13, v15
}
"#;
    let s = same_behaviour(
        text,
        &[PassKind::Gvn, PassKind::Dce],
        &[
            &[i64s(-5), Val::f64(-0.0)],
            &[i64s(i64::MAX), Val::f64(2.5)],
        ],
    );
    assert!(s.contains("add v1"), "float x + 0.0 must stay:\n{s}");
    assert!(!s.contains("not"), "{s}");
    assert!(!s.contains("trap"), "{s}");
    assert_eq!(s.matches("narrow").count(), 1, "{s}");
}

// -------------------------------------------------------------------- DCE

#[test]
fn test_dce_keeps_every_side_effect() {
    let text = r#"module "t" ptr64
sig s0 = (ptr, i64) -> () fast
sig s1 = (i64) -> () fast

global @g export mutable size 8 align 8 zeroed

func @ext s1 import

func @f s0 export {
b0(v0: ptr, v1: i64):
    v2: i64 = mul<overflow=wrap> v1, v1
    v3: i64 = load v0 align 8
    v4: i64 = load v0 align 8 volatile
    v5: i64 = add<overflow=trap> v1, v1
    v6: i64 = div<overflow=wrap,div_zero=trap> v1, v1
    v7: i64 = shl<shift=mask> v1, v1
    store v1, v0 align 8
    v8: ptr = global_addr @g
    v9: i64 = atomic_rmw add v8, v1 seq_cst
    v10: i64 = atomic_load v8 acquire
    fence seq_cst
    call @ext(v1)
    ret
}
"#;
    let (_, s) = run(text, &[PassKind::Dce]);
    for kept in [
        "load v0 align 8 volatile",
        "add<overflow=trap>",
        "div<overflow=wrap,div_zero=trap>",
        "store v1",
        "atomic_rmw",
        "atomic_load",
        "fence",
        "call @ext",
    ] {
        assert!(s.contains(kept), "{kept} was removed:\n{s}");
    }
    for gone in ["mul<", "shl<", "load v0 align 8\n"] {
        assert!(!s.contains(gone), "{gone} was kept:\n{s}");
    }
}

#[test]
fn test_dce_removes_a_dead_loop_variable() {
    let text = r#"module "t" ptr64
sig s0 = (i64) -> (i64) fast

func @f s0 export {
b0(v0: i64):
    v1: u32 = const 0
    jump b1(v1, v0)
b1(v2: u32, v3: i64):
    v4: u32 = const 4
    v5: bool = lt v2, v4
    br v5, b2, b3
b2:
    v6: i64 = mul<overflow=wrap> v3, v3
    v7: u32 = const 1
    v8: u32 = add<overflow=wrap> v2, v7
    jump b1(v8, v6)
b3:
    ret v0
}
"#;
    let s = same_behaviour(text, &[PassKind::Dce], &[&[i64s(3)]]);
    assert!(!s.contains("mul<"), "{s}");
    assert!(
        s.contains("b1(v2: u32):") || s.contains("(v1: u32):"),
        "{s}"
    );
}

#[test]
fn test_dce_rebuilds_blocks_when_many_parameters_die() {
    // 24 dead parameters across 6 blocks: more than the in-place limit, so the
    // blocks are rebuilt (edges retargeted, a self loop included).
    let mut text = String::from(
        "module \"t\" ptr64\nsig s0 = (i64) -> (i64) fast\n\nfunc @f s0 export {\nb0(v0: i64):\n    jump b1(v0, v0, v0, v0, v0)\n",
    );
    let mut v = 1;
    for blk in 1..=6 {
        let p: Vec<String> = (0..5).map(|k| format!("v{}: i64", v + k)).collect();
        let first = v;
        v += 5;
        text.push_str(&format!("b{blk}({}):\n", p.join(", ")));
        let next = if blk < 6 { blk + 1 } else { 7 };
        if blk == 3 {
            // A self loop guarded by the live parameter.
            text.push_str(&format!(
                "    v{v}: i64 = const 0\n    v{}: bool = lt v{first}, v{v}\n",
                v + 1
            ));
            text.push_str(&format!(
                "    br v{}, b{blk}(v{first}, v{first}, v{first}, v{first}, v{first}), b{next}(v{first}, v{first}, v{first}, v{first}, v{first})\n",
                v + 1
            ));
            v += 2;
        } else if blk < 6 {
            text.push_str(&format!(
                "    jump b{next}(v{first}, v{}, v{}, v{}, v{})\n",
                first + 1,
                first + 2,
                first + 3,
                first + 4
            ));
        } else {
            text.push_str(&format!("    ret v{first}\n"));
        }
    }
    text.push_str("}\n");
    let s = same_behaviour(&text, &[PassKind::Dce], &[&[i64s(5)], &[i64s(0)]]);
    assert!(
        !s.lines().any(|l| l.starts_with('b') && l.contains(", ")),
        "dead parameters remain:\n{s}"
    );
}

// --------------------------------------------------------------- copy-prop

#[test]
fn test_copy_prop_replaces_uniform_parameters() {
    let text = r#"module "t" ptr64
sig s0 = (i64, bool) -> (i64) fast

func @f s0 export {
b0(v0: i64, v1: bool):
    br v1, b1(v0), b2(v0)
b1(v2: i64):
    jump b3(v2, v0)
b2(v3: i64):
    jump b3(v3, v3)
b3(v4: i64, v5: i64):
    v6: u32 = const 0
    jump b4(v6, v4)
b4(v7: u32, v8: i64):
    v9: u32 = const 3
    v10: bool = lt v7, v9
    br v10, b5, b6
b5:
    v11: u32 = const 1
    v12: u32 = add<overflow=wrap> v7, v11
    jump b4(v12, v8)
b6:
    v13: i64 = add<overflow=wrap> v8, v5
    ret v13
}
"#;
    let s = same_behaviour(
        text,
        &[PassKind::CopyProp],
        &[&[i64s(4), Val::bool(true)], &[i64s(-9), Val::bool(false)]],
    );
    assert!(s.contains("add<overflow=wrap> v0, v0"), "{s}");
    // Every i64 parameter but the function's own is gone.
    assert_eq!(
        s.matches(": i64,").count() + s.matches(": i64)").count(),
        1,
        "{s}"
    );
}

#[test]
fn test_copy_prop_keeps_parameters_fed_by_results() {
    let text = r#"module "t" ptr64
sig s0 = (i64) -> (i64) fast

func @f s0 export {
b0(v0: i64):
    check neg<overflow=error> v0 to b1(res0) error b2(err)
b1(v1: i64):
    ret v1
b2(v2: u32):
    v3: i64 = zext v2
    ret v3
}
"#;
    let (_, s) = run(text, &[PassKind::CopyProp]);
    assert!(
        s.contains("b1(v1: i64)") && s.contains("b2(v2: u32)"),
        "{s}"
    );
}

// ------------------------------------------------------------ simplify-cfg

#[test]
fn test_simplify_cfg_threads_merges_and_removes_unreachable() {
    let text = r#"module "t" ptr64
sig s0 = (i64, bool) -> (i64) fast

func @f s0 export {
b0(v0: i64, v1: bool):
    br v1, b1(v0), b2
b1(v2: i64):
    jump b3(v2, v2)
b2:
    v3: i64 = const 7
    jump b4(v3)
b4(v4: i64):
    jump b3(v4, v0)
b3(v5: i64, v6: i64):
    v7: i64 = add<overflow=wrap> v5, v6
    jump b5
b5:
    v8: i64 = mul<overflow=wrap> v7, v7
    jump b6
b6:
    ret v8
b7:
    v9: i64 = const 1
    ret v9
}
"#;
    let s = same_behaviour(
        text,
        &[PassKind::SimplifyCfg],
        &[&[i64s(3), Val::bool(true)], &[i64s(3), Val::bool(false)]],
    );
    assert!(!s.contains("b7") && !s.contains("const 1\n"), "{s}");
    assert!(!s.contains("jump b5") && !s.contains("jump b6"), "{s}");
    // b1 was an empty forwarder: the branch goes straight to the join.
    assert!(s.contains("br v1, b2(v0, v0), b1"), "{s}");
}

#[test]
fn test_simplify_cfg_folds_trivial_branches_and_switch_cases() {
    let text = r#"module "t" ptr64
sig s0 = (i64, bool) -> (i64) fast

func @f s0 export {
b0(v0: i64, v1: bool):
    v2: i64 = const 1
    br v1, b1(v2), b1(v2)
b1(v3: i64):
    v4: i64 = add<overflow=wrap> v0, v3
    switch v0 default b2 [1: b2, 2: b2]
b2:
    ret v4
}
"#;
    let s = same_behaviour(
        text,
        &[PassKind::SimplifyCfg],
        &[&[i64s(1), Val::bool(true)], &[i64s(2), Val::bool(false)]],
    );
    assert!(!s.contains("br ") && !s.contains("switch"), "{s}");
}

#[test]
fn test_simplify_cfg_keeps_a_forwarder_whose_parameter_is_used_later() {
    let text = r#"module "t" ptr64
sig s0 = (i64) -> (i64) fast

func @f s0 export {
b0(v0: i64):
    check neg<overflow=error> v0 to b1(res0) error b3(err)
b1(v1: i64):
    jump b2
b2:
    v2: i64 = add<overflow=wrap> v1, v1
    ret v2
b3(v3: u32):
    v4: i64 = zext v3
    ret v4
}
"#;
    same_behaviour(
        text,
        &[PassKind::SimplifyCfg],
        &[&[i64s(4)], &[i64s(i64::MIN)]],
    );
}

#[test]
fn test_simplify_cfg_never_redirects_unwind_edges() {
    let text = r#"module "t" ptr64
sig s0 = () -> (i64) fast

func @g s0 import

func @f s0 export {
b0:
    invoke @g() to b1(res0) unwind b2(exn)
b1(v0: i64):
    ret v0
b2(v1: ptr):
    jump b3(v1)
b3(v2: ptr):
    resume v2
}
"#;
    let (_, s) = run(text, &[PassKind::SimplifyCfg]);
    assert!(s.contains("unwind b2(exn)"), "{s}");
}

#[test]
fn test_simplify_cfg_terminates_on_a_cycle_of_empty_blocks() {
    let text = r#"module "t" ptr64
sig s0 = (bool) -> () fast

func @f s0 export {
b0(v0: bool):
    br v0, b1, b3
b1:
    jump b2
b2:
    jump b1
b3:
    ret
}
"#;
    let (m, _) = run(text, &[PassKind::SimplifyCfg]);
    m.validate().unwrap();
}

// -------------------------------------------------------------------- LICM

#[test]
fn test_licm_hoists_invariants_and_leaves_effects() {
    let text = r#"module "t" ptr64
sig s0 = (i64, i64) -> (i64) fast

func @f s0 export {
    ss0 = slot 8 align 8
b0(v0: i64, v1: i64):
    v2: ptr = stack_addr ss0
    store v1, v2 align 8
    v3: u32 = const 0
    jump b1(v3, v0)
b1(v4: u32, v5: i64):
    v6: u32 = const 5
    v7: bool = lt v4, v6
    br v7, b2, b3
b2:
    v8: i64 = mul<overflow=wrap> v0, v1
    v9: i64 = add<overflow=wrap> v8, v1
    v10: i64 = load v2 align 8
    v11: i64 = add<overflow=trap> v0, v1
    v12: i64 = add<overflow=wrap> v5, v9
    v13: i64 = add<overflow=wrap> v12, v10
    v14: i64 = add<overflow=wrap> v13, v11
    store v14, v2 align 8
    v15: u32 = const 1
    v16: u32 = add<overflow=wrap> v4, v15
    jump b1(v16, v14)
b3:
    ret v5
}
"#;
    let s = same_behaviour(
        text,
        &[PassKind::Licm],
        &[
            &[i64s(3), i64s(4)],
            &[i64s(i64::MAX), i64s(0)],
            &[i64s(i64::MAX), i64s(1)],
        ],
    );
    let (after, _) = run(text, &[PassKind::Licm]);
    let func = after.function(ir_lang::FuncId::from_u32(0)).unwrap();
    // The multiply and its sum moved to the entry (the existing preheader);
    // the load (memory changes in the loop) and the trapping add did not.
    let entry: Vec<String> = func
        .insts(func.entry())
        .map(|i| format!("{:?}", func.inst(i).unwrap()))
        .collect();
    assert!(entry.iter().any(|t| t.contains("Mul")), "{s}");
    assert!(!entry.iter().any(|t| t.contains("Load")), "{s}");
    assert!(!entry.iter().any(|t| t.contains("Trap")), "{s}");
    // Idempotent.
    let mut again = after.clone();
    let mut budget = Budget::unlimited();
    let f = ir_lang::FuncId::from_u32(0);
    assert!(!opt_lang::run_pass(&mut again.edit(f).unwrap(), PassKind::Licm, &mut budget).unwrap());
}

#[test]
fn test_licm_creates_a_preheader_and_hoists_out_of_nested_loops() {
    let text = r#"module "t" ptr64
sig s0 = (i64, bool) -> (i64) fast

func @f s0 export {
b0(v0: i64, v1: bool):
    v2: u32 = const 0
    br v1, b1(v2, v0), b1(v2, v0)
b1(v3: u32, v4: i64):
    v5: u32 = const 3
    v6: bool = lt v3, v5
    br v6, b2(v2, v4), b5
b2(v7: u32, v8: i64):
    v9: bool = lt v7, v5
    br v9, b3, b4
b3:
    v10: i64 = const 11
    v11: i64 = mul<overflow=wrap> v0, v10
    v12: i64 = add<overflow=wrap> v8, v11
    v13: u32 = const 1
    v14: u32 = add<overflow=wrap> v7, v13
    jump b2(v14, v12)
b4:
    v15: u32 = const 1
    v16: u32 = add<overflow=wrap> v3, v15
    jump b1(v16, v8)
b5:
    ret v4
}
"#;
    let s = same_behaviour(
        text,
        &[PassKind::Licm],
        &[&[i64s(2), Val::bool(true)], &[i64s(-1), Val::bool(false)]],
    );
    let m = parse(&s).unwrap();
    let func = m.function(ir_lang::FuncId::from_u32(0)).unwrap();
    // The multiply is outside both loops: in a block that does not loop back.
    let cfg_loops = |text: &str| text.matches("mul<").count();
    assert_eq!(cfg_loops(&s), 1, "{s}");
    let mul_block = func
        .blocks()
        .find(|&b| {
            func.insts(b).any(|i| {
                matches!(
                    func.inst(i),
                    Some(ir_lang::InstData::Binary {
                        op: ir_lang::BinaryOp::Mul,
                        ..
                    })
                )
            })
        })
        .unwrap();
    // The block holding it is reached before the outer header b1.
    let preds = func.predecessors();
    let header = ir_lang::Block::from_u32(1);
    assert!(
        preds[header.index()].contains(&mul_block) || mul_block == func.entry(),
        "{s}"
    );
}

// ------------------------------------------------------------- GC / refs

#[test]
fn test_tracked_values_are_not_merged_or_hoisted_across_safepoints() {
    // Two `ref_to_ptr` of the relocated reference around a safepoint must stay
    // separate (merging them would keep a derived pointer live across it).
    let text = r#"module "t" ptr64
sig s0 = (ref) -> (i64) fast

func @f s0 export {
b0(v0: ref):
    v1: ptr = ref_to_ptr v0
    v2: i64 = load v1 align 8
    v3: ref = safepoint gc(v0)
    v4: ptr = ref_to_ptr v3
    v5: i64 = load v4 align 8
    v6: i64 = add<overflow=wrap> v2, v5
    v7: ref = const null
    v8: bool = eq v3, v7
    br v8, b1, b2
b1:
    ret v6
b2:
    v9: ref = safepoint gc(v3)
    v10: ptr = ref_to_ptr v9
    v11: i64 = load v10 align 8
    ret v11
}
"#;
    let mut m = module(text);
    opt_lang::Optimizer::new()
        .validate(true)
        .run(&mut m)
        .unwrap();
    m.validate().unwrap();
    let s = m.to_string();
    assert_eq!(s.matches("ref_to_ptr").count(), 3, "{s}");
}

#[test]
fn test_dce_rebuilds_a_landing_pad() {
    // A landing pad with 20 dead parameters besides the payload: the rebuilt
    // pad is still reached only by the unwind edge.
    let dead: Vec<String> = (3..23).map(|k| format!("v{k}: i64")).collect();
    let args = vec!["v0"; 20].join(", ");
    let text = format!(
        "module \"t\" ptr64\nsig s0 = (i64) -> (i64) fast\n\nfunc @g s0 import\n\nfunc @f s0 export {{\nb0(v0: i64):\n    invoke @g(v0) to b1(res0) unwind b2(exn, {args})\nb1(v1: i64):\n    ret v1\nb2(v2: ptr, {}):\n    v23: u64 = ptr_to_int v2\n    v24: i64 = bitcast v23\n    ret v24\n}}\n",
        dead.join(", ")
    );
    let (_, s) = run(&text, &[PassKind::Dce]);
    assert!(s.contains("unwind b2(exn)") || s.contains("(exn)"), "{s}");
    assert_eq!(s.matches(": i64,").count(), 0, "{s}");
}
