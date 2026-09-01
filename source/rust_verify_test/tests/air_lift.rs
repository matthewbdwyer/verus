//! AirLift end-to-end capability tests.
//!
//! Each test runs a small Verus program under `-V observers=airlift-probe`, which
//! embeds an `air_lift::AirLift`, lifts the failing assertion's AIR expression, and
//! emits the rendered source-level goal as an `AIRLIFT:{"goals":[...]}` note. The
//! test asserts on that rendered goal — a focused, auditable oracle for one AirLift
//! capability.

#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

/// Extract the `AIRLIFT:` note payload from a failed verification.
fn airlift_note(err: &TestErr) -> String {
    err.notes
        .iter()
        .find_map(|n| {
            let t = n.rendered.strip_prefix("note: ").unwrap_or(&n.rendered);
            if t.starts_with("AIRLIFT:") {
                Some(t.to_string())
            } else {
                None
            }
        })
        .unwrap_or_else(|| {
            panic!(
                "AIRLIFT note not found; notes: {:?}",
                err.notes.iter().map(|n| n.rendered.clone()).collect::<Vec<_>>()
            )
        })
}

/// True if the AIRLIFT note contains `goal` as one of its rendered goals.
fn has_goal(note: &str, goal: &str) -> bool {
    note.contains(&format!("{:?}", goal))
}

test_verify_one_file_with_options! {
    #[test]
    airlift_intermediate ["observers=airlift-probe"] => verus_code! {
        fn f() {
            let mut x: u64 = 0;
            while x < 10 invariant x <= 10 decreases 10 - x { x = x + 1; }
            assert(x == 5);
        }
    } => Err(err) => {
        let note = airlift_note(&err);
        // The loop temporary is expanded, leaving the post-loop value comparison.
        assert!(has_goal(&note, "x == 5"), "E6 got: {}", note);
    }
}

test_verify_one_file_with_options! {
    #[test]
    airlift_mut_ref_final ["observers=airlift-probe"] => verus_code! {
        fn f(x: &mut u64) ensures *final(x) == 0 { *x = 5; }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "*final(x) == 0"), "E11 got: {}", note);
    }
}

test_verify_one_file_with_options! {
    #[test]
    airlift_closure_call ["observers=airlift-probe"] => verus_code! {
        use vstd::prelude::*;
        proof fn f(g: spec_fn(u64) -> bool) ensures call_ensures(g, (0,), true) { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(note.contains("call_ensures(g,"), "E12 got: {}", note);
    }
}

test_verify_one_file_with_options! {
    #[test]
    airlift_opaque ["observers=airlift-probe"] => verus_code! {
        fn f(x: u64) ensures (x & 1) == 0 { }
    } => Err(err) => {
        // A bitwise op has no LiftedExpr variant -> lift degrades to Opaque, so lifting
        // stays total (no panic) and a goal is still produced.
        let note = airlift_note(&err);
        assert!(note.contains("== 0"), "E16 got: {}", note);
    }
}

test_verify_one_file_with_options! {
    #[test]
    airlift_chained_comparison ["observers=airlift-probe"] => verus_code! {
        fn f(x: u64) ensures 10 <= x && x <= 20 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "10 <= x <= 20"), "E17 got: {}", note);
    }
}

test_verify_one_file_with_options! {
    #[test]
    airlift_clip ["observers=airlift-probe"] => verus_code! {
        fn f(x: u64) ensures (x as u32) == 0 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(
            !note.contains("clip") && !note.contains("Clip"),
            "clip: expected no clip noise, got: {}",
            note
        );
    }
}

test_verify_one_file_with_options! {
    #[test]
    airlift_variant_discriminant ["observers=airlift-probe"] => verus_code! {
        enum E { A, B }
        fn f(e: E) ensures matches!(e, E::A) { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "matches!(e, E::A)"), "E10 got: {}", note);
    }
}

test_verify_one_file_with_options! {
    #[test]
    airlift_precedence ["observers=airlift-probe"] => verus_code! {
        fn f(x: u64) ensures (x + 1) * 2 == 0 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "(x + 1) * 2 == 0"), "E15 got: {}", note);
    }
}

test_verify_one_file_with_options! {
    #[test]
    airlift_forall ["observers=airlift-probe"] => verus_code! {
        use vstd::prelude::*;
        proof fn f(s: Seq<u64>) ensures forall|i: int| #[trigger] s[i] == 0 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "forall|i: int| s[i] == 0"), "E11 got: {}", note);
    }
}

test_verify_one_file_with_options! {
    #[test]
    airlift_implies ["observers=airlift-probe"] => verus_code! {
        fn f(x: u64) ensures x > 100 ==> x < 50 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "x > 100 ==> x < 50"), "E12 got: {}", note);
    }
}

test_verify_one_file_with_options! {
    #[test]
    airlift_disjunction ["observers=airlift-probe"] => verus_code! {
        fn f(x: u64) ensures x > 100 || x < 50 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "x > 100 || x < 50"), "E13 got: {}", note);
    }
}

test_verify_one_file_with_options! {
    #[test]
    airlift_spec_call ["observers=airlift-probe"] => verus_code! {
        use vstd::prelude::*;
        spec fn g(x: u64) -> bool;
        proof fn f(x: u64) ensures g(x) { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "g(x)"), "E14 got: {}", note);
    }
}

test_verify_one_file_with_options! {
    #[test]
    airlift_field ["observers=airlift-probe"] => verus_code! {
        struct S { a: u64 }
        fn f(s: S) ensures s.a == 5 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "s.a == 5"), "E4 got: {}", note);
    }
}

test_verify_one_file_with_options! {
    #[test]
    airlift_len ["observers=airlift-probe"] => verus_code! {
        use vstd::prelude::*;
        proof fn f(s: Seq<u64>) ensures s.len() == 5 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "s.len() == 5"), "E2 got: {}", note);
    }
}

test_verify_one_file_with_options! {
    #[test]
    airlift_index ["observers=airlift-probe"] => verus_code! {
        use vstd::prelude::*;
        proof fn f(s: Seq<u64>) requires s.len() > 0 ensures s[0] == 0 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "s[0] == 0"), "E3 got: {}", note);
    }
}

test_verify_one_file_with_options! {
    #[test]
    airlift_equality ["observers=airlift-probe"] => verus_code! {
        fn f(x: u64) ensures x == 5 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "x == 5"), "E6 got: {}", note);
    }
}

test_verify_one_file_with_options! {
    #[test]
    airlift_ext_eq ["observers=airlift-probe"] => verus_code! {
        use vstd::prelude::*;
        proof fn f(s1: Seq<u64>, s2: Seq<u64>) ensures s1 =~= s2 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "s1 =~= s2"), "E7 got: {}", note);
    }
}

test_verify_one_file_with_options! {
    #[test]
    airlift_arith ["observers=airlift-probe"] => verus_code! {
        fn f(x: u64) ensures x + 1 == x { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "x + 1 == x"), "E8 got: {}", note);
    }
}

test_verify_one_file_with_options! {
    #[test]
    airlift_conjunction ["observers=airlift-probe"] => verus_code! {
        fn f(x: u64) ensures x > 100 && x < 50 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "x > 100 && x < 50"), "E9 got: {}", note);
    }
}

test_verify_one_file_with_options! {
    #[test]
    airlift_boolean ["observers=airlift-probe"] => verus_code! {
        fn f(b: bool) ensures b { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "b"), "E10 got: {}", note);
    }
}

test_verify_one_file_with_options! {
    // E1: a false `ensures x > 100` — the failing goal lifts to "x > 100".
    #[test]
    airlift_comparison ["observers=airlift-probe"] => verus_code! {
        fn f(x: u64)
            ensures x > 100
        {
        }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "x > 100"), "expected goal `x > 100`, got AIRLIFT note: {}", note);
    }
}

test_verify_one_file_with_options! {
    // E5: a &mut parameter's pre-state — false `ensures *old(x) > 100` exercises
    // Old + Deref classification (mut-ref old value). Full current/`final` mut-ref
    // is covered in T9.
    #[test]
    airlift_mut_ref_old ["observers=airlift-probe"] => verus_code! {
        fn f(x: &mut u64)
            ensures *old(x) > 100
        {
            *x = 0;
        }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(
            has_goal(&note, "*old(x) > 100"),
            "expected goal `*old(x) > 100`, got AIRLIFT note: {}",
            note
        );
    }
}


/// Extract an integer field from the AIRLIFT note.
fn airlift_count(note: &str, field: &str) -> usize {
    let key = format!("\"{}\":", field);
    let rest = &note[note.find(&key).expect("field present") + key.len()..];
    let end = rest.find(|c: char| !c.is_ascii_digit()).unwrap_or(rest.len());
    rest[..end].parse().expect("integer")
}

test_verify_one_file_with_options! {
    // The accumulated context a consumer reads back: function definitions gathered from
    // forall-equality axioms, and the current query's temporary definitions.
    #[test]
    airlift_accumulated_context ["observers=airlift-probe"] => verus_code! {
        use vstd::prelude::*;
        spec fn double(x: int) -> int { x + x }
        proof fn f(x: int) ensures double(x) == 0 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(
            airlift_count(&note, "defs") > 0,
            "expected accumulated function definitions, got: {}",
            note
        );
    }
}

test_verify_one_file_with_options! {
    // Bit operations read infix, as they do in source.
    #[test]
    airlift_bitwise_ops ["observers=airlift-probe"] => verus_code! {
        fn f(a: u32, b: u32) ensures ((a & b) | (a ^ b)) > 1000 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "a & b | a ^ b > 1000"),
            "bitwise got: {}", note);
    }
}

test_verify_one_file_with_options! {
    // A shift reads infix.
    #[test]
    airlift_shift ["observers=airlift-probe"] => verus_code! {
        fn f(n: u32) ensures (1u32 << n) == 0 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(note.contains("<<"), "shift got: {}", note);
    }
}

test_verify_one_file_with_options! {
    // A range invariant states bounds the type already implies; the value is what reads.
    #[test]
    airlift_range_invariant ["observers=airlift-probe"] => verus_code! {
        fn f(x: u64, y: u64) ensures x + y > 0 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(!note.contains("uInv") && !note.contains("iInv"),
            "range invariant should not appear: {}", note);
    }
}

test_verify_one_file_with_options! {
    // A decreases check compares the measure before and after.
    #[test]
    airlift_termination_check ["observers=airlift-probe"] => verus_code! {
        spec fn count(n: nat) -> nat decreases n { if n == 0 { 0 } else { count(n) + 1 } }
        proof fn f() ensures count(1) == 0 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(!note.contains("check_decrease"), "termination check should read as a comparison: {}", note);
    }
}

// ---- Coverage for behaviour a downstream consumer exposed ----
// Each of these renders a construct whose lifting was previously untested here, and was found to
// be missing or wrong only when a consumer with a large test suite rendered it.

test_verify_one_file_with_options! {
    // A tuple's positional field.
    #[test]
    airlift_tuple_field ["observers=airlift-probe"] => verus_code! {
        spec fn pair(x: int) -> (int, int);
        proof fn f(x: int) ensures pair(x).0 > 100 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "pair(x).0 > 100"), "got: {}", note);
    }
}

test_verify_one_file_with_options! {
    // Slicing from the start reads as `take`.
    #[test]
    airlift_slice_take ["observers=airlift-probe"] => verus_code! {
        use vstd::prelude::*;
        proof fn f(s: Seq<int>) requires s.len() > 3 ensures s.take(2).len() > 100 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "s.take(2).len() > 100"), "got: {}", note);
    }
}

test_verify_one_file_with_options! {
    // Slicing to the end reads as `skip`.
    #[test]
    airlift_slice_skip ["observers=airlift-probe"] => verus_code! {
        use vstd::prelude::*;
        proof fn f(s: Seq<int>) requires s.len() > 3 ensures s.skip(1).len() > 100 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "s.skip(1).len() > 100"), "got: {}", note);
    }
}

test_verify_one_file_with_options! {
    // A general slice keeps both bounds.
    #[test]
    airlift_slice_subrange ["observers=airlift-probe"] => verus_code! {
        use vstd::prelude::*;
        proof fn f(s: Seq<int>) requires s.len() > 5 ensures s.subrange(2, 4).len() > 100 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "s.subrange(2, 4).len() > 100"), "got: {}", note);
    }
}

test_verify_one_file_with_options! {
    // Set membership. The finite-to-infinite conversion is machinery and must not appear.
    #[test]
    airlift_set_membership ["observers=airlift-probe"] => verus_code! {
        use vstd::prelude::*;
        proof fn f(s: Set<int>, k: int) ensures s.contains(k) { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "s.contains(k)"), "got: {}", note);
        assert!(!note.contains("to_iset"), "conversion machinery leaked: {}", note);
    }
}

test_verify_one_file_with_options! {
    // Membership on a map's domain reads as a key test.
    #[test]
    airlift_map_membership ["observers=airlift-probe"] => verus_code! {
        use vstd::prelude::*;
        proof fn f(m: Map<int, int>, k: int) ensures m.contains_key(k) { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "m.contains_key(k)"), "got: {}", note);
        assert!(!note.contains("dom()"), "domain call leaked: {}", note);
    }
}

test_verify_one_file_with_options! {
    // A trait method reached through an impl block: the impl-block path must not appear.
    #[test]
    airlift_impl_method ["observers=airlift-probe"] => verus_code! {
        struct P { a: int }
        trait Val { spec fn val(&self) -> int; }
        impl Val for P { spec fn val(&self) -> int { self.a } }
        proof fn f(p: P) requires p.a > 0 ensures p.val() > 100 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "p.val() > 100"), "got: {}", note);
        assert!(!note.contains("impl&"), "impl-block path leaked: {}", note);
    }
}

test_verify_one_file_with_options! {
    // A tuple-struct constructor.
    #[test]
    airlift_tuple_struct_ctor ["observers=airlift-probe"] => verus_code! {
        struct W(int);
        proof fn f(x: int) ensures W(x).0 > 100 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "W(x).0 > 100"), "got: {}", note);
    }
}

test_verify_one_file_with_options! {
    // A constructor with named fields.
    #[test]
    airlift_struct_literal ["observers=airlift-probe"] => verus_code! {
        struct N { a: int, b: int }
        spec fn mk(x: int) -> N;
        proof fn f(x: int) ensures mk(x) == (N { a: 1, b: 2 }) { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "mk(x) == N { a: 1, b: 2 }"), "got: {}", note);
    }
}

test_verify_one_file_with_options! {
    // `Option::unwrap` reads as the method it is, rather than disappearing.
    #[test]
    airlift_option_unwrap ["observers=airlift-probe"] => verus_code! {
        use vstd::prelude::*;
        proof fn f(o: Option<int>) requires o is Some ensures o.unwrap() > 100 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "o.unwrap() > 100"), "got: {}", note);
    }
}

test_verify_one_file_with_options! {
    // A closure reads as a closure, with the application's arguments substituted for the
    // body's placeholders (a placeholder must not survive into the output).
    #[test]
    airlift_closure_body ["observers=airlift-probe"] => verus_code! {
        use vstd::prelude::*;
        proof fn f(s: Seq<int>) ensures s.map(|_i: int, x: int| x + 1) =~= s { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "s.map(|_i, x| x + 1) =~= s"), "got: {}", note);
        assert!(!note.contains("hole"), "placeholder leaked: {}", note);
        assert!(!note.contains("%%lambda%%"), "internal lambda name leaked: {}", note);
    }
}

test_verify_one_file_with_options! {
    // Bit complement.
    #[test]
    airlift_bit_complement ["observers=airlift-probe"] => verus_code! {
        fn f(x: u32) ensures !x == 0 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(note.contains("!x"), "got: {}", note);
    }
}

test_verify_one_file_with_options! {
    // Negation.
    #[test]
    airlift_negation ["observers=airlift-probe"] => verus_code! {
        proof fn f(x: int) ensures -x > 100 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(note.contains("-x"), "got: {}", note);
    }
}

test_verify_one_file_with_options! {
    // Nested quantifiers binding the same name: the inner binder is renamed in the encoding to
    // avoid the clash, and reads by its source name.
    #[test]
    airlift_binder_renaming ["observers=airlift-probe"] => verus_code! {
        use vstd::prelude::*;
        proof fn f(s: Seq<int>, t: Seq<int>)
            requires s.len() > 0, t.len() > 0,
            ensures
                forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==>
                    forall|i: int| #![trigger t[i]] 0 <= i < t.len() ==> s[i] + t[i] > 0
        { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(!note.contains("i$"), "renamed binder leaked: {}", note);
        assert!(note.matches("forall|i").count() >= 2, "both binders should read as `i`: {}", note);
    }
}

// ---- Hardening: additional variant coverage ----

test_verify_one_file_with_options! {
    // A real literal renders as itself.
    #[test]
    airlift_real_literal ["observers=airlift-probe"] => verus_code! {
        proof fn f(x: real) ensures x > 1.5 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(note.contains("1.5"), "real literal: {}", note);
    }
}

test_verify_one_file_with_options! {
    // Real division renders infix.
    #[test]
    airlift_real_division ["observers=airlift-probe"] => verus_code! {
        proof fn f(x: real, y: real) ensures x / y > 100.0 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "x / y > 100.0"), "real div: {}", note);
        assert!(!note.contains("RDiv"), "encoding leaked: {}", note);
    }
}

test_verify_one_file_with_options! {
    #[test]
    airlift_push_method ["observers=airlift-probe"] => verus_code! {
        use vstd::prelude::*;
        proof fn f(v: Seq<int>, x: int) ensures v.push(x).len() > 100 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "v.push(x).len() > 100"), "push: {}", note);
    }
}

test_verify_one_file_with_options! {
    #[test]
    airlift_map_insert ["observers=airlift-probe"] => verus_code! {
        use vstd::prelude::*;
        proof fn f(m: Map<int, int>, k: int, v: int) ensures m.insert(k, v).len() > 1000 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(note.contains("insert(k, v)"), "insert: {}", note);
    }
}

// ---- Coverage for examples features not yet tested ----

test_verify_one_file_with_options! {
    // A Ghost value reads as an ordinary variable (Ghost<T> is transparent in spec).
    #[test]
    airlift_ghost_var ["observers=airlift-probe"] => verus_code! {
        use vstd::prelude::*;
        proof fn f(x: Ghost<int>) ensures x@ > 100 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(note.contains("x") && note.contains("> 100"), "ghost var: {}", note);
    }
}

test_verify_one_file_with_options! {
    // The .view() method renders as a method call.
    #[test]
    airlift_view_method ["observers=airlift-probe"] => verus_code! {
        use vstd::prelude::*;
        fn f(v: Vec<u64>) ensures v.view().len() > 100 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(note.contains("v.view()") || note.contains("v@"),
            "view method: {}", note);
    }
}

test_verify_one_file_with_options! {
    // An assert ... by(nonlinear_arith) still lifts its goal on failure.
    #[test]
    airlift_assert_by ["observers=airlift-probe"] => verus_code! {
        proof fn f(x: int, y: int) requires x > 0, y > 0 {
            assert(x * y > x + y) by(nonlinear_arith)
                requires x > 0, y > 0
            {}
        }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(note.contains("x * y"), "assert-by goal: {}", note);
    }
}

// ---- Coverage for additional lifted shapes: nested field, `>=`, field-on-future ----

test_verify_one_file_with_options! {
    // Nested field access lifts as a two-level path `o.inner.z` (not just single-level).
    #[test]
    airlift_nested_field ["observers=airlift-probe"] => verus_code! {
        struct Inner { x: u64, z: u64 }
        struct Outer { inner: Inner }
        fn f(o: Outer) ensures o.inner.z == 5 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "o.inner.z == 5"), "nested field got: {}", note);
    }
}

test_verify_one_file_with_options! {
    // `>=` is kept (not canonicalized to `<=`), rendering as `>=`.
    #[test]
    airlift_ge_comparison ["observers=airlift-probe"] => verus_code! {
        fn f(x: u64) ensures x >= 100 { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "x >= 100"), "ge got: {}", note);
    }
}

test_verify_one_file_with_options! {
    // A field access on a `&mut` future value: `(*final(s)).b` — a field access whose receiver
    // is the deref of a future value `*final(..)`. (Field b is unchanged; a is assigned.)
    #[test]
    airlift_final_field ["observers=airlift-probe"] => verus_code! {
        struct S { a: u64, b: u64 }
        fn f(s: &mut S) ensures (*final(s)).b == 0 { s.a = 5; }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(has_goal(&note, "(*final(s)).b == 0"), "final field got: {}", note);
    }
}

test_verify_one_file_with_options! {
    // A call of a function *value* (`spec_fn`/closure parameter) must render as `g(x)`.
    #[test]
    airlift_spec_fn_value_call ["observers=airlift-probe"] => verus_code! {
        proof fn f(g: spec_fn(int) -> bool, x: int) ensures g(x) { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(note.contains("g(x)"), "spec_fn value call; got: {}", note);
        assert!(!note.contains("apply"), "apply-family encoding leaked; got: {}", note);
        assert!(note.contains("\"syn_ok\":true"), "to_syn must re-parse; got: {}", note);
    }
}

test_verify_one_file_with_options! {
    // A trait *associated* function that does not take `self` must render as a plain call
    // (`func(x)`), not method-call syntax (`x.func()`). `func` is a `closed spec fn`, so the call
    // stays opaque and the (unprovable) ensures fails with the call as the goal.
    #[test]
    airlift_trait_assoc_fn_not_method ["observers=airlift-probe"] => verus_code! {
        trait MyTrait { spec fn func(x: int) -> bool; }
        proof fn f<T: MyTrait>(x: int) ensures T::func(x) { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(!note.contains("x.func("), "must not be method-call syntax; got: {}", note);
        assert!(note.contains("func(x)"), "expected func(x) call syntax; got: {}", note);
    }
}

test_verify_one_file_with_options! {
    // A const generic `N` is encoded in AIR with a trailing type-parameter suffix
    // (`N&`). The lifted goal must recover the source name `N`, never leak `N&`.
    #[test]
    airlift_const_generic ["observers=airlift-probe"] => verus_code! {
        fn f<const N: usize>() {
            assert(N as int == 999);
        }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(!note.contains("N&"), "const-generic suffix leaked; got: {}", note);
        assert!(note.contains('N'), "expected the const generic N in the goal; got: {}", note);
    }
}

test_verify_one_file_with_options! {
    // A quantifier goal must lower through `to_syn` to a structural, re-parseable node that
    // carries the binder type (not the under-typed `forall|i|`, and not a whole-form `_`
    // collapse).
    #[test]
    airlift_to_syn_forall_structural ["observers=airlift-probe"] => verus_code! {
        spec fn p(i: int) -> bool;
        proof fn f() ensures forall|i: int| p(i) { }
    } => Err(err) => {
        let note = airlift_note(&err);
        assert!(note.contains("\"syn_ok\":true"), "to_syn did not re-parse: {}", note);
        assert!(note.contains("forall"), "to_syn lost the quantifier structure: {}", note);
        assert!(note.contains("int"), "to_syn dropped the binder type: {}", note);
    }
}
