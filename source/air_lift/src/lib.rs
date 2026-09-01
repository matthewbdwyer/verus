//! AirLift — lifts AIR-level representations back to source-level Verus/Rust.
//!
//! Consumes the observer interface (`AirObserver` + `VirObserver`) to accumulate
//! classification metadata during lowering, then lifts an AIR `Expr` into
//! [`lifted::LiftedExpr`] — a structured, source-level intermediate representation.
//! Lifting is *expression*-centric: how expressions are grouped or presented is a
//! consumer's concern.
//!
//! # Two rendering paths
//!
//! `LiftedExpr` has two independent lowerings, chosen by what the consumer needs:
//!
//! - [`render`] produces a compact, human-readable **display string** (for diagnostics
//!   and assertions). It reads like source but is not guaranteed to be legal, parseable
//!   Verus: a [`lifted::LiftedExpr::Opaque`] node emits its raw fallback text verbatim.
//! - [`syn_bridge`] produces a legal, precedence-correct `verus_syn::Expr` — an
//!   **injectable AST**, for generating Verus code to splice into a program.
//!
//! Both lower directly from `LiftedExpr` because their output guarantees differ, and
//! deriving either from the other is lossy or costly: a compact string from the AST
//! requires a bespoke pretty-printer, and an injectable AST from the string requires
//! re-parsing (which `Opaque` fragments do not support). Only the small precedence
//! model is common to both, so the overlap is deliberate and minimal.

pub mod types;
pub mod air_names;
pub mod expr_utils;
pub mod var_info;
pub mod lifted;
pub mod pipeline;
pub mod state;
pub mod roles;
pub mod lift;
pub mod accumulate;
pub mod render;
pub mod syn_bridge;

#[cfg(test)]
// Exercises the pure helpers in `air_names`, `expr_utils` and `var_info` from the crate
// root, so those modules stay free of test code.
mod tests {
    use crate::air_names::clean_air_name;
    use crate::expr_utils::expr_key;
    use crate::var_info::{parse_versioned, strip_to_base_with_at};
    use air::ast::{Constant, ExprX};
    use std::sync::Arc;

    #[test]
    fn expr_key_is_structural() {
        let t: air::ast::Expr = Arc::new(ExprX::Const(Constant::Bool(true)));
        assert_eq!(expr_key(&t), "true");
        let v1: air::ast::Expr = Arc::new(ExprX::Var(Arc::new("x".to_string())));
        let v2: air::ast::Expr = Arc::new(ExprX::Var(Arc::new("x".to_string())));
        assert_eq!(expr_key(&v1), "x");
        // Structural: equal structure ⇒ equal key (the dedup basis).
        assert_eq!(expr_key(&v1), expr_key(&v2));
    }

    #[test]
    fn versioned_name_parsing() {
        assert_eq!(parse_versioned("x@3"), ("x@", Some(3)));
        assert_eq!(parse_versioned("y"), ("y", None));
        assert_eq!(strip_to_base_with_at("x@3"), "x@");
        assert_eq!(strip_to_base_with_at("result@0"), "result@");
    }

    #[test]
    fn air_name_cleaning() {
        assert_eq!(clean_air_name("x@"), "x"); // strip local-stmt suffix
        assert_eq!(clean_air_name("y!"), "y"); // strip param suffix
    }
}
