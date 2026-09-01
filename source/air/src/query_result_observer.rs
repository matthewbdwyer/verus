//! Query-result observer.
//!
//! Defines `QueryResultObserver` — the interface for observing the outcome of
//! each verification query (`Invalid` / `Valid` / `Timeout`), including live
//! model evaluation on `Invalid`.
//!
//! This trait is independent: it does **not** require `AirObserver` or
//! `VirObserver`. A consumer that only cares about verification outcomes
//! implements this trait alone.
//!
//! **`Invalid` is an interactive, live-window callback** — the one deliberate
//! exception to "observers are passive." Alongside the counterexample model
//! (`model_defs`), it hands the observer `eval_bool_expr`, a closure that
//! evaluates a boolean AIR expression against the *live* Z3 model. The model is
//! only valid for the duration of the callback: the core discovers the failing
//! assertion, invokes the observer, and only then disables the assertion label
//! (which invalidates the model). See the Phase 1/2/3 structure in
//! `smt_verify.rs`.

use crate::ast::{Expr, Ident};
use crate::messages::ArcDynMessage as Message;
use crate::model::ModelDef;
use std::any::Any;
use std::collections::HashMap;

/// Verification result passed to the observer after each query.
pub enum CheckValidResult<'a> {
    Invalid {
        /// The parsed Z3 counterexample model (concrete symbol assignments).
        /// Built by the core for its own error reporting; exposed here for free.
        model_defs: &'a HashMap<Ident, ModelDef>,
        /// Evaluate a boolean AIR expression against the live Z3 model.
        /// Returns `Some(bool)` for a boolean result, `None` for a non-boolean
        /// expression or one the model cannot evaluate. Valid only during this
        /// callback (the model is torn down afterward).
        eval_bool_expr: &'a mut dyn FnMut(&Expr) -> Option<bool>,
        assert_id: &'a Option<crate::ast::AssertId>,
        error: &'a Message,
    },
    Valid,
    Timeout {
        assert_id: &'a Option<crate::ast::AssertId>,
    },
}

/// Observer for verification query results.
///
/// The single callback fires once per query after the solver returns. All
/// methods except `as_any`/`as_any_mut` have default no-op implementations.
pub trait QueryResultObserver: Any {
    /// A verification query completed with a result.
    fn on_check_valid_result(&mut self, _result: &mut CheckValidResult) {}

    fn as_any(&self) -> &dyn Any;
    fn as_any_mut(&mut self) -> &mut dyn Any;
}
