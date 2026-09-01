//! Lifecycle-scoped accumulation state for [`crate::accumulate::AirLift`].
//!
//! Each struct groups fields by their reset cadence:
//! - [`GlobalAnnotations`]: built once per krate (function roles, friendly names)
//! - [`FunctionState`]: reset per function (variable versioning events, binders)
//! - [`AirDecls`]: accumulated during AIR lowering (lambda/choose decls)
//! - [`QueryState`]: built per query (variable classification, tmp defs)


use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use air::ast::{Expr, Ident, Query};

use crate::expr_utils::DeclRhs;
use crate::types::{FunctionRole, SpanKind, VarInfo};

/// Global annotations built once from the full krate.
#[derive(Default)]
pub struct GlobalAnnotations {
    pub function_roles: HashMap<Ident, FunctionRole>,
    pub friendly_names: HashMap<Ident, String>,
    pub datatype_field_names: HashMap<Ident, String>,
    pub field_update_names: HashMap<Ident, String>,
    /// Return binding line numbers: AIR name of return param → source line.
    pub ret_binding_lines: HashMap<Ident, u32>,
    /// Rendered name of the crate under verification (e.g. "test_crate"),
    /// used to strip the crate prefix from friendly names so a same-crate
    /// call renders `double(x)` rather than `test_crate::double(x)`.
    pub current_crate: Option<String>,
}

/// Per-function state, reset on each `on_function_lowered`.
#[derive(Default)]
pub struct FunctionState {
    /// Ordered havoc events per variable (for cursor-based replay).
    pub havoc_events: HashMap<Ident, Vec<(u32, SpanKind)>>,
    /// Ordered assign events per variable (for cursor-based replay).
    pub assign_events: HashMap<Ident, Vec<(u32, SpanKind)>>,
    pub for_loop_var_map: HashMap<String, String>,
    pub reveal_strings: HashMap<Ident, Arc<String>>,
    pub binder_lines: HashMap<Ident, u32>,
    pub binder_decl_names: HashSet<Ident>,
    pub variable_def_lines: HashMap<Ident, u32>,
    pub assert_id_counter: u64,
    /// VIR-level type for each quantifier binder, keyed by AIR name. Recorded so that lifting
    /// can produce a typed binder (`forall|i: int|`) rather than an untyped one.
    pub binder_types: HashMap<Ident, vir::ast::Typ>,
}

/// AIR-level declarations accumulated across queries.
#[derive(Default)]
pub struct AirDecls {
    pub lambda_decls: HashMap<Ident, (Vec<Ident>, Expr)>,
    pub choose_binder_names: HashMap<Ident, Ident>,
    pub decls: HashMap<Ident, DeclRhs>,
}

/// Per-query state built in `on_query_lowered`.
#[derive(Clone)]
pub struct QueryState {
    pub var_info: HashMap<Ident, VarInfo>,
    pub tmp_defs: HashMap<Ident, Expr>,
    pub query: Query,
}
