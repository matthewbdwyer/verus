//! `AirLift` — the accumulation observer.
//!
//! Records information during AIR/VIR lowering — variable versioning, function-role
//! classification (via `crate::roles`), lambda/choose declarations, reveal strings and
//! binder lines — into lifecycle-scoped state, and exposes `pipeline_context()` to give
//! the lifter a `PipelineContext` for the most recent query.
//!
//! Accumulation only: reacting to a query's *result* is a consumer's concern, so this
//! type implements `AirObserver` and `VirObserver` but not `QueryResultObserver`.

use std::collections::HashMap;
use std::sync::Arc;

use air::air_observer::AirObserver;
use air::ast::{AssertId, Expr, Ident, Query, Snapshots};
use vir::ast::{Krate, Typ, VarBinder, VarIdent};
use vir::def::NameCtxt;
use vir::sst::{Exp, ExpX, Stm, StmX};
use vir::vir_observer::{AssertIdKind, VersionCorrelator, VirObserver, line_from_span};

use crate::air_names::{VERUS_GHOST_ITER, VERUS_LOOP_NEXT};
use crate::pipeline::{PipelineContext, collect_tmp_defs_from_stmt};
use crate::roles::build_global_annotations;
use crate::state::{AirDecls, FunctionState, GlobalAnnotations, QueryState};
use crate::types::SpanKind;

/// Accumulates lowering metadata for the lifter. One instance per verification run.
pub struct AirLift {
    pub global: GlobalAnnotations,
    per_function: FunctionState,
    /// Saved per-function state from the most recent `on_function_lowered`
    /// (VIR lowers a function before AIR processes its queries).
    saved_per_function: FunctionState,
    air_decls: AirDecls,
    per_query: Option<QueryState>,
    correlator: VersionCorrelator,
    versioned_span_map: HashMap<Ident, (u32, SpanKind)>,
    version_cursors: HashMap<Ident, usize>,
}

impl Default for AirLift {
    fn default() -> Self {
        Self::new()
    }
}

impl AirLift {
    pub fn new() -> Self {
        Self {
            global: GlobalAnnotations::default(),
            per_function: FunctionState::default(),
            saved_per_function: FunctionState::default(),
            air_decls: AirDecls::default(),
            per_query: None,
            correlator: VersionCorrelator::new(),
            versioned_span_map: HashMap::new(),
            version_cursors: HashMap::new(),
        }
    }

    /// Build the `PipelineContext` for the most recently lowered query — the
    /// input the lifter reads to classify names and applications.
    pub fn pipeline_context(&self) -> PipelineContext {
        PipelineContext {
            function_roles: self.global.function_roles.clone(),
            friendly_names: self.global.friendly_names.clone(),
            variable_info: self.per_query.as_ref().map(|q| q.var_info.clone()).unwrap_or_default(),
            for_loop_var_map: self.saved_per_function.for_loop_var_map.clone(),
            reveal_strings: self.saved_per_function.reveal_strings.clone(),
            binder_lines: self.saved_per_function.binder_lines.clone(),
            binder_decl_names: self.saved_per_function.binder_decl_names.clone(),
            variable_def_lines: self.saved_per_function.variable_def_lines.clone(),
            choose_binder_names: self.air_decls.choose_binder_names.clone(),
            lambda_decls: self.air_decls.lambda_decls.clone(),
            datatype_field_names: self.global.datatype_field_names.clone(),
            field_update_names: self.global.field_update_names.clone(),
            binder_types: self.saved_per_function.binder_types.clone(),
            current_crate: self.global.current_crate.clone(),
        }
    }

    /// Function definitions accumulated from `forall`-equality axioms, keyed by function
    /// name: the binders and the body. A consumer that expands or inlines function
    /// applications needs these.
    pub fn definitions(&self) -> &HashMap<Ident, crate::expr_utils::DeclRhs> {
        &self.air_decls.decls
    }

    /// Temporary definitions collected from the most recent query, keyed by temporary name.
    /// [`Self::lift`] applies these itself; a consumer that works on the raw AIR query
    /// (before lifting) needs them directly.
    pub fn current_tmp_defs(&self) -> Option<&HashMap<Ident, Expr>> {
        self.per_query.as_ref().map(|q| &q.tmp_defs)
    }

    /// The most recently lowered query (whose assertion the consumer lifts on failure).
    pub fn current_query(&self) -> Option<&Query> {
        self.per_query.as_ref().map(|q| &q.query)
    }

    /// Lift an expression in the context of the most recently lowered query: expand the
    /// query's temporary definitions, `normalize`, then classify (`lift_expr`).
    ///
    /// The entry point for a consumer that has observed a verification run. It is
    /// *expression*-centric: how expressions are grouped or presented is the consumer's
    /// concern.
    ///
    /// Without an observed query there is no context to consult, so this degrades — no
    /// temporary expansion, no variable classification — rather than panicking. A caller
    /// with no query context should instead use [`crate::lift::lift_expr`] directly,
    /// supplying its own `PipelineContext`.
    pub fn lift(&self, expr: &Expr) -> crate::lifted::LiftedExpr {
        debug_assert!(
            self.per_query.is_some(),
            "AirLift::lift called with no current query; use lift_expr for context-less lifting"
        );
        let ctx = self.pipeline_context();
        let expanded = match &self.per_query {
            Some(q) => crate::pipeline::expand_temporaries(&q.tmp_defs, expr),
            None => expr.clone(),
        };
        let normalized = ctx.normalize(&expanded);
        crate::lift::lift_expr(&normalized, &ctx)
    }
}

impl AirObserver for AirLift {
    fn on_query_lowered(
        &mut self,
        query: &Query,
        snapshots: &Snapshots,
        __local_vars: &[air::ast::Decl],
    ) {
        tracing::debug!(versioned_span_map_len = self.versioned_span_map.len(), "on_query_lowered");
        // Build span_map for var_info from per-version entries only.
        // Version 0 has no on_wp_version_created callback — it gets its line
        // from variable_def_lines via lookup_span fallback (the let-binding site).
        let mut span_map_for_var_info: HashMap<Ident, (u32, crate::types::SpanKind)> =
            HashMap::new();
        for (k, (line, kind)) in self.versioned_span_map.drain() {
            span_map_for_var_info.insert(k, (line, kind));
        }

        // Determine version 0's line for loop-entry variables.
        // In loop maintenance queries: on_wp_version_created fires for the body
        // assign (Assign-origin), NOT for the loop-entry havoc. Version 0 IS the
        // havoc. Detect this: Havoc cursor == 0 AND Assign cursor > 0.
        // In main body queries: on_wp_version_created fires for havocs (Havoc-origin).
        // Version 0 is the let-binding. Havoc cursor > 0 means we DON'T use havoc line.
        for (base, events) in self.saved_per_function.havoc_events.iter() {
            let havoc_cursor_key = Arc::new(format!("H:{}", base));
            let assign_cursor_key = Arc::new(format!("A:{}", base));
            let havoc_cursor = self.version_cursors.get(&havoc_cursor_key).copied().unwrap_or(0);
            let assign_cursor = self.version_cursors.get(&assign_cursor_key).copied().unwrap_or(0);
            // Loop maintenance query: no Havoc callbacks but Assign callbacks fired
            if havoc_cursor == 0 && assign_cursor > 0 {
                if let Some(&(line, kind)) = events.first() {
                    let v0_key = Arc::new(format!("{}0", base));
                    span_map_for_var_info.entry(v0_key).or_insert((line, kind));
                }
            }
        }

        let mut var_info = crate::var_info::build_var_info(
            query,
            snapshots,
            &span_map_for_var_info,
            &self.saved_per_function.binder_lines,
            &self.saved_per_function.variable_def_lines,
        );
        // Merge global ret_binding_lines into variable_def_lines for disambiguation
        let mut var_def_lines = self.saved_per_function.variable_def_lines.clone();
        for (k, v) in self.global.ret_binding_lines.iter() {
            var_def_lines.entry(k.clone()).or_insert(*v);
        }
        crate::var_info::disambiguate_var_info(
            &mut var_info,
            &var_def_lines,
            &self.saved_per_function.binder_lines,
            &self.saved_per_function.binder_decl_names,
        );
        let mut tmp_defs = HashMap::new();
        collect_tmp_defs_from_stmt(&query.assertion, &mut tmp_defs);
        tracing::debug!(
            span_map = span_map_for_var_info.len(),
            var_info = var_info.len(),
            tmp_defs = tmp_defs.len(),
            "on_query_lowered summary"
        );
        let qs = QueryState { var_info, tmp_defs, query: query.clone() };

        self.per_query = Some(qs);
        // Reset cursors so the next query's on_wp_version_created calls start fresh.
        self.version_cursors.clear();
    }

    fn on_wp_version_created(&mut self, versioned: &Ident, kind: air::air_observer::VersionOrigin) {
        use air::air_observer::VersionOrigin;

        match kind {
            VersionOrigin::Havoc | VersionOrigin::Assign => {
                let base = crate::var_info::strip_to_base_with_at(versioned.as_str());
                let base_key: Ident = std::sync::Arc::new(base.to_string());
                // Use kind-specific cursor and event list
                let cursor_key = match kind {
                    VersionOrigin::Havoc => std::sync::Arc::new(format!("H:{}", base)),
                    _ => std::sync::Arc::new(format!("A:{}", base)),
                };
                let cursor = self.version_cursors.entry(cursor_key).or_insert(0);
                let events = match kind {
                    VersionOrigin::Havoc => self.saved_per_function.havoc_events.get(&base_key),
                    _ => self.saved_per_function.assign_events.get(&base_key),
                };
                if let Some(events) = events {
                    if let Some(&(line, span_kind)) = events.get(*cursor) {
                        self.versioned_span_map.insert(versioned.clone(), (line, span_kind));
                    }
                }
                *cursor += 1;
            }
            VersionOrigin::BranchMerge | VersionOrigin::BreakMerge => {
                if let Some(stm) = self.correlator.resolve(versioned, kind) {
                    if let Some(line) = line_from_span(&stm.span) {
                        self.versioned_span_map
                            .insert(versioned.clone(), (line, crate::types::SpanKind::Other));
                    }
                }
                return;
            }
        }

        // Drain the correlator queue to keep it in sync
        let _ = self.correlator.resolve(versioned, kind);
    }

    fn on_lambda_decl(&mut self, name: &Ident, params: &[Ident], body: &Expr) {
        self.air_decls.lambda_decls.insert(name.clone(), (params.to_vec(), body.clone()));
    }

    fn on_choose_decl(&mut self, name: &Ident, binder_name: &Ident) {
        self.air_decls.choose_binder_names.insert(name.clone(), binder_name.clone());
    }

    fn on_axiom_decl(&mut self, expr: &Expr) {
        // Accumulate forall-eq axioms as function definitions for inlining
        if let air::ast::ExprX::Bind(bind, inner) = &**expr
            && let air::ast::BindX::Quant(air::ast::Quant::Forall, binders, _, _) = &**bind
            && let air::ast::ExprX::Binary(air::ast::BinaryOp::Eq, lhs, rhs) = &**inner
            && let air::ast::ExprX::Apply(fname, _) = &**lhs
        {
            self.air_decls.decls.insert(fname.clone(), (binders.clone(), rhs.clone()));
        }
    }

    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }
}

impl VirObserver for AirLift {
    fn on_krate(&mut self, krate: &Krate, name_ctxt: &NameCtxt, current_crate: &vir::ast::CrateId) {
        self.global = build_global_annotations(krate, name_ctxt, current_crate);
    }

    fn on_havoc(&mut self, stm: &Stm, var: &VarIdent) {
        let air_name = vir::def::suffix_local_unique_id(var);
        if let Some(line) = line_from_span(&stm.span) {
            self.per_function
                .havoc_events
                .entry(air_name.clone())
                .or_default()
                .push((line, SpanKind::LoopEntry));
        }
        self.correlator.record_havoc_or_assign(&air_name, stm);
    }

    fn on_assign(&mut self, stm: &Stm, var: &VarIdent) {
        let air_name = vir::def::suffix_local_unique_id(var);
        if let Some(line) = line_from_span(&stm.span) {
            self.per_function
                .assign_events
                .entry(air_name.clone())
                .or_default()
                .push((line, SpanKind::Other));
        }
        self.correlator.record_havoc_or_assign(&air_name, stm);
    }

    fn on_variable_def(&mut self, stm: &Stm, var: &VarIdent) {
        let air_name = vir::def::suffix_local_unique_id(var);
        if let Some(line) = line_from_span(&stm.span) {
            self.per_function.variable_def_lines.insert(air_name, line);
        }
    }

    fn on_branch_merge(&mut self, stm: &Stm) {
        self.correlator.record_branch_merge(stm);
    }

    fn on_break_merge(&mut self, stm: &Stm) {
        self.correlator.record_break_merge(stm);
    }

    fn on_for_loop(&mut self, stm: &Stm) {
        if let Some((ghost_key, user_var)) = extract_for_loop_var_info(stm) {
            self.per_function.for_loop_var_map.insert(ghost_key, user_var);
        }
    }

    fn on_quantifier_binder(&mut self, binder: &VarBinder<Typ>, exp: &Exp) {
        let air_name = vir::def::suffix_local_unique_id(&binder.name);
        if let Some(line) = line_from_span(&exp.span) {
            self.per_function.binder_lines.insert(air_name.clone(), line);
        }
        self.per_function.binder_types.insert(air_name, binder.a.clone());
    }

    fn on_quantifier_binder_decl(&mut self, var: &VarIdent) {
        let air_name = vir::def::suffix_local_unique_id(var);
        self.per_function.binder_decl_names.insert(air_name);
    }

    fn on_body_lowering_start(&mut self) {
        self.per_function.binder_lines.clear();
    }

    fn on_reveal_string(&mut self, lit: &Arc<String>) {
        use sha2::{Digest, Sha512};
        let mut hasher = Sha512::new();
        hasher.update(lit.as_bytes());
        let hash_bytes = hasher.finalize();
        // Match the endianness used by sst_to_air.rs
        #[cfg(target_endian = "little")]
        let hash_int = num_bigint::BigUint::from_bytes_le(&hash_bytes);
        #[cfg(target_endian = "big")]
        let hash_int = num_bigint::BigUint::from_bytes_be(&hash_bytes);
        let hash_str = hash_int.to_string();
        self.per_function.reveal_strings.insert(Arc::new(hash_str), lit.clone());
    }

    fn make_assert_id(
        &mut self,
        _kind: &AssertIdKind,
        _index: usize,
        _parent: &Option<AssertId>,
    ) -> Option<AssertId> {
        let id = (1u64 << 32) | self.per_function.assert_id_counter;
        self.per_function.assert_id_counter += 1;
        Some(Arc::new(vec![id]))
    }

    fn on_function_lowered(&mut self) {
        // Save per-function state for use by on_query_lowered, which is called
        // AFTER on_function_lowered (VIR lowers the function, then AIR processes queries).
        self.saved_per_function = std::mem::take(&mut self.per_function);
        self.version_cursors.clear();
    }
    fn as_any(&self) -> &dyn std::any::Any {
        self
    }
    fn as_any_mut(&mut self) -> &mut dyn std::any::Any {
        self
    }
}

fn extract_for_loop_var_info(stm: &Stm) -> Option<(String, String)> {
    match &stm.x {
        StmX::Block(stmts) => {
            for s in stmts.iter() {
                if let Some(result) = extract_for_loop_var_info(s) {
                    return Some(result);
                }
            }
            None
        }
        StmX::Assign { lhs: vir::sst::Dest { dest, is_init: true }, rhs } => {
            let dest_name = match &dest.x {
                ExpX::Var(id) | ExpX::VarLoc(id) => Some(id.0.as_str()),
                ExpX::VarAt(id, _) => Some(id.0.as_str()),
                _ => None,
            };
            if let Some(dest_name) = dest_name {
                let rhs_name = match &rhs.x {
                    ExpX::Var(id) | ExpX::VarLoc(id) => Some(id.0.as_str()),
                    ExpX::VarAt(id, _) => Some(id.0.as_str()),
                    _ => None,
                };
                if let Some(rhs_name) = rhs_name
                    && rhs_name.starts_with(VERUS_LOOP_NEXT)
                {
                    return Some((VERUS_GHOST_ITER.to_string(), dest_name.to_string()));
                }
            }
            None
        }
        _ => None,
    }
}
