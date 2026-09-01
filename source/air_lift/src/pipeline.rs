//! Source-level normalization applied to AIR expressions before lifting: temporary and
//! version normalization, for-loop variable substitution, and the `normalize` rewrite
//! pass, all keyed off an accumulated [`PipelineContext`].

use crate::air_names::{self, AirName};
use crate::expr_utils;
use crate::types::{FunctionRole, VarInfo};
use air::ast::{BinaryOp, BindX, Constant, Expr, ExprX, Ident, MultiOp, StmtX, UnaryOp};
use air::ast_util::str_var;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

/// Bundles the annotation maps needed by the pipeline (accumulated from the
/// observer callbacks). Extended here with `choose_binder_names` + `lambda_decls`
/// (formerly on `FailedAssertContext`) since `normalize` needs them.
#[derive(Debug, Clone, Default)]
pub struct PipelineContext {
    // global
    pub function_roles: HashMap<Ident, FunctionRole>,
    pub friendly_names: HashMap<Ident, String>,
    // local
    pub variable_info: HashMap<Ident, VarInfo>,
    pub for_loop_var_map: HashMap<String, String>,
    pub reveal_strings: HashMap<Ident, Arc<String>>,
    pub binder_lines: HashMap<Ident, u32>,
    pub binder_decl_names: HashSet<Ident>,
    pub variable_def_lines: HashMap<Ident, u32>,
    // accumulated AIR declarations needed by `normalize`
    pub choose_binder_names: HashMap<Ident, Ident>,
    pub lambda_decls: HashMap<Ident, (Vec<Ident>, Expr)>,
    // datatype field-accessor AIR name -> clean source field name (for FieldAccess)
    pub datatype_field_names: HashMap<Ident, String>,
    // field-update AIR name -> clean source field name (for FieldUpdate decomposition)
    pub field_update_names: HashMap<Ident, String>,
    // VIR-level binder types, keyed by AIR name (for typed quantifier binders)
    pub binder_types: HashMap<Ident, vir::ast::Typ>,
    // crate under verification, to strip its prefix from friendly names
    pub current_crate: Option<String>,
}

pub fn expr_variant_name(expr: &Expr) -> &'static str {
    match &**expr {
        ExprX::Const(_) => "Const",
        ExprX::Var(_) => "Var",
        ExprX::Old(_, _) => "Old",
        ExprX::Apply(_, _) => "Apply",
        ExprX::ApplyFun(_, _, _) => "ApplyFun",
        ExprX::Unary(_, _) => "Unary",
        ExprX::Binary(_, _, _) => "Binary",
        ExprX::Multi(_, _) => "Multi",
        ExprX::IfElse(_, _, _) => "IfElse",
        ExprX::Array(_) => "Array",
        ExprX::Bind(_, _) => "Bind",
        ExprX::LabeledAxiom(_, _, _) => "LabeledAxiom",
        ExprX::LabeledAssertion(_, _, _, _) => "LabeledAssertion",
    }
}

/// Collect all variable names in an expression, including binder values.
pub fn collect_vars(expr: &Expr) -> HashSet<String> {
    expr_utils::fold_expr(expr, HashSet::new(), &|mut acc, e| {
        match &**e {
            ExprX::Var(name) | ExprX::Old(_, name) => {
                acc.insert(name.to_string());
            }
            _ => {}
        }
        acc
    })
}

/// Check if a function name represents iterator boilerplate.
fn is_iterator_boilerplate(fname: &Ident, ctx: &PipelineContext) -> bool {
    if ctx
        .function_roles
        .get(fname)
        .map(|r| matches!(r, FunctionRole::IteratorBoilerplate))
        .unwrap_or(false)
    {
        return true;
    }
    // Match by friendly name: the for-loop ghost iterator and the vstd
    // IteratorSpec machinery (obeys_prophetic_iter_laws, peek, remaining, ...).
    let friendly = ctx.friendly_names.get(fname).map(|s| s.as_str()).unwrap_or(fname.as_str());
    if friendly.contains(air_names::FOR_LOOP_GHOST_ITERATOR)
        || friendly.contains(air_names::FOR_LOOP_WRAPPER)
        || fname.as_str().contains(air_names::FOR_LOOP_WRAPPER)
    {
        return true;
    }
    air_names::ITERATOR_SPEC_METHODS.iter().any(|m| {
        // match `::method` or `.method` as a path/segment tail
        friendly.ends_with(m)
            || friendly.contains(&format!("::{}", m))
            || friendly.contains(&format!(".{}", m))
    })
}

pub fn transform_versioned_expr_with(expr: &Expr, var_info: &HashMap<Ident, VarInfo>) -> Expr {
    if var_info.is_empty() {
        return expr.clone();
    }
    expr_utils::apply_rewrite_once(expr, |e| {
        let ExprX::Var(name) = &**e else { return None };
        match var_info.get(name) {
            Some(VarInfo::Current { clean_name }) => Some(str_var(clean_name)),
            Some(VarInfo::Old { clean_name }) => Some(Arc::new(ExprX::Old(
                Arc::new(air_names::SNAPSHOT_INITIAL.to_string()),
                Arc::new(clean_name.clone()),
            ))),
            Some(VarInfo::Intermediate { clean_name, line, .. }) => {
                Some(str_var(&format!("{}@{}", clean_name, line)))
            }
            Some(VarInfo::Temporary) | Some(VarInfo::Noise) | None => None,
        }
    })
}

/// Strip mutation-version suffix from a variable name.
pub fn strip_version_suffix(name: &str) -> &str {
    let is_numeric = |s: &str| s.chars().all(|c| c.is_ascii_digit());

    if let Some(at_pos) = name.rfind(air_names::SUFFIX_LOCAL_STMT_CHAR)
        && is_numeric(&name[at_pos + 1..])
    {
        return &name[..at_pos];
    }
    for sentinel in &[air_names::SENTINEL_LOOP, air_names::SENTINEL_INIT] {
        if let Some(pos) = name.find(sentinel)
            && is_numeric(&name[pos + sentinel.len()..])
        {
            return &name[..pos];
        }
    }
    name
}

pub fn apply_for_loop_var_substitution(expr: &Expr, ctx: &PipelineContext) -> Expr {
    let map = &ctx.for_loop_var_map;
    if map.is_empty() {
        return expr.clone();
    }
    expr_utils::apply_rewrite(expr, |e| {
        if let ExprX::IfElse(cond, _then_expr, _else_expr) = &**e
            && let ExprX::Apply(f, cond_args) = &**cond
            && f.as_str().starts_with(air_names::IS_VARIANT_PREFIX)
        {
            for arg in cond_args.iter() {
                if contains_ghost_iter_call_annotated(arg, ctx)
                    && let Some(user_var) = find_ghost_iter_user_var_annotated(arg, ctx)
                {
                    return Some(str_var(user_var));
                }
            }
        }
        if let ExprX::Apply(f, args) = &**e {
            if is_iterator_boilerplate(f, ctx)
                && args.iter().any(|a| match_ghost_iter_arg(a, map).is_some())
            {
                return Some(Arc::new(ExprX::Const(Constant::Bool(true))));
            }
            if f.as_str().contains(air_names::SPEC_UNWRAP)
                || f.as_str().contains(air_names::OPTION_SOME_VARIANT_FIELD)
            {
                for arg in args.iter() {
                    if contains_ghost_iter_call_annotated(arg, ctx)
                        && let Some(user_var) = find_ghost_iter_user_var_annotated(arg, ctx)
                    {
                        return Some(str_var(user_var));
                    }
                }
            }
        }
        None
    })
}

fn contains_ghost_iter_call_annotated(expr: &Expr, ctx: &PipelineContext) -> bool {
    match &**expr {
        ExprX::Apply(f, args) => {
            if is_iterator_boilerplate(f, ctx) {
                return args
                    .iter()
                    .any(|a| match_ghost_iter_arg(a, &ctx.for_loop_var_map).is_some());
            }
            args.iter().any(|a| contains_ghost_iter_call_annotated(a, ctx))
        }
        _ => false,
    }
}

fn find_ghost_iter_user_var_annotated<'a>(
    expr: &Expr,
    ctx: &'a PipelineContext,
) -> Option<&'a str> {
    let map = &ctx.for_loop_var_map;
    let ExprX::Apply(f, args) = &**expr else { return None };

    if is_iterator_boilerplate(f, ctx) {
        args.iter().find_map(|arg| match_ghost_iter_arg(arg, map))
    } else {
        args.iter().find_map(|arg| find_ghost_iter_user_var_annotated(arg, ctx))
    }
}

fn match_ghost_iter_arg<'a>(arg: &Expr, map: &'a HashMap<String, String>) -> Option<&'a str> {
    match &**arg {
        ExprX::Var(v) => {
            let base = strip_version_suffix(v.as_str());
            map.get(base).map(|s| s.as_str())
        }
        ExprX::Apply(f, inner_args) => {
            if matches!(AirName::parse(f.as_str()), AirName::Boxed(_) | AirName::Unboxed(_))
                && inner_args.len() == 1
            {
                return match_ghost_iter_arg(&inner_args[0], map);
            }
            None
        }
        _ => None,
    }
}

/// Normalize AIR expressions for source-level display.

impl PipelineContext {
    pub fn normalize(&self, expr: &Expr) -> Expr {
        fn negate_if_sub_zero(first: &Expr, second: &Expr) -> Option<Expr> {
            if let ExprX::Const(Constant::Nat(n)) = &**first
                && n.as_str() == "0"
            {
                return Some(Arc::new(ExprX::Unary(UnaryOp::BitNeg, second.clone())));
            }
            None
        }

        let roles = &self.function_roles;
        let choose_binder_names = &self.choose_binder_names;
        let lambda_decls = &self.lambda_decls;
        let var_info = &self.variable_info;
        let normalized = expr_utils::apply_rewrite(expr, |e| match &**e {
            ExprX::LabeledAxiom(_, _, inner) => Some(inner.clone()),
            ExprX::LabeledAssertion(_, _, _, inner) => Some(inner.clone()),

            ExprX::Var(name) => {
                if let Some((params, body)) = lambda_decls.get(name) {
                    let binders: Vec<Arc<air::ast::BinderX<Arc<air::ast::TypX>>>> = params
                        .iter()
                        .map(|p| {
                            Arc::new(air::ast::BinderX {
                                name: p.clone(),
                                a: Arc::new(air::ast::TypX::Fun),
                            })
                        })
                        .collect();
                    return Some(Arc::new(ExprX::Bind(
                        Arc::new(BindX::Lambda(Arc::new(binders), Arc::new(vec![]), None)),
                        body.clone(),
                    )));
                }
                None
            }

            ExprX::Unary(UnaryOp::Not, inner) => {
                if let ExprX::Var(name) = &**inner
                    && name.as_str() == vir::def::FUEL_DEFAULTS
                {
                    return Some(Arc::new(ExprX::Const(Constant::Bool(false))));
                }
                None
            }

            ExprX::Binary(BinaryOp::Implies, lhs, rhs) => {
                if let ExprX::Var(name) = &**lhs {
                    if AirName::parse(name.as_str()).is_location_label() {
                        return Some(rhs.clone());
                    }
                    if name.as_str() == vir::def::FUEL_DEFAULTS
                        || matches!(AirName::parse(name.as_str()), AirName::TmpVar(_))
                        || matches!(
                            var_info.get(name),
                            Some(VarInfo::Noise) | Some(VarInfo::Temporary)
                        )
                    {
                        return Some(rhs.clone());
                    }
                }
                if let ExprX::Const(Constant::Bool(true)) = &**lhs {
                    return Some(rhs.clone());
                }
                if let ExprX::Apply(func_name, _) = &**lhs
                    && matches!(
                        roles.get(func_name),
                        Some(r) if matches!(r, FunctionRole::Clip) || r.is_bookkeeping()
                    )
                {
                    return Some(rhs.clone());
                }
                if let ExprX::Apply(func_name, _) = &**rhs
                    && matches!(roles.get(func_name), Some(r) if r.is_bookkeeping())
                {
                    return Some(Arc::new(ExprX::Const(Constant::Bool(true))));
                }
                if let ExprX::Var(name) = &**rhs
                    && AirName::parse(name.as_str()).is_location_label()
                {
                    return Some(Arc::new(ExprX::Const(Constant::Bool(true))));
                }
                None
            }

            ExprX::Bind(bind, body) => {
                if let BindX::Let(binders) = &**bind {
                    let mut inlined = body.clone();
                    for b in binders.iter() {
                        inlined = expr_utils::subst_expr(&b.name, &b.a, &inlined);
                    }
                    return Some(inlined);
                }
                None
            }

            ExprX::Multi(MultiOp::And, operands) if !operands.is_empty() => {
                let is_noise_term = |e: &Expr| match &**e {
                    ExprX::Apply(f, _) => {
                        matches!(roles.get(f), Some(r) if matches!(r, FunctionRole::Clip) || r.is_bookkeeping())
                    }
                    ExprX::Var(n) => air_names::is_solver_noise(n.as_str()),
                    ExprX::Const(Constant::Bool(true)) => true,
                    _ => false,
                };
                let remaining: Vec<_> =
                    operands.iter().filter(|e| !is_noise_term(e)).cloned().collect();
                if remaining.len() == operands.len() {
                    None
                } else if remaining.is_empty() {
                    Some(Arc::new(ExprX::Const(Constant::Bool(true))))
                } else if remaining.len() == 1 {
                    Some(remaining[0].clone())
                } else {
                    Some(Arc::new(ExprX::Multi(MultiOp::And, Arc::new(remaining))))
                }
            }

            // `X == mut_ref_update_current(Y, e)` — the encoding of `*X = e`
            // through a &mut. Rewrite to `mut_ref_current(X) == e` so it renders
            // as `*X == e` (program terms) rather than the raw update function.
            // The future-frame half (`future(X) == future(Y)`) states the frame condition
            // — that the mutation leaves the rest of the value unchanged. Reading `*X = e`
            // at the source level leaves the frame implicit, so it has no surface term.
            ExprX::Binary(BinaryOp::Eq, lhs, rhs) => {
                // Reflexivity: `x == x` is a tautology carrying no program information,
                // so it simplifies to `true`.
                if expr_utils::expr_key(lhs) == expr_utils::expr_key(rhs) {
                    return Some(Arc::new(ExprX::Const(Constant::Bool(true))));
                }
                let mk = |x: &Expr, e: &Expr| {
                    Some(Arc::new(ExprX::Binary(
                        BinaryOp::Eq,
                        Arc::new(ExprX::Apply(
                            Arc::new(air_names::MUT_REF_CURRENT.to_string()),
                            Arc::new(vec![x.clone()]),
                        )),
                        e.clone(),
                    )))
                };
                if let ExprX::Apply(f, a) = &**rhs
                    && f.as_str() == air_names::MUT_REF_UPDATE_CURRENT
                    && a.len() == 2
                {
                    return mk(lhs, &a[1]);
                }
                if let ExprX::Apply(f, a) = &**lhs
                    && f.as_str() == air_names::MUT_REF_UPDATE_CURRENT
                    && a.len() == 2
                {
                    return mk(rhs, &a[1]);
                }
                // Eq(x, FieldUpdate(field, base, val)) — the encoding of a struct field
                // assignment — decomposes to `x.field == val`. Recursively peels nested
                // FieldUpdates: Eq(x, FU(f1, _, FU(f2, _, v))) → x.f1.f2 == v.
                if let ExprX::Binary(BinaryOp::FieldUpdate(field_id), _base, val) = &**rhs {
                    fn peel_field_update(
                        lhs: Expr,
                        field_id: &Ident,
                        val: &Expr,
                        ctx: &PipelineContext,
                    ) -> Expr {
                        let field_name = ctx
                            .field_update_names
                            .get(field_id)
                            .map(|s| s.as_str())
                            .unwrap_or(field_id.as_str());
                        let field_acc = Arc::new(ExprX::Apply(
                            Arc::new(field_name.to_string()),
                            Arc::new(vec![lhs]),
                        ));
                        if let ExprX::Binary(BinaryOp::FieldUpdate(inner_field), _inner_base, inner_val) = &**val {
                            peel_field_update(field_acc, inner_field, inner_val, ctx)
                        } else {
                            Arc::new(ExprX::Binary(BinaryOp::Eq, field_acc, val.clone()))
                        }
                    }
                    return Some(peel_field_update(lhs.clone(), field_id, val, &self));
                }
                // Decompose a mut-ref field update `mut_ref_current(X) == Ctor{f: e, ..}`
                // (or a nested field thereof, `self.inner == Inner{..}`) into
                // per-field equalities `X.f == e`. Fires when the LHS is rooted at
                // mut_ref_current (a &mut current value / its fields) — leaves
                // user-written constructor equalities like `r == Wrapper(x)` intact.
                // Runs recursively via apply_rewrite's fixpoint for nested structs.
                let lhs_is_mut_ref_rooted = expr_utils::fold_expr(lhs, false, &|acc, e| {
                    acc || matches!(&**e,
                        ExprX::Apply(f, _) if f.as_str() == air_names::MUT_REF_CURRENT)
                });
                if lhs_is_mut_ref_rooted
                    && let ExprX::Apply(ctor, ctor_args) = &**rhs
                    && let Some(FunctionRole::VariantConstructor { field_accessors, .. }) =
                        roles.get(ctor)
                    && !field_accessors.is_empty()
                    && ctor_args.len() >= field_accessors.len()
                {
                    let vals = &ctor_args[ctor_args.len() - field_accessors.len()..];
                    let conjuncts: Vec<Expr> = field_accessors
                        .iter()
                        .zip(vals.iter())
                        .map(|(acc, val)| {
                            Arc::new(ExprX::Binary(
                                BinaryOp::Eq,
                                Arc::new(ExprX::Apply(
                                    Arc::new(acc.clone()),
                                    Arc::new(vec![lhs.clone()]),
                                )),
                                val.clone(),
                            ))
                        })
                        .collect();
                    if conjuncts.len() == 1 {
                        return Some(conjuncts.into_iter().next().unwrap());
                    }
                    return Some(Arc::new(ExprX::Multi(MultiOp::And, Arc::new(conjuncts))));
                }
                None
            }

            ExprX::Apply(func_name, args) => {
                match AirName::parse(func_name.as_str()) {
                    AirName::Boxed(_) | AirName::Unboxed(_) => {
                        if args.len() == 1 {
                            return Some(args[0].clone());
                        }
                    }
                    _ => {}
                }
                if func_name.as_str() == air_names::MK_FUN && args.len() == 1 {
                    return Some(args[0].clone());
                }
                // Prelude axiom: mut_ref_current(mut_ref_update_current(m, v)) == v.
                // Reading the current value of a just-updated &mut yields the new value.
                if func_name.as_str() == air_names::MUT_REF_CURRENT
                    && args.len() == 1
                    && let ExprX::Apply(inner_f, inner_args) = &*args[0]
                    && inner_f.as_str() == air_names::MUT_REF_UPDATE_CURRENT
                    && inner_args.len() == 2
                {
                    return Some(inner_args[1].clone());
                }
                match roles.get(func_name) {
                    Some(FunctionRole::Clip) if !args.is_empty() => {
                        Some(args.last().unwrap().clone())
                    }
                    Some(FunctionRole::IntCoerce) if !args.is_empty() => Some(args[0].clone()),
                    _ => {
                        if func_name.as_str().starts_with(air_names::CHOOSE)
                            && let Some(binder_name) = choose_binder_names.get(func_name)
                        {
                            let s = binder_name.as_str();
                            let clean = if let Some(pos) =
                                s.rfind(air_names::SUFFIX_LOCAL_EXPR_CHAR)
                            {
                                let suffix = &s[pos + 1..];
                                if !suffix.is_empty() && suffix.chars().all(|c| c.is_ascii_digit())
                                {
                                    &s[..pos]
                                } else {
                                    s
                                }
                            } else {
                                s
                            };
                            return Some(Arc::new(ExprX::Var(Arc::new(clean.to_string()))));
                        }
                        if func_name.as_str() == air_names::SUB && args.len() == 2 {
                            return negate_if_sub_zero(&args[0], &args[1]);
                        }
                        if args.len() == 1 {
                            let fname = func_name.as_str();
                            if fname == air_names::U_HI
                                || fname == air_names::I_HI
                                || fname == air_names::I_LO
                            {
                                let width_name = match &*args[0] {
                                    ExprX::Var(v) if v.as_str() == air_names::ARCH_SIZE => "size",
                                    ExprX::Const(Constant::Nat(n)) => n.as_str(),
                                    _ => "",
                                };
                                let tp = match width_name {
                                    "8" => Some(if fname == air_names::U_HI { "u8" } else { "i8" }),
                                    "16" => {
                                        Some(if fname == air_names::U_HI { "u16" } else { "i16" })
                                    }
                                    "32" => {
                                        Some(if fname == air_names::U_HI { "u32" } else { "i32" })
                                    }
                                    "64" => {
                                        Some(if fname == air_names::U_HI { "u64" } else { "i64" })
                                    }
                                    "128" => {
                                        Some(if fname == air_names::U_HI { "u128" } else { "i128" })
                                    }
                                    "size" => Some(if fname == air_names::U_HI {
                                        "usize"
                                    } else {
                                        "isize"
                                    }),
                                    _ => None,
                                };
                                if let Some(tp) = tp {
                                    let bound = if fname == air_names::I_LO {
                                        format!("{}::MIN", tp)
                                    } else {
                                        format!("{}::MAX + 1", tp)
                                    };
                                    return Some(Arc::new(ExprX::Var(Arc::new(bound))));
                                }
                            }
                        }
                        None
                    }
                }
            }

            ExprX::Multi(MultiOp::Sub, operands) if operands.len() == 2 => {
                negate_if_sub_zero(&operands[0], &operands[1])
            }

            _ => None,
        });

        // Fold `TYPE::MAX + 1 - 1` back to `TYPE::MAX`.

        let normalized = expr_utils::apply_rewrite(&normalized, |e| {
            if let ExprX::Multi(MultiOp::Sub, operands) = &**e
                && operands.len() == 2
                && let ExprX::Const(Constant::Nat(n)) = &*operands[1]
                && n.as_str() == "1"
                && let ExprX::Var(v) = &*operands[0]
                && v.as_str().ends_with("::MAX + 1")
            {
                let max_name = v.as_str().trim_end_matches(" + 1");
                return Some(Arc::new(ExprX::Var(Arc::new(max_name.to_string()))));
            }
            None
        });

        // Rewrite `e < TYPE::MAX + 1` to `e <= TYPE::MAX`: the exclusive upper bound
        // `2^N` has no symbolic name in source, whereas `<= MAX` does.
        expr_utils::apply_rewrite(&normalized, |e| {
            if let ExprX::Binary(BinaryOp::Lt, lhs, rhs) = &**e
                && let ExprX::Var(v) = &**rhs
                && v.as_str().ends_with("::MAX + 1")
            {
                let max_name = v.as_str().trim_end_matches(" + 1").to_string();
                return Some(Arc::new(ExprX::Binary(
                    BinaryOp::Le,
                    lhs.clone(),
                    Arc::new(ExprX::Var(Arc::new(max_name))),
                )));
            }
            None
        })
    }
}

pub fn collect_tmp_defs_from_stmt(stmt: &air::ast::Stmt, defs: &mut HashMap<Ident, Expr>) {
    // Collect every candidate definition first, then keep only temps with exactly one
    // distinct definition. A temp assigned different values on different control-flow
    // paths (e.g. a match lowered as a statement-level switch, one assignment per arm)
    // is path-dependent: substituting any single definition globally would attribute
    // one arm's value to every path. Such temps are left to path-local resolution.
    let mut multi: HashMap<Ident, Vec<Expr>> = HashMap::new();
    collect_tmp_def_candidates_from_stmt(stmt, &mut multi);
    for (name, candidates) in multi {
        if candidates.len() == 1 {
            defs.entry(name).or_insert_with(|| candidates.into_iter().next().unwrap());
        }
    }
}

fn collect_tmp_def_candidates_from_stmt(
    stmt: &air::ast::Stmt,
    multi: &mut HashMap<Ident, Vec<Expr>>,
) {
    match &**stmt {
        StmtX::Assert(_, _, _, e) | StmtX::Assume(e) => collect_tmp_def_candidates(e, multi),
        StmtX::Block(stmts) | StmtX::Switch(stmts) => {
            for s in stmts.iter() {
                collect_tmp_def_candidates_from_stmt(s, multi);
            }
        }
        // Loop and branch statement nesting also carries temporary definitions.
        StmtX::DeadEnd(s) | StmtX::Breakable(_, s) => {
            collect_tmp_def_candidates_from_stmt(s, multi)
        }
        _ => {}
    }
}

pub fn collect_tmp_defs_from_expr(expr: &Expr, defs: &mut HashMap<Ident, Expr>) {
    let mut multi: HashMap<Ident, Vec<Expr>> = HashMap::new();
    collect_tmp_def_candidates(expr, &mut multi);
    for (name, candidates) in multi {
        if candidates.len() == 1 {
            defs.entry(name).or_insert_with(|| candidates.into_iter().next().unwrap());
        }
    }
}

/// Record every `tmp == def` candidate (either the guarded `(tmp == def) ==> _` form or a
/// standalone equality), deduplicated per temp by structural key, so the caller can tell
/// single-assignment temps (one distinct definition) from path-dependent ones (several).
fn collect_tmp_def_candidates(expr: &Expr, multi: &mut HashMap<Ident, Vec<Expr>>) {
    let push = |name: &Ident, rhs: &Expr, multi: &mut HashMap<Ident, Vec<Expr>>| {
        let entry = multi.entry(name.clone()).or_default();
        let key = expr_utils::expr_key(rhs);
        if !entry.iter().any(|e| expr_utils::expr_key(e) == key) {
            entry.push(rhs.clone());
        }
    };
    let collected = expr_utils::fold_expr(expr, Vec::new(), &|mut acc, e| {
        // `(tmp == def) ==> _`  — the guarded definition form.
        if let ExprX::Binary(BinaryOp::Implies, lhs, _) = &**e
            && let ExprX::Binary(BinaryOp::Eq, left, right) = &**lhs
            && let ExprX::Var(name) = &**left
            && matches!(AirName::parse(name.as_str()), AirName::TmpVar(_))
        {
            acc.push((name.clone(), right.clone()));
        }
        // `tmp == def`  — a standalone definition.
        if let ExprX::Binary(BinaryOp::Eq, left, right) = &**e
            && let ExprX::Var(name) = &**left
            && matches!(AirName::parse(name.as_str()), AirName::TmpVar(_))
        {
            acc.push((name.clone(), right.clone()));
        }
        acc
    });
    for (name, rhs) in collected {
        push(&name, &rhs, multi);
    }
}

// ---------------------------------------------------------------------------
// Temporary-definition expansion, applied before lifting.
// ---------------------------------------------------------------------------

/// Transitively resolve a tmp-definition map (a def may reference another def).
pub fn resolve_defs_transitively(def_map: &mut HashMap<Ident, Expr>) {
    loop {
        let mut changed = false;
        let keys: Vec<Ident> = def_map.keys().cloned().collect();
        for key in keys {
            let val = def_map[&key].clone();
            let resolved = expr_utils::apply_rewrite_once(&val, |e| {
                if let ExprX::Var(name) = &**e
                    && name != &key
                {
                    return def_map.get(name).cloned();
                }
                None
            });
            if expr_utils::expr_key(&resolved) != expr_utils::expr_key(&val) {
                def_map.insert(key, resolved);
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
}

/// Substitute a (resolved) def map into an expression.
pub fn substitute_defs(expr: &Expr, def_map: &HashMap<Ident, Expr>) -> Expr {
    if def_map.is_empty() {
        return expr.clone();
    }
    expr_utils::apply_rewrite_once(expr, |e| {
        if let ExprX::Var(name) = &**e { def_map.get(name).cloned() } else { None }
    })
}

/// Expand temporaries in `expr` using an already-collected tmp-def map (as gathered
/// by `collect_tmp_defs_from_stmt`, e.g. `QueryState::tmp_defs`). Resolves the map
/// transitively, then substitutes — no re-collection.
pub fn expand_temporaries(tmp_defs: &HashMap<Ident, Expr>, expr: &Expr) -> Expr {
    if tmp_defs.is_empty() {
        return expr.clone();
    }
    let mut defs = tmp_defs.clone();
    resolve_defs_transitively(&mut defs);
    substitute_defs(expr, &defs)
}

#[cfg(test)]
mod temporaries_tests {
    use super::*;
    use air::ast::{Constant, ExprX};
    use std::sync::Arc;

    // E13: expand_temporaries — transitive tmp-def resolution + substitution
    // eliminates tmp% variables from a lifted goal.
    #[test]
    fn expand_temporaries_resolves_and_substitutes() {
        let five: Expr = Arc::new(ExprX::Const(Constant::Nat(Arc::new("5".to_string()))));
        let tmp1: Ident = Arc::new("tmp%1".to_string());
        let tmp2: Ident = Arc::new("tmp%2".to_string());
        let mut defs: HashMap<Ident, Expr> = HashMap::new();
        defs.insert(tmp1.clone(), five.clone());
        // tmp2 references tmp1 (must resolve transitively to 5).
        defs.insert(tmp2.clone(), Arc::new(ExprX::Var(tmp1.clone())));
        resolve_defs_transitively(&mut defs);
        assert_eq!(expr_utils::expr_key(&defs[&tmp2]), expr_utils::expr_key(&five));

        // Substituting into a goal that uses tmp2 leaves no tmp% behind.
        let goal: Expr = Arc::new(ExprX::Var(tmp2.clone()));
        let out = substitute_defs(&goal, &defs);
        let key = expr_utils::expr_key(&out);
        assert_eq!(key, "5");
        assert!(!key.contains("tmp%"), "tmp% must not survive expansion: {}", key);

        // The public one-shot wrapper takes the *already-collected* map and yields the
        // same clean result (resolve + substitute, no re-collection).
        let mut raw: HashMap<Ident, Expr> = HashMap::new();
        raw.insert(tmp1.clone(), five.clone());
        raw.insert(tmp2.clone(), Arc::new(ExprX::Var(tmp1.clone())));
        let via_wrapper = expand_temporaries(&raw, &Arc::new(ExprX::Var(tmp2)));
        assert_eq!(expr_utils::expr_key(&via_wrapper), "5");
    }

    // A temporary assigned different values on different control-flow paths (e.g. a
    // match lowered as a statement-level switch, one assignment per arm) is NOT a
    // single-assignment temp: no definition may be substituted globally. Only temps
    // with exactly one (deduplicated) definition enter the map.
    #[test]
    fn multi_path_tmp_definitions_are_not_collected() {
        use air::ast::StmtX;
        let tmp3: Ident = Arc::new("tmp%3".to_string());
        let mk_num = |n: &str| -> Expr {
            Arc::new(ExprX::Const(Constant::Nat(Arc::new(n.to_string()))))
        };
        let assign = |v: &Ident, e: &Expr| -> air::ast::Stmt {
            Arc::new(StmtX::Assume(Arc::new(ExprX::Binary(
                BinaryOp::Eq,
                Arc::new(ExprX::Var(v.clone())),
                e.clone(),
            ))))
        };
        // switch { assume tmp%3 == 1 } { assume tmp%3 == 0 }
        let sw: air::ast::Stmt = Arc::new(StmtX::Switch(Arc::new(vec![
            assign(&tmp3, &mk_num("1")),
            assign(&tmp3, &mk_num("0")),
        ])));
        let mut defs: HashMap<Ident, Expr> = HashMap::new();
        collect_tmp_defs_from_stmt(&sw, &mut defs);
        assert!(
            !defs.contains_key(&tmp3),
            "path-dependent temp must not get a global definition; got: {:?}",
            defs.get(&tmp3).map(|e| expr_utils::expr_key(e))
        );

        // Control: the same definition on both paths IS single-assignment (deduplicated).
        let sw_same: air::ast::Stmt = Arc::new(StmtX::Switch(Arc::new(vec![
            assign(&tmp3, &mk_num("1")),
            assign(&tmp3, &mk_num("1")),
        ])));
        let mut defs2: HashMap<Ident, Expr> = HashMap::new();
        collect_tmp_defs_from_stmt(&sw_same, &mut defs2);
        assert!(defs2.contains_key(&tmp3), "identical defs on all paths are collectable");
    }
}
