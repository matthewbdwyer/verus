//! Utilities for working with AIR expressions
//!
//! This module provides functions for manipulating AIR expressions including:
//! - Variable substitution with capture avoidance
//! - Function inlining with recursion detection
//! - One-point rule transformation for logical simplification

use air::ast::{BindX, Binder, BinderX, Binders, Constant, Expr, ExprX, Ident};
use std::collections::HashSet;
use std::sync::Arc;

/// Type alias for function declarations: (parameters, body)
pub type DeclRhs = (Binders<air::ast::Typ>, Expr);

/// Produce a canonical string key for an AIR expression.
pub fn expr_key(expr: &Expr) -> String {
    match &**expr {
        ExprX::Const(Constant::Bool(b)) => b.to_string(),
        ExprX::Const(Constant::Nat(n)) => n.to_string(),
        ExprX::Const(Constant::Real(r)) => r.to_string(),
        ExprX::Const(Constant::BitVec(v, width)) => format!("bv{}_{}", width, v),
        ExprX::Var(name) => name.to_string(),
        ExprX::Apply(f, args) => {
            let args: Vec<_> = args.iter().map(expr_key).collect();
            if args.is_empty() { f.to_string() } else { format!("({} {})", f, args.join(" ")) }
        }
        ExprX::Unary(op, e) => format!("({:?} {})", op, expr_key(e)),
        ExprX::Binary(op, a, b) => format!("({:?} {} {})", op, expr_key(a), expr_key(b)),
        ExprX::Multi(op, args) => {
            let args: Vec<_> = args.iter().map(expr_key).collect();
            format!("({:?} {})", op, args.join(" "))
        }
        ExprX::IfElse(c, t, e) => format!("(ite {} {} {})", expr_key(c), expr_key(t), expr_key(e)),
        ExprX::Bind(bind, body) => format!("(bind {:?} {})", bind, expr_key(body)),
        ExprX::LabeledAxiom(_, _, inner) | ExprX::LabeledAssertion(_, _, _, inner) => {
            expr_key(inner)
        }
        _ => format!("(opaque {:?})", std::mem::discriminant(expr.as_ref())),
    }
}

/// Collect all free variables in an expression.
fn free_vars(expr: &Expr) -> HashSet<Ident> {
    fn go(expr: &Expr, bound: &HashSet<Ident>, acc: &mut HashSet<Ident>) {
        match &**expr {
            ExprX::Var(name) => {
                if !bound.contains(name) {
                    acc.insert(name.clone());
                }
            }
            ExprX::Const(_) | ExprX::Old(_, _) => {}
            ExprX::Apply(_, args) | ExprX::Multi(_, args) | ExprX::Array(args) => {
                for a in args.iter() {
                    go(a, bound, acc);
                }
            }
            ExprX::ApplyFun(_, f, args) => {
                go(f, bound, acc);
                for a in args.iter() {
                    go(a, bound, acc);
                }
            }
            ExprX::Unary(_, e) => go(e, bound, acc),
            ExprX::Binary(_, l, r) => {
                go(l, bound, acc);
                go(r, bound, acc);
            }
            ExprX::IfElse(c, t, e) => {
                go(c, bound, acc);
                go(t, bound, acc);
                go(e, bound, acc);
            }
            ExprX::Bind(bind, body) => {
                let mut inner_bound = bound.clone();
                match &**bind {
                    BindX::Let(binders) => {
                        for b in binders.iter() {
                            go(&b.a, bound, acc);
                            inner_bound.insert(b.name.clone());
                        }
                    }
                    BindX::Quant(_, binders, triggers, _) | BindX::Lambda(binders, triggers, _) => {
                        for b in binders.iter() {
                            inner_bound.insert(b.name.clone());
                        }
                        for trigger in triggers.iter() {
                            for e in trigger.iter() {
                                go(e, &inner_bound, acc);
                            }
                        }
                    }
                    BindX::Choose(binders, triggers, _, cond) => {
                        for b in binders.iter() {
                            inner_bound.insert(b.name.clone());
                        }
                        for trigger in triggers.iter() {
                            for e in trigger.iter() {
                                go(e, &inner_bound, acc);
                            }
                        }
                        go(cond, &inner_bound, acc);
                    }
                }
                go(body, &inner_bound, acc);
            }
            ExprX::LabeledAxiom(_, _, inner) | ExprX::LabeledAssertion(_, _, _, inner) => {
                go(inner, bound, acc);
            }
        }
    }
    let mut acc = HashSet::new();
    go(expr, &HashSet::new(), &mut acc);
    acc
}

/// Returns `expr[var := replacement]` with capture-avoiding substitution.
///
/// If a Bind introduces a binder name that conflicts with a free variable in
/// `replacement`, the binder is alpha-renamed to a fresh name before recursing.
pub fn subst_expr(var: &Ident, replacement: &Expr, expr: &Expr) -> Expr {
    subst_expr_inner(var, replacement, expr, &free_vars(replacement))
}

/// Global counter for generating fresh names during alpha-renaming.
fn fresh_name(base: &Ident) -> Ident {
    use std::sync::atomic::{AtomicU64, Ordering};
    static COUNTER: AtomicU64 = AtomicU64::new(0);
    let n = COUNTER.fetch_add(1, Ordering::Relaxed);
    Arc::new(format!("{}$$alpha{}", base, n))
}

fn subst_expr_inner(
    var: &Ident,
    replacement: &Expr,
    expr: &Expr,
    repl_fvs: &HashSet<Ident>,
) -> Expr {
    match &**expr {
        ExprX::Var(name) => {
            if name == var {
                replacement.clone()
            } else {
                expr.clone()
            }
        }
        ExprX::Const(_) | ExprX::Old(_, _) => expr.clone(),
        ExprX::Apply(f, args) => {
            let new_args: Vec<Expr> =
                args.iter().map(|a| subst_expr_inner(var, replacement, a, repl_fvs)).collect();
            Arc::new(ExprX::Apply(f.clone(), Arc::new(new_args)))
        }
        ExprX::ApplyFun(typ, fun_expr, args) => {
            let new_fun = subst_expr_inner(var, replacement, fun_expr, repl_fvs);
            let new_args: Vec<Expr> =
                args.iter().map(|a| subst_expr_inner(var, replacement, a, repl_fvs)).collect();
            Arc::new(ExprX::ApplyFun(typ.clone(), new_fun, Arc::new(new_args)))
        }
        ExprX::Unary(op, e) => {
            Arc::new(ExprX::Unary(*op, subst_expr_inner(var, replacement, e, repl_fvs)))
        }
        ExprX::Binary(op, l, r) => {
            let nl = subst_expr_inner(var, replacement, l, repl_fvs);
            let nr = subst_expr_inner(var, replacement, r, repl_fvs);
            Arc::new(ExprX::Binary(op.clone(), nl, nr))
        }
        ExprX::Multi(op, operands) => {
            let new_ops: Vec<Expr> =
                operands.iter().map(|a| subst_expr_inner(var, replacement, a, repl_fvs)).collect();
            Arc::new(ExprX::Multi(*op, Arc::new(new_ops)))
        }
        ExprX::IfElse(c, t, e) => {
            let nc = subst_expr_inner(var, replacement, c, repl_fvs);
            let nt = subst_expr_inner(var, replacement, t, repl_fvs);
            let ne = subst_expr_inner(var, replacement, e, repl_fvs);
            Arc::new(ExprX::IfElse(nc, nt, ne))
        }
        ExprX::Array(elements) => {
            let new_elems: Vec<Expr> =
                elements.iter().map(|a| subst_expr_inner(var, replacement, a, repl_fvs)).collect();
            Arc::new(ExprX::Array(Arc::new(new_elems)))
        }
        ExprX::Bind(bind, body) => subst_bind(var, replacement, bind, body, repl_fvs),
        ExprX::LabeledAxiom(msgs, filter, inner) => {
            let new_inner = subst_expr_inner(var, replacement, inner, repl_fvs);
            Arc::new(ExprX::LabeledAxiom(msgs.clone(), filter.clone(), new_inner))
        }
        ExprX::LabeledAssertion(assert_id, msg, filter, inner) => {
            let new_inner = subst_expr_inner(var, replacement, inner, repl_fvs);
            Arc::new(ExprX::LabeledAssertion(
                assert_id.clone(),
                msg.clone(),
                filter.clone(),
                new_inner,
            ))
        }
    }
}

/// Handle substitution into Bind expressions with capture-avoiding alpha-renaming.
fn subst_bind(
    var: &Ident,
    replacement: &Expr,
    bind: &air::ast::Bind,
    body: &Expr,
    repl_fvs: &HashSet<Ident>,
) -> Expr {
    match &**bind {
        BindX::Let(binders) => {
            let mut new_binders: Vec<Binder<Expr>> = Vec::new();
            let mut renames: Vec<(Ident, Ident)> = Vec::new();
            let mut shadowed = false;
            for b in binders.iter() {
                let new_val = if shadowed {
                    b.a.clone()
                } else {
                    subst_expr_inner(var, replacement, &b.a, repl_fvs)
                };
                if &b.name == var {
                    shadowed = true;
                    new_binders.push(Arc::new(BinderX { name: b.name.clone(), a: new_val }));
                } else if repl_fvs.contains(&b.name) {
                    let fresh = fresh_name(&b.name);
                    renames.push((b.name.clone(), fresh.clone()));
                    new_binders.push(Arc::new(BinderX { name: fresh, a: new_val }));
                } else {
                    new_binders.push(Arc::new(BinderX { name: b.name.clone(), a: new_val }));
                }
            }
            let mut new_body = if shadowed {
                body.clone()
            } else {
                subst_expr_inner(var, replacement, body, repl_fvs)
            };
            // Apply alpha-renames to body
            for (old_name, new_name) in &renames {
                new_body = rename_var(old_name, new_name, &new_body);
            }
            Arc::new(ExprX::Bind(Arc::new(BindX::Let(Arc::new(new_binders))), new_body))
        }
        BindX::Quant(quant, binders, triggers, qid) => {
            if binders.iter().any(|b| &b.name == var) {
                // var is shadowed by quantifier — no substitution in body/triggers
                return Arc::new(ExprX::Bind(bind.clone(), body.clone()));
            }
            let (new_binders, renames) = alpha_rename_typed_binders(binders, repl_fvs);
            let new_triggers = subst_triggers(var, replacement, triggers, repl_fvs, &renames);
            let mut new_body = subst_expr_inner(var, replacement, body, repl_fvs);
            for (old_name, new_name) in &renames {
                new_body = rename_var(old_name, new_name, &new_body);
            }
            Arc::new(ExprX::Bind(
                Arc::new(BindX::Quant(*quant, new_binders, new_triggers, qid.clone())),
                new_body,
            ))
        }
        BindX::Lambda(binders, triggers, qid) => {
            if binders.iter().any(|b| &b.name == var) {
                return Arc::new(ExprX::Bind(bind.clone(), body.clone()));
            }
            let (new_binders, renames) = alpha_rename_typed_binders(binders, repl_fvs);
            let new_triggers = subst_triggers(var, replacement, triggers, repl_fvs, &renames);
            let mut new_body = subst_expr_inner(var, replacement, body, repl_fvs);
            for (old_name, new_name) in &renames {
                new_body = rename_var(old_name, new_name, &new_body);
            }
            Arc::new(ExprX::Bind(
                Arc::new(BindX::Lambda(new_binders, new_triggers, qid.clone())),
                new_body,
            ))
        }
        BindX::Choose(binders, triggers, qid, cond) => {
            if binders.iter().any(|b| &b.name == var) {
                return Arc::new(ExprX::Bind(bind.clone(), body.clone()));
            }
            let (new_binders, renames) = alpha_rename_typed_binders(binders, repl_fvs);
            let new_triggers = subst_triggers(var, replacement, triggers, repl_fvs, &renames);
            let mut new_cond = subst_expr_inner(var, replacement, cond, repl_fvs);
            let mut new_body = subst_expr_inner(var, replacement, body, repl_fvs);
            for (old_name, new_name) in &renames {
                new_cond = rename_var(old_name, new_name, &new_cond);
                new_body = rename_var(old_name, new_name, &new_body);
            }
            Arc::new(ExprX::Bind(
                Arc::new(BindX::Choose(new_binders, new_triggers, qid.clone(), new_cond)),
                new_body,
            ))
        }
    }
}

/// Alpha-rename typed binders that conflict with free variables in the replacement.
fn alpha_rename_typed_binders(
    binders: &Binders<air::ast::Typ>,
    repl_fvs: &HashSet<Ident>,
) -> (Binders<air::ast::Typ>, Vec<(Ident, Ident)>) {
    let mut renames = Vec::new();
    let new_binders: Vec<Binder<air::ast::Typ>> = binders
        .iter()
        .map(|b| {
            if repl_fvs.contains(&b.name) {
                let fresh = fresh_name(&b.name);
                renames.push((b.name.clone(), fresh.clone()));
                Arc::new(BinderX { name: fresh, a: b.a.clone() })
            } else {
                b.clone()
            }
        })
        .collect();
    (Arc::new(new_binders), renames)
}

/// Substitute inside triggers and apply alpha-renames.
fn subst_triggers(
    var: &Ident,
    replacement: &Expr,
    triggers: &air::ast::Triggers,
    repl_fvs: &HashSet<Ident>,
    renames: &[(Ident, Ident)],
) -> air::ast::Triggers {
    let new_triggers: Vec<_> = triggers
        .iter()
        .map(|trigger| {
            let new_trigger: Vec<_> = trigger
                .iter()
                .map(|e| {
                    let mut ne = subst_expr_inner(var, replacement, e, repl_fvs);
                    for (old_name, new_name) in renames {
                        ne = rename_var(old_name, new_name, &ne);
                    }
                    ne
                })
                .collect();
            Arc::new(new_trigger)
        })
        .collect();
    Arc::new(new_triggers)
}

/// Simple variable renaming: replace all free occurrences of `old` with `Var(new_name)`.
fn rename_var(old: &Ident, new_name: &Ident, expr: &Expr) -> Expr {
    let replacement = Arc::new(ExprX::Var(new_name.clone()));
    // Use apply_rewrite_once for a single-pass rename (no fixpoint needed)
    apply_rewrite_once(expr, |e| {
        if let ExprX::Var(name) = &**e
            && name == old
        {
            return Some(replacement.clone());
        }
        None
    })
}

/// Function inlining for AIR expressions with eligibility predicate.
pub fn inline_functions_with_eligibility<F>(
    expr: &Expr,
    decls: &std::collections::HashMap<Ident, (Binders<air::ast::Typ>, Expr)>,
    is_eligible: F,
) -> Expr
where
    F: Fn(&Ident, &(Binders<air::ast::Typ>, Expr)) -> bool,
{
    inline_functions_rec(expr, decls, &mut HashSet::new(), &is_eligible)
}

fn inline_functions_rec<F>(
    expr: &Expr,
    decls: &std::collections::HashMap<Ident, (Binders<air::ast::Typ>, Expr)>,
    inlining_stack: &mut HashSet<Ident>,
    is_eligible: &F,
) -> Expr
where
    F: Fn(&Ident, &(Binders<air::ast::Typ>, Expr)) -> bool,
{
    match &**expr {
        ExprX::Apply(func_name, args) => {
            let inlined_args: Vec<Expr> = args
                .iter()
                .map(|arg| inline_functions_rec(arg, decls, inlining_stack, is_eligible))
                .collect();

            if let Some(decl) = decls.get(func_name) {
                let (binders, body) = decl;

                if !is_eligible(func_name, decl) {
                    return Arc::new(ExprX::Apply(func_name.clone(), Arc::new(inlined_args)));
                }

                if inlining_stack.contains(func_name) {
                    return Arc::new(ExprX::Apply(func_name.clone(), Arc::new(inlined_args)));
                }

                if binders.len() == inlined_args.len() {
                    inlining_stack.insert(func_name.clone());

                    let mut result = body.clone();
                    for (binder, arg) in binders.iter().zip(inlined_args.iter()) {
                        result = subst_expr(&binder.name, arg, &result);
                    }

                    let final_result =
                        inline_functions_rec(&result, decls, inlining_stack, is_eligible);

                    inlining_stack.remove(func_name);

                    final_result
                } else {
                    Arc::new(ExprX::Apply(func_name.clone(), Arc::new(inlined_args)))
                }
            } else {
                Arc::new(ExprX::Apply(func_name.clone(), Arc::new(inlined_args)))
            }
        }

        ExprX::Const(_) | ExprX::Var(_) | ExprX::Old(_, _) => expr.clone(),

        ExprX::ApplyFun(typ, fun_expr, args) => {
            let inlined_fun = inline_functions_rec(fun_expr, decls, inlining_stack, is_eligible);
            let inlined_args: Vec<Expr> = args
                .iter()
                .map(|arg| inline_functions_rec(arg, decls, inlining_stack, is_eligible))
                .collect();
            Arc::new(ExprX::ApplyFun(typ.clone(), inlined_fun, Arc::new(inlined_args)))
        }

        ExprX::Unary(op, operand) => {
            let inlined = inline_functions_rec(operand, decls, inlining_stack, is_eligible);
            Arc::new(ExprX::Unary(*op, inlined))
        }

        ExprX::Binary(op, lhs, rhs) => {
            let inlined_lhs = inline_functions_rec(lhs, decls, inlining_stack, is_eligible);
            let inlined_rhs = inline_functions_rec(rhs, decls, inlining_stack, is_eligible);
            Arc::new(ExprX::Binary(op.clone(), inlined_lhs, inlined_rhs))
        }

        ExprX::Multi(op, operands) => {
            let inlined: Vec<Expr> = operands
                .iter()
                .map(|operand| inline_functions_rec(operand, decls, inlining_stack, is_eligible))
                .collect();
            Arc::new(ExprX::Multi(*op, Arc::new(inlined)))
        }

        ExprX::IfElse(cond, then_expr, else_expr) => {
            let inlined_cond = inline_functions_rec(cond, decls, inlining_stack, is_eligible);
            let inlined_then = inline_functions_rec(then_expr, decls, inlining_stack, is_eligible);
            let inlined_else = inline_functions_rec(else_expr, decls, inlining_stack, is_eligible);
            Arc::new(ExprX::IfElse(inlined_cond, inlined_then, inlined_else))
        }

        ExprX::Array(elements) => {
            let inlined: Vec<Expr> = elements
                .iter()
                .map(|elem| inline_functions_rec(elem, decls, inlining_stack, is_eligible))
                .collect();
            Arc::new(ExprX::Array(Arc::new(inlined)))
        }

        ExprX::Bind(bind, body) => {
            let inlined_body = inline_functions_rec(body, decls, inlining_stack, is_eligible);
            let inlined_bind = match &**bind {
                BindX::Let(binders) => {
                    let inlined_binders: Vec<Binder<Expr>> = binders
                        .iter()
                        .map(|binder| {
                            let inlined_expr =
                                inline_functions_rec(&binder.a, decls, inlining_stack, is_eligible);
                            Arc::new(BinderX { name: binder.name.clone(), a: inlined_expr })
                        })
                        .collect();
                    Arc::new(BindX::Let(Arc::new(inlined_binders)))
                }
                BindX::Quant(quant, binders, triggers, qid) => {
                    let inlined_triggers: Vec<_> = triggers
                        .iter()
                        .map(|trigger| {
                            let inlined_trigger: Vec<_> = trigger
                                .iter()
                                .map(|e| {
                                    inline_functions_rec(e, decls, inlining_stack, is_eligible)
                                })
                                .collect();
                            Arc::new(inlined_trigger)
                        })
                        .collect();
                    Arc::new(BindX::Quant(
                        *quant,
                        binders.clone(),
                        Arc::new(inlined_triggers),
                        qid.clone(),
                    ))
                }
                BindX::Lambda(binders, triggers, qid) => {
                    let inlined_triggers: Vec<_> = triggers
                        .iter()
                        .map(|trigger| {
                            let inlined_trigger: Vec<_> = trigger
                                .iter()
                                .map(|e| {
                                    inline_functions_rec(e, decls, inlining_stack, is_eligible)
                                })
                                .collect();
                            Arc::new(inlined_trigger)
                        })
                        .collect();
                    Arc::new(BindX::Lambda(
                        binders.clone(),
                        Arc::new(inlined_triggers),
                        qid.clone(),
                    ))
                }
                BindX::Choose(binders, triggers, qid, cond) => {
                    let inlined_triggers: Vec<_> = triggers
                        .iter()
                        .map(|trigger| {
                            let inlined_trigger: Vec<_> = trigger
                                .iter()
                                .map(|e| {
                                    inline_functions_rec(e, decls, inlining_stack, is_eligible)
                                })
                                .collect();
                            Arc::new(inlined_trigger)
                        })
                        .collect();
                    let inlined_cond =
                        inline_functions_rec(cond, decls, inlining_stack, is_eligible);
                    Arc::new(BindX::Choose(
                        binders.clone(),
                        Arc::new(inlined_triggers),
                        qid.clone(),
                        inlined_cond,
                    ))
                }
            };
            Arc::new(ExprX::Bind(inlined_bind, inlined_body))
        }

        ExprX::LabeledAxiom(msgs, filter, inner) => {
            let inlined = inline_functions_rec(inner, decls, inlining_stack, is_eligible);
            Arc::new(ExprX::LabeledAxiom(msgs.clone(), filter.clone(), inlined))
        }

        ExprX::LabeledAssertion(assert_id, msg, filter, inner) => {
            let inlined = inline_functions_rec(inner, decls, inlining_stack, is_eligible);
            Arc::new(ExprX::LabeledAssertion(
                assert_id.clone(),
                msg.clone(),
                filter.clone(),
                inlined,
            ))
        }
    }
}

/// Returns true if `expr` references any `tmp%` variable.
pub fn lhs_involves_tmp(expr: &Expr) -> bool {
    match &**expr {
        ExprX::Var(name) => name.as_str().contains("tmp%"),
        ExprX::Apply(_, args) => args.iter().any(lhs_involves_tmp),
        ExprX::Binary(_, a, b) => lhs_involves_tmp(a) || lhs_involves_tmp(b),
        ExprX::Unary(_, e) => lhs_involves_tmp(e),
        _ => false,
    }
}

/// Apply a rewrite rule once to an expression.
pub fn apply_rewrite_once<F>(expr: &Expr, rewrite: F) -> Expr
where
    F: Fn(&Expr) -> Option<Expr> + Copy,
{
    apply_rewrite_once_tracked(expr, rewrite).0
}

/// Like apply_rewrite_once but also returns whether any change occurred.
fn apply_rewrite_once_tracked<F>(expr: &Expr, rewrite: F) -> (Expr, bool)
where
    F: Fn(&Expr) -> Option<Expr> + Copy,
{
    if let Some(rewritten) = rewrite(expr) {
        return (rewritten, true);
    }

    macro_rules! recurse {
        ($e:expr) => {{ apply_rewrite_once_tracked($e, rewrite) }};
    }
    macro_rules! recurse_vec {
        ($args:expr) => {{
            let mut changed = false;
            let v: Vec<Expr> = $args
                .iter()
                .map(|a| {
                    let (e, c) = apply_rewrite_once_tracked(a, rewrite);
                    changed |= c;
                    e
                })
                .collect();
            (v, changed)
        }};
    }

    match &**expr {
        ExprX::Const(_) | ExprX::Var(_) | ExprX::Old(_, _) => (expr.clone(), false),
        ExprX::Apply(func_name, args) => {
            let (new_args, changed) = recurse_vec!(args);
            (Arc::new(ExprX::Apply(func_name.clone(), Arc::new(new_args))), changed)
        }
        ExprX::ApplyFun(typ, fun_expr, args) => {
            let (new_fun, cf) = recurse!(fun_expr);
            let (new_args, ca) = recurse_vec!(args);
            (Arc::new(ExprX::ApplyFun(typ.clone(), new_fun, Arc::new(new_args))), cf || ca)
        }
        ExprX::Unary(op, operand) => {
            let (new_op, c) = recurse!(operand);
            (Arc::new(ExprX::Unary(*op, new_op)), c)
        }
        ExprX::Binary(op, lhs, rhs) => {
            let (nl, cl) = recurse!(lhs);
            let (nr, cr) = recurse!(rhs);
            (Arc::new(ExprX::Binary(op.clone(), nl, nr)), cl || cr)
        }
        ExprX::Multi(op, operands) => {
            let (new_ops, changed) = recurse_vec!(operands);
            (Arc::new(ExprX::Multi(*op, Arc::new(new_ops))), changed)
        }
        ExprX::IfElse(cond, then_expr, else_expr) => {
            let (nc, cc) = recurse!(cond);
            let (nt, ct) = recurse!(then_expr);
            let (ne, ce) = recurse!(else_expr);
            (Arc::new(ExprX::IfElse(nc, nt, ne)), cc || ct || ce)
        }
        ExprX::Array(elements) => {
            let (new_elems, changed) = recurse_vec!(elements);
            (Arc::new(ExprX::Array(Arc::new(new_elems))), changed)
        }
        ExprX::Bind(bind, body) => {
            let (new_body, cb) = recurse!(body);
            let (new_bind, cbind) = match &**bind {
                BindX::Let(binders) => {
                    let mut changed = false;
                    let new_binders: Vec<Binder<Expr>> = binders
                        .iter()
                        .map(|b| {
                            let (new_expr, c) = apply_rewrite_once_tracked(&b.a, rewrite);
                            changed |= c;
                            Arc::new(BinderX { name: b.name.clone(), a: new_expr })
                        })
                        .collect();
                    (Arc::new(BindX::Let(Arc::new(new_binders))), changed)
                }
                BindX::Quant(quant, binders, triggers, qid) => {
                    let mut changed = false;
                    let new_triggers: Vec<_> = triggers
                        .iter()
                        .map(|trigger| {
                            let new_trigger: Vec<_> = trigger
                                .iter()
                                .map(|e| {
                                    let (ne, c) = apply_rewrite_once_tracked(e, rewrite);
                                    changed |= c;
                                    ne
                                })
                                .collect();
                            Arc::new(new_trigger)
                        })
                        .collect();
                    (
                        Arc::new(BindX::Quant(
                            *quant,
                            binders.clone(),
                            Arc::new(new_triggers),
                            qid.clone(),
                        )),
                        changed,
                    )
                }
                BindX::Lambda(binders, triggers, qid) => {
                    let mut changed = false;
                    let new_triggers: Vec<_> = triggers
                        .iter()
                        .map(|trigger| {
                            let new_trigger: Vec<_> = trigger
                                .iter()
                                .map(|e| {
                                    let (ne, c) = apply_rewrite_once_tracked(e, rewrite);
                                    changed |= c;
                                    ne
                                })
                                .collect();
                            Arc::new(new_trigger)
                        })
                        .collect();
                    (
                        Arc::new(BindX::Lambda(
                            binders.clone(),
                            Arc::new(new_triggers),
                            qid.clone(),
                        )),
                        changed,
                    )
                }
                BindX::Choose(binders, triggers, qid, cond) => {
                    let mut changed = false;
                    let new_triggers: Vec<_> = triggers
                        .iter()
                        .map(|trigger| {
                            let new_trigger: Vec<_> = trigger
                                .iter()
                                .map(|e| {
                                    let (ne, c) = apply_rewrite_once_tracked(e, rewrite);
                                    changed |= c;
                                    ne
                                })
                                .collect();
                            Arc::new(new_trigger)
                        })
                        .collect();
                    let (new_cond, cc) = apply_rewrite_once_tracked(cond, rewrite);
                    changed |= cc;
                    (
                        Arc::new(BindX::Choose(
                            binders.clone(),
                            Arc::new(new_triggers),
                            qid.clone(),
                            new_cond,
                        )),
                        changed,
                    )
                }
            };
            (Arc::new(ExprX::Bind(new_bind, new_body)), cbind || cb)
        }
        ExprX::LabeledAxiom(msgs, filter, inner_expr) => {
            let (new_inner, c) = recurse!(inner_expr);
            (Arc::new(ExprX::LabeledAxiom(msgs.clone(), filter.clone(), new_inner)), c)
        }
        ExprX::LabeledAssertion(assert_id, msg, filter, inner_expr) => {
            let (new_inner, c) = recurse!(inner_expr);
            (
                Arc::new(ExprX::LabeledAssertion(
                    assert_id.clone(),
                    msg.clone(),
                    filter.clone(),
                    new_inner,
                )),
                c,
            )
        }
    }
}

/// Apply a rewrite rule repeatedly until no more changes occur.
pub fn apply_rewrite<F>(expr: &Expr, rewrite: F) -> Expr
where
    F: Fn(&Expr) -> Option<Expr> + Copy,
{
    let mut current = expr.clone();
    loop {
        let (next, changed) = apply_rewrite_once_tracked(&current, rewrite);
        if !changed {
            break;
        }
        current = next;
    }
    current
}

/// Fold over all subexpressions in pre-order, accumulating a value.
pub fn fold_expr<A, F>(expr: &Expr, init: A, f: &F) -> A
where
    F: Fn(A, &Expr) -> A,
{
    let acc = f(init, expr);
    match &**expr {
        ExprX::Const(_) | ExprX::Var(_) | ExprX::Old(_, _) => acc,
        ExprX::Apply(_, args) | ExprX::Multi(_, args) | ExprX::Array(args) => {
            args.iter().fold(acc, |a, e| fold_expr(e, a, f))
        }
        ExprX::ApplyFun(_, func, args) => {
            let acc = fold_expr(func, acc, f);
            args.iter().fold(acc, |a, e| fold_expr(e, a, f))
        }
        ExprX::Unary(_, e) => fold_expr(e, acc, f),
        ExprX::Binary(_, l, r) => fold_expr(r, fold_expr(l, acc, f), f),
        ExprX::IfElse(c, t, e) => fold_expr(e, fold_expr(t, fold_expr(c, acc, f), f), f),
        ExprX::Bind(bind, body) => {
            let acc = if let BindX::Let(binders) = &**bind {
                binders.iter().fold(acc, |a, b| fold_expr(&b.a, a, f))
            } else {
                acc
            };
            fold_expr(body, acc, f)
        }
        ExprX::LabeledAxiom(_, _, inner) | ExprX::LabeledAssertion(_, _, _, inner) => {
            fold_expr(inner, acc, f)
        }
    }
}
