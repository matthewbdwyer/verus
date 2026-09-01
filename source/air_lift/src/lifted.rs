//! `LiftedExpr` — the source-level intermediate representation.
//!
//! A clean, structured AST sitting between AIR `Expr` and rendered output. Unlike
//! AIR's `ExprX`, `LiftedExpr` derives structural `PartialEq`/`Eq`/`Hash`, so
//! consumers can deduplicate (`HashSet<LiftedExpr>`) and pattern-match it — for
//! example to rewrite or simplify expressions. Shapes that don't lift structurally
//! fall back to [`LiftedExpr::Opaque`], which carries an already-rendered string.

use crate::types::FunctionRole;

/// A source-level variable occurrence, with its version/provenance classification.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LiftedName {
    /// User-visible base name (AIR suffixes/versions stripped).
    pub source_name: String,
    /// Weakest-precondition version number, if the occurrence was versioned
    /// (`x@3` → `3`).
    pub version: Option<u32>,
    /// Source line the version was produced at, if known.
    pub version_line: Option<u32>,
    /// Source line the variable was declared at, if known.
    pub decl_line: Option<u32>,
    /// How this occurrence relates to the user's variable.
    pub kind: NameKind,
    /// The Verus source-level type of this binder (e.g. `"int"`, `"u64"`), if known.
    /// Present for quantifier/choose/closure binders; `None` for other occurrences.
    pub typ: Option<String>,
}

/// Classification of a variable occurrence relative to the user's program.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum NameKind {
    /// The current value of a user variable.
    Current,
    /// A pre-state value (`old(x)`).
    Old,
    /// An intermediate weakest-precondition version introduced by control flow.
    Intermediate { reason: VersionReason },
    /// A binder introduced by a quantifier.
    QuantBinder,
    /// A solver-internal temporary introduced during verification-condition generation
    /// (e.g. AIR `tmp%N`). It has no user-facing source name — the provided renderers show
    /// its cleaned name like any variable — but it is classified so a consumer can act on
    /// it: minimisation passes can drop unreferenced temporaries, and a consumer splicing a
    /// fragment into a program can detect that such a name would need a binding.
    Temporary,
}

/// Why an intermediate version exists.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum VersionReason {
    /// Introduced across a loop iteration.
    Loop,
    /// Introduced by a mutation (assignment / `&mut`).
    Mutation,
    /// Introduced by a control-flow merge (join of branches).
    Merge,
}

/// A source-level function/operator identity applied in a [`LiftedExpr::FunctionCall`].
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct LiftedFunction {
    /// User-visible function name.
    pub source_name: String,
    /// Classified role (see [`crate::types::FunctionRole`]).
    pub role: FunctionRole,
    /// Number of leading type arguments (dropped when rendering).
    pub type_arg_count: usize,
}

/// A literal value.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LitValue {
    Bool(bool),
    /// Integer literal kept as its rendered text (handles bignum; keeps `Eq`/`Hash` cheap).
    Int(String),
    /// Real literal kept as its rendered text.
    Real(String),
}

/// Binary operators rendered infix. Non-infix AIR applications lift to
/// [`LiftedExpr::FunctionCall`] instead.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Eq,
    Ne,
    Lt,
    Le,
    Gt,
    Ge,
    And,
    Or,
    Implies,
    /// Extensional equality (`=~=`).
    ExtEq,
    BitAnd,
    BitOr,
    BitXor,
    Shl,
    Shr,
}

/// Unary operators rendered prefix.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum UnOp {
    Not,
    Neg,
    /// Bitwise complement (`!x` on an integer).
    BitNot,
    /// Dereference (`*x`) — e.g. the current value of a `&mut`.
    Deref,
}

/// Quantifier kind.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum QuantKind {
    Forall,
    Exists,
}

/// A lifted, source-level expression. See the module documentation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum LiftedExpr {
    Var(LiftedName),
    Literal(LitValue),
    BinaryOp {
        op: BinOp,
        lhs: Box<LiftedExpr>,
        rhs: Box<LiftedExpr>,
    },
    UnaryOp {
        op: UnOp,
        operand: Box<LiftedExpr>,
    },
    FunctionCall {
        func: LiftedFunction,
        args: Vec<LiftedExpr>,
    },
    /// Application of a function *value* (a `spec_fn`/closure), e.g. `g(x)`. Distinct from
    /// `FunctionCall`, whose callee is a *named* function.
    Apply {
        callee: Box<LiftedExpr>,
        args: Vec<LiftedExpr>,
    },
    FieldAccess {
        receiver: Box<LiftedExpr>,
        field: String,
    },
    Index {
        receiver: Box<LiftedExpr>,
        index: Box<LiftedExpr>,
    },
    Quantifier {
        kind: QuantKind,
        binders: Vec<LiftedName>,
        body: Box<LiftedExpr>,
        /// Trigger groups (`#[trigger]` / `#![trigger ..]`). Source-level in Verus, so
        /// carried faithfully; a consumer chooses whether to render them (the provided
        /// renderers do not). Not traversed by `fold_lifted`/`rewrite_lifted`.
        triggers: Vec<Vec<LiftedExpr>>,
    },
    IfThenElse {
        cond: Box<LiftedExpr>,
        then_: Box<LiftedExpr>,
        else_: Box<LiftedExpr>,
    },
    /// A tuple, `(a, b)`.
    Tuple(Vec<LiftedExpr>),
    /// Positional field access, `t.0`.
    TupleField { receiver: Box<LiftedExpr>, index: usize },
    /// A cast, `e as ty`.
    Cast { value: Box<LiftedExpr>, ty: String },
    /// A closure, `|a, b| body`.
    Closure { params: Vec<String>, body: Box<LiftedExpr>, triggers: Vec<Vec<LiftedExpr>> },
    /// A struct literal, `Type { f: a }`.
    StructLiteral { name: String, fields: Vec<(String, LiftedExpr)> },
    /// A method call on a receiver, `recv.name(args)`.
    MethodCall { receiver: Box<LiftedExpr>, method: String, args: Vec<LiftedExpr> },
    /// A `choose` binding, `choose|binder| predicate`.
    Choose {
        binders: Vec<LiftedName>,
        body: Box<LiftedExpr>,
        triggers: Vec<Vec<LiftedExpr>>,
    },
    /// An array literal, `[e1, e2, e3]`.
    ArrayLiteral(Vec<LiftedExpr>),
    /// Escape hatch: a shape that didn't lift structurally, carrying its
    /// already-rendered source string.
    Opaque(String),
}

impl LiftedExpr {
    /// Convenience: a current-value variable occurrence by name.
    pub fn var(name: impl Into<String>) -> LiftedExpr {
        LiftedExpr::Var(LiftedName {
            source_name: name.into(),
            version: None,
            version_line: None,
            decl_line: None,
            kind: NameKind::Current,
            typ: None,
        })
    }
}

/// Fold over every subexpression of a `LiftedExpr` in pre-order, accumulating a value.
///
/// The lifted-IR mirror of [`crate::expr_utils::fold_expr`]. It descends through the
/// structural children of each node (operands, arguments, receivers, bodies, tuple and
/// array elements, struct-field values). It does **not** descend into binder metadata
/// such as quantifier/closure/choose trigger groups: triggers are instantiation hints,
/// not part of the expression's value, so folding (and the `collect_vars`-style queries
/// built on it) treats them as opaque.
pub fn fold_lifted<A, F>(expr: &LiftedExpr, init: A, f: &F) -> A
where
    F: Fn(A, &LiftedExpr) -> A,
{
    let acc = f(init, expr);
    match expr {
        LiftedExpr::Var(_) | LiftedExpr::Literal(_) | LiftedExpr::Opaque(_) => acc,
        LiftedExpr::BinaryOp { lhs, rhs, .. } => fold_lifted(rhs, fold_lifted(lhs, acc, f), f),
        LiftedExpr::UnaryOp { operand, .. } => fold_lifted(operand, acc, f),
        LiftedExpr::FunctionCall { args, .. } => {
            args.iter().fold(acc, |a, e| fold_lifted(e, a, f))
        }
        LiftedExpr::Apply { callee, args } => {
            let acc = fold_lifted(callee, acc, f);
            args.iter().fold(acc, |a, e| fold_lifted(e, a, f))
        }
        LiftedExpr::FieldAccess { receiver, .. } => fold_lifted(receiver, acc, f),
        LiftedExpr::Index { receiver, index } => {
            fold_lifted(index, fold_lifted(receiver, acc, f), f)
        }
        LiftedExpr::Quantifier { body, .. } => fold_lifted(body, acc, f),
        LiftedExpr::IfThenElse { cond, then_, else_ } => {
            fold_lifted(else_, fold_lifted(then_, fold_lifted(cond, acc, f), f), f)
        }
        LiftedExpr::Tuple(es) | LiftedExpr::ArrayLiteral(es) => {
            es.iter().fold(acc, |a, e| fold_lifted(e, a, f))
        }
        LiftedExpr::TupleField { receiver, .. } => fold_lifted(receiver, acc, f),
        LiftedExpr::Cast { value, .. } => fold_lifted(value, acc, f),
        LiftedExpr::Closure { body, .. } => fold_lifted(body, acc, f),
        LiftedExpr::StructLiteral { fields, .. } => {
            fields.iter().fold(acc, |a, (_, e)| fold_lifted(e, a, f))
        }
        LiftedExpr::MethodCall { receiver, args, .. } => {
            let acc = fold_lifted(receiver, acc, f);
            args.iter().fold(acc, |a, e| fold_lifted(e, a, f))
        }
        LiftedExpr::Choose { body, .. } => fold_lifted(body, acc, f),
    }
}

/// Rewrite a `LiftedExpr` by applying `rewrite` repeatedly until it reaches a fixpoint.
///
/// The lifted-IR mirror of [`crate::expr_utils::apply_rewrite`]. At each node `rewrite`
/// is tried first; if it returns `Some`, that replacement is taken and the process
/// repeats, otherwise the node's children are rewritten. This drives, for example,
/// closure-body substitution (replace a binder occurrence) and tuple-projection collapse
/// (`TupleField(Tuple([..]), i) -> e_i`). Binder trigger metadata is not rewritten, for
/// the same reason `fold_lifted` does not descend into it.
pub fn rewrite_lifted<F>(expr: &LiftedExpr, rewrite: F) -> LiftedExpr
where
    F: Fn(&LiftedExpr) -> Option<LiftedExpr> + Copy,
{
    let mut current = expr.clone();
    loop {
        let (next, changed) = rewrite_lifted_once_tracked(&current, rewrite);
        if !changed {
            break;
        }
        current = next;
    }
    current
}

/// One bottom-up rewrite pass, also reporting whether anything changed.
fn rewrite_lifted_once_tracked<F>(expr: &LiftedExpr, rewrite: F) -> (LiftedExpr, bool)
where
    F: Fn(&LiftedExpr) -> Option<LiftedExpr> + Copy,
{
    if let Some(rewritten) = rewrite(expr) {
        return (rewritten, true);
    }
    macro_rules! recurse {
        ($e:expr) => {{
            let (e, c) = rewrite_lifted_once_tracked($e, rewrite);
            (Box::new(e), c)
        }};
    }
    macro_rules! recurse_vec {
        ($items:expr) => {{
            let mut changed = false;
            let v: Vec<LiftedExpr> = $items
                .iter()
                .map(|a| {
                    let (e, c) = rewrite_lifted_once_tracked(a, rewrite);
                    changed |= c;
                    e
                })
                .collect();
            (v, changed)
        }};
    }
    match expr {
        LiftedExpr::Var(_) | LiftedExpr::Literal(_) | LiftedExpr::Opaque(_) => (expr.clone(), false),
        LiftedExpr::BinaryOp { op, lhs, rhs } => {
            let (nl, cl) = recurse!(lhs);
            let (nr, cr) = recurse!(rhs);
            (LiftedExpr::BinaryOp { op: *op, lhs: nl, rhs: nr }, cl || cr)
        }
        LiftedExpr::UnaryOp { op, operand } => {
            let (no, c) = recurse!(operand);
            (LiftedExpr::UnaryOp { op: *op, operand: no }, c)
        }
        LiftedExpr::FunctionCall { func, args } => {
            let (na, c) = recurse_vec!(args);
            (LiftedExpr::FunctionCall { func: func.clone(), args: na }, c)
        }
        LiftedExpr::Apply { callee, args } => {
            let (nc, cc) = recurse!(callee);
            let (na, ca) = recurse_vec!(args);
            (LiftedExpr::Apply { callee: nc, args: na }, cc || ca)
        }
        LiftedExpr::FieldAccess { receiver, field } => {
            let (nr, c) = recurse!(receiver);
            (LiftedExpr::FieldAccess { receiver: nr, field: field.clone() }, c)
        }
        LiftedExpr::Index { receiver, index } => {
            let (nr, cr) = recurse!(receiver);
            let (ni, ci) = recurse!(index);
            (LiftedExpr::Index { receiver: nr, index: ni }, cr || ci)
        }
        LiftedExpr::Quantifier { kind, binders, body, triggers } => {
            let (nb, c) = recurse!(body);
            (
                LiftedExpr::Quantifier {
                    kind: *kind,
                    binders: binders.clone(),
                    body: nb,
                    triggers: triggers.clone(),
                },
                c,
            )
        }
        LiftedExpr::IfThenElse { cond, then_, else_ } => {
            let (nc, cc) = recurse!(cond);
            let (nt, ct) = recurse!(then_);
            let (ne, ce) = recurse!(else_);
            (LiftedExpr::IfThenElse { cond: nc, then_: nt, else_: ne }, cc || ct || ce)
        }
        LiftedExpr::Tuple(es) => {
            let (ne, c) = recurse_vec!(es);
            (LiftedExpr::Tuple(ne), c)
        }
        LiftedExpr::ArrayLiteral(es) => {
            let (ne, c) = recurse_vec!(es);
            (LiftedExpr::ArrayLiteral(ne), c)
        }
        LiftedExpr::TupleField { receiver, index } => {
            let (nr, c) = recurse!(receiver);
            (LiftedExpr::TupleField { receiver: nr, index: *index }, c)
        }
        LiftedExpr::Cast { value, ty } => {
            let (nv, c) = recurse!(value);
            (LiftedExpr::Cast { value: nv, ty: ty.clone() }, c)
        }
        LiftedExpr::Closure { params, body, triggers } => {
            let (nb, c) = recurse!(body);
            (
                LiftedExpr::Closure {
                    params: params.clone(),
                    body: nb,
                    triggers: triggers.clone(),
                },
                c,
            )
        }
        LiftedExpr::StructLiteral { name, fields } => {
            let mut changed = false;
            let nf: Vec<(String, LiftedExpr)> = fields
                .iter()
                .map(|(k, e)| {
                    let (ne, c) = rewrite_lifted_once_tracked(e, rewrite);
                    changed |= c;
                    (k.clone(), ne)
                })
                .collect();
            (LiftedExpr::StructLiteral { name: name.clone(), fields: nf }, changed)
        }
        LiftedExpr::MethodCall { receiver, method, args } => {
            let (nr, cr) = recurse!(receiver);
            let (na, ca) = recurse_vec!(args);
            (LiftedExpr::MethodCall { receiver: nr, method: method.clone(), args: na }, cr || ca)
        }
        LiftedExpr::Choose { binders, body, triggers } => {
            let (nb, c) = recurse!(body);
            (
                LiftedExpr::Choose {
                    binders: binders.clone(),
                    body: nb,
                    triggers: triggers.clone(),
                },
                c,
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::HashSet;

    fn le(n: u64) -> LiftedExpr {
        LiftedExpr::Literal(LitValue::Int(n.to_string()))
    }

    #[test]
    fn structural_equality() {
        // x < 100 built twice compares equal (structural, unlike AIR Expr).
        let build = || LiftedExpr::BinaryOp {
            op: BinOp::Lt,
            lhs: Box::new(LiftedExpr::var("x")),
            rhs: Box::new(le(100)),
        };
        assert_eq!(build(), build());
    }

    #[test]
    fn hashset_dedup() {
        // Equal LiftedExprs collapse in a HashSet — the dedup consumers rely on.
        let mut set = HashSet::new();
        set.insert(LiftedExpr::var("x"));
        set.insert(LiftedExpr::var("x"));
        set.insert(LiftedExpr::var("y"));
        assert_eq!(set.len(), 2);
    }

    #[test]
    fn opaque_roundtrips() {
        let o = LiftedExpr::Opaque("<uninterpretable>".to_string());
        match o {
            LiftedExpr::Opaque(s) => assert_eq!(s, "<uninterpretable>"),
            _ => panic!("expected Opaque"),
        }
    }

    #[test]
    fn fold_lifted_collects_variable_names() {
        // fold over `x < 100 && f(y)` visits both variable occurrences.
        let e = LiftedExpr::BinaryOp {
            op: BinOp::And,
            lhs: Box::new(LiftedExpr::BinaryOp {
                op: BinOp::Lt,
                lhs: Box::new(LiftedExpr::var("x")),
                rhs: Box::new(le(100)),
            }),
            rhs: Box::new(LiftedExpr::FunctionCall {
                func: LiftedFunction {
                    source_name: "f".to_string(),
                    role: FunctionRole::UserDefined { type_arg_count: 0, is_method: false },
                    type_arg_count: 0,
                },
                args: vec![LiftedExpr::var("y")],
            }),
        };
        let names = fold_lifted(&e, HashSet::new(), &|mut acc, node| {
            if let LiftedExpr::Var(n) = node {
                acc.insert(n.source_name.clone());
            }
            acc
        });
        assert_eq!(names, HashSet::from(["x".to_string(), "y".to_string()]));
    }

    #[test]
    fn rewrite_lifted_collapses_tuple_projection() {
        // `(a, b).1` rewrites to `b`, to a fixpoint, anywhere in the tree.
        let projection = LiftedExpr::TupleField {
            receiver: Box::new(LiftedExpr::Tuple(vec![LiftedExpr::var("a"), LiftedExpr::var("b")])),
            index: 1,
        };
        let wrapped = LiftedExpr::UnaryOp { op: UnOp::Not, operand: Box::new(projection) };
        let out = rewrite_lifted(&wrapped, |e| {
            if let LiftedExpr::TupleField { receiver, index } = e
                && let LiftedExpr::Tuple(elems) = receiver.as_ref()
                && *index < elems.len()
            {
                return Some(elems[*index].clone());
            }
            None
        });
        assert_eq!(out, LiftedExpr::UnaryOp { op: UnOp::Not, operand: Box::new(LiftedExpr::var("b")) });
    }

    #[test]
    fn rewrite_lifted_substitutes_a_binder() {
        // Substitute the binder `arg` with the concrete value `5` in `arg < 100`.
        let body = LiftedExpr::BinaryOp {
            op: BinOp::Lt,
            lhs: Box::new(LiftedExpr::var("arg")),
            rhs: Box::new(le(100)),
        };
        let out = rewrite_lifted(&body, |e| {
            if let LiftedExpr::Var(n) = e
                && n.source_name == "arg"
            {
                return Some(le(5));
            }
            None
        });
        assert_eq!(
            out,
            LiftedExpr::BinaryOp { op: BinOp::Lt, lhs: Box::new(le(5)), rhs: Box::new(le(100)) }
        );
    }
}
