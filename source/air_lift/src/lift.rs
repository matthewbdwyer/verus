//! `lift_expr` — classify an AIR `Expr` into the source-level [`LiftedExpr`] IR.
//!
//! Classification consults a [`crate::pipeline::PipelineContext`] to recover
//! source-level names, function roles, and variable versions from the AIR encoding.
//! Lifting is **total**: a shape with no structural counterpart becomes
//! [`LiftedExpr::Opaque`], carrying a structural key, so lifting never fails.

use crate::air_names::{self, AirName, clean_air_name};
use crate::expr_utils;
use crate::lifted::{
    BinOp, LiftedExpr, LiftedFunction, LiftedName, LitValue, NameKind, QuantKind, UnOp,
    VersionReason,
};
use crate::pipeline::PipelineContext;
use crate::types::{FunctionRole, IntermediateKind, VarInfo};
use crate::var_info::parse_versioned;
use air::ast::{BinaryOp, BindX, Constant, Expr, ExprX, Exprs, Ident, MultiOp, Quant, UnaryOp};
use vir::def::{ADD, EUC_DIV, EUC_MOD, MUL, RADD, RDIV, RMUL, RSUB, SUB};
use std::sync::Arc;

/// Lifts AIR `Expr` into [`LiftedExpr`], using an accumulated [`PipelineContext`]
/// for variable/function classification.
pub struct Lifter<'a> {
    ctx: &'a PipelineContext,
}

/// Convenience: lift `expr` in the context `ctx`.
pub fn lift_expr(expr: &Expr, ctx: &PipelineContext) -> LiftedExpr {
    Lifter::new(ctx).lift(expr)
}

impl<'a> Lifter<'a> {
    pub fn new(ctx: &'a PipelineContext) -> Self {
        Lifter { ctx }
    }

    /// Lift a single AIR expression.
    pub fn lift(&self, expr: &Expr) -> LiftedExpr {
        match &**expr {
            ExprX::Const(c) => lift_const(c),
            ExprX::Var(name) => self.lift_var(name),
            ExprX::Old(_snap, var) => self.lift_old(var),
            ExprX::Apply(f, args) => self.lift_apply(expr, f, args),
            ExprX::Binary(op, l, r) => {
                // Strip typing guards: `(has_type x T) ==> P` / `(sized x) ==> P` reduce to P.
                if matches!(op, BinaryOp::Implies) && is_type_guard(l) {
                    self.lift(r)
                } else {
                    match map_binop(op) {
                        Some(bop) => LiftedExpr::BinaryOp {
                            op: bop,
                            lhs: Box::new(self.lift(l)),
                            rhs: Box::new(self.lift(r)),
                        },
                        None => opaque(expr),
                    }
                }
            }
            ExprX::Unary(UnaryOp::Not, e) => {
                LiftedExpr::UnaryOp { op: UnOp::Not, operand: Box::new(self.lift(e)) }
            }
            ExprX::Unary(UnaryOp::BitNot, e) => {
                LiftedExpr::UnaryOp { op: UnOp::BitNot, operand: Box::new(self.lift(e)) }
            }
            ExprX::Unary(UnaryOp::BitNeg, e) => {
                LiftedExpr::UnaryOp { op: UnOp::Neg, operand: Box::new(self.lift(e)) }
            }
            // Real conversions read as they do in source.
            ExprX::Unary(UnaryOp::ToReal, e) => LiftedExpr::Cast {
                value: Box::new(self.lift(e)),
                ty: "real".to_string(),
            },
            ExprX::Unary(UnaryOp::RealToInt, e) => LiftedExpr::MethodCall {
                receiver: Box::new(self.lift(e)),
                method: "floor".to_string(),
                args: vec![],
            },
            // A width coercion carries no source-level meaning; the value does.
            ExprX::Unary(
                UnaryOp::BitZeroExtend(_) | UnaryOp::BitSignExtend(_) | UnaryOp::BitExtract(_, _),
                e,
            ) => self.lift(e),
            ExprX::Multi(op, es) => self.lift_multi(op, es, expr),
            ExprX::IfElse(c, t, e) => LiftedExpr::IfThenElse {
                cond: Box::new(self.lift(c)),
                then_: Box::new(self.lift(t)),
                else_: Box::new(self.lift(e)),
            },
            ExprX::Array(es) => {
                LiftedExpr::ArrayLiteral(es.iter().map(|a| self.lift(a)).collect())
            }
            ExprX::Bind(bind, body) => self.lift_bind(bind, body, expr),
            ExprX::ApplyFun(_ty, callee, args) => LiftedExpr::Apply {
                callee: Box::new(self.lift(callee)),
                args: args.iter().map(|a| self.lift(a)).collect(),
            },
            ExprX::LabeledAxiom(_, _, e) => self.lift(e),
            ExprX::LabeledAssertion(_, _, _, e) => self.lift(e),
            // The remaining unary ops are SMT FloatingPoint-theory primitives (FloatNeg,
            // FloatIsNaN, FloatFromIeeeBits, ...). Verus source float operations lower to named
            // `ieee_float_*` functions, so these AIR ops have no source-level form. No wildcard,
            // so a new ExprX variant breaks the build.
            ExprX::Unary(_, _) => opaque(expr),
        }
    }

    fn lift_var(&self, name: &Ident) -> LiftedExpr {
        let (_, version) = parse_versioned(name.as_str());
        let decl_line = self.ctx.variable_def_lines.get(name).copied();
        let lname = match self.ctx.variable_info.get(name) {
            Some(VarInfo::Current { clean_name }) => LiftedName {
                source_name: clean_name.clone(),
                version,
                version_line: None,
                decl_line,
                kind: NameKind::Current,
                typ: None,
            },
            Some(VarInfo::Old { clean_name }) => LiftedName {
                source_name: clean_name.clone(),
                version: None,
                version_line: None,
                decl_line,
                kind: NameKind::Old,
                typ: None,
            },
            Some(VarInfo::Intermediate { clean_name, line, kind }) => {
                let nk = match kind {
                    IntermediateKind::Loop => {
                        NameKind::Intermediate { reason: VersionReason::Loop }
                    }
                    IntermediateKind::Merge => {
                        NameKind::Intermediate { reason: VersionReason::Merge }
                    }
                    IntermediateKind::Mutation => {
                        NameKind::Intermediate { reason: VersionReason::Mutation }
                    }
                    IntermediateKind::QuantBinder => NameKind::QuantBinder,
                };
                let version_line =
                    if matches!(kind, IntermediateKind::QuantBinder) { None } else { Some(*line) };
                LiftedName {
                    source_name: clean_name.clone(),
                    version,
                    version_line,
                    decl_line,
                    kind: nk,
                    typ: None,
                }
            }
            // A solver-internal temporary: carry the classification (rather than
            // degrading to Current) so a consumer can recognise and act on it. Its cleaned
            // name still renders like any variable.
            Some(VarInfo::Temporary) => LiftedName {
                source_name: clean_air_name(name.as_str()),
                version,
                version_line: None,
                decl_line,
                kind: NameKind::Temporary,
                typ: None,
            },
            // Noise (and unclassified names) degrade to a cleaned current-value name.
            Some(VarInfo::Noise) | None => LiftedName {
                source_name: clean_air_name(name.as_str()),
                version,
                version_line: None,
                decl_line,
                kind: NameKind::Current,
                typ: None,
            },
        };
        LiftedExpr::Var(lname)
    }

    fn lift_old(&self, var: &Ident) -> LiftedExpr {
        let source_name = match self.ctx.variable_info.get(var) {
            Some(VarInfo::Current { clean_name }) | Some(VarInfo::Old { clean_name }) => {
                clean_name.clone()
            }
            _ => clean_air_name(var.as_str()),
        };
        LiftedExpr::Var(LiftedName {
            source_name,
            version: None,
            version_line: None,
            decl_line: None,
            kind: NameKind::Old,
            typ: None,
        })
    }

    fn lift_multi(&self, op: &MultiOp, es: &Exprs, expr: &Expr) -> LiftedExpr {
        // `distinct(a, b, c, ..)` reads as the pairwise inequality `a != b && a != c && b != c`.
        if let MultiOp::Distinct = op {
            let items: Vec<LiftedExpr> = es.iter().map(|e| self.lift(e)).collect();
            let mut pairs: Vec<LiftedExpr> = Vec::new();
            for i in 0..items.len() {
                for j in (i + 1)..items.len() {
                    pairs.push(LiftedExpr::BinaryOp {
                        op: BinOp::Ne,
                        lhs: Box::new(items[i].clone()),
                        rhs: Box::new(items[j].clone()),
                    });
                }
            }
            let mut it = pairs.into_iter();
            return match it.next() {
                None => opaque(expr), // fewer than two operands: nothing to compare
                Some(first) => it.fold(first, |acc, p| LiftedExpr::BinaryOp {
                    op: BinOp::And,
                    lhs: Box::new(acc),
                    rhs: Box::new(p),
                }),
            };
        }
        let bop = match op {
            MultiOp::And => BinOp::And,
            MultiOp::Or => BinOp::Or,
            MultiOp::Add => BinOp::Add,
            MultiOp::Sub => BinOp::Sub,
            MultiOp::Mul => BinOp::Mul,
            MultiOp::Xor => BinOp::BitXor,
            // Float is an IEEE FP constructor from bit fields — no Verus surface form.
            // Enumerated (no wildcard) so a new MultiOp variant breaks the build.
            MultiOp::Distinct | MultiOp::Float => return opaque(expr),
        };
        match es.len() {
            0 => opaque(expr),
            1 => self.lift(&es[0]),
            _ => {
                let mut acc = self.lift(&es[0]);
                for e in &es[1..] {
                    acc = LiftedExpr::BinaryOp {
                        op: bop,
                        lhs: Box::new(acc),
                        rhs: Box::new(self.lift(e)),
                    };
                }
                acc
            }
        }
    }

    fn lift_apply(&self, expr: &Expr, f: &Ident, args: &Exprs) -> LiftedExpr {
        // Box/unbox coercions are transparent.
        if args.len() == 1
            && matches!(AirName::parse(f.as_str()), AirName::Boxed(_) | AirName::Unboxed(_))
        {
            return self.lift(&args[0]);
        }

        // Application of a function value: `%%apply%%N(f, a1, ..)` reads as `f(a1, ..)` —
        // the first argument is the callee, the rest are its arguments.
        if f.as_str().starts_with(air_names::APPLY) && !args.is_empty() {
            return LiftedExpr::Apply {
                callee: Box::new(self.lift(&args[0])),
                args: args[1..].iter().map(|a| self.lift(a)).collect(),
            };
        }

        // Arithmetic encoded as an application (Add/Sub/Mul/EucDiv/EucMod).
        let stripped = f.as_str().trim_start_matches(air_names::AIR_POLY_PREFIX);
        if args.len() == 2 {
            let bop = if stripped == ADD {
                Some(BinOp::Add)
            } else if stripped == SUB {
                Some(BinOp::Sub)
            } else if stripped == MUL {
                Some(BinOp::Mul)
            } else if stripped == EUC_DIV {
                Some(BinOp::Div)
            } else if stripped == EUC_MOD {
                Some(BinOp::Mod)
            } else if stripped == RADD {
                Some(BinOp::Add)
            } else if stripped == RSUB {
                Some(BinOp::Sub)
            } else if stripped == RMUL {
                Some(BinOp::Mul)
            } else if stripped == RDIV {
                Some(BinOp::Div)
            } else {
                None
            };
            if let Some(bop) = bop {
                return LiftedExpr::BinaryOp {
                    op: bop,
                    lhs: Box::new(self.lift(&args[0])),
                    rhs: Box::new(self.lift(&args[1])),
                };
            }
        }

        // An application of a recorded closure reads as the closure itself, with the
        // application's arguments substituted for the body's placeholders.
        if let Some((params, body)) = self.ctx.lambda_decls.get(f) {
            let mut resolved = body.clone();
            for (i, arg) in args.iter().enumerate() {
                let hole: Ident = Arc::new(format!("{}{}", air_names::HOLE, i));
                resolved = expr_utils::subst_expr(&hole, arg, &resolved);
            }
            return LiftedExpr::Closure {
                params: params.iter().map(|p| clean_air_name(p.as_str())).collect(),
                body: Box::new(self.lift(&resolved)),
                triggers: Vec::new(),
            };
        }
        match self.ctx.function_roles.get(f).cloned() {
            Some(role) => self.lift_role(f, role, args),
            // An AIR-internal name with no classification is an encoding this crate does
            // not recognise. Report it and lift to `Opaque`, rather than presenting the
            // raw internal name as though it were source.
            None if air_names::is_air_internal(f.as_str()) => {
                debug_assert!(false, "unclassified AIR-internal function: {}", f.as_str());
                tracing::warn!(
                    name = f.as_str(),
                    "unclassified AIR-internal function; lifting as Opaque"
                );
                opaque(expr)
            }
            None => self.lift_call(f, args, 0, false),
        }
    }

    fn lift_role(&self, f: &Ident, role: FunctionRole, args: &Exprs) -> LiftedExpr {
        let tac = role.type_arg_count();
        let vargs: &[Expr] = if args.len() >= tac { &args[tac..] } else { &args[..] };
        match &role {
            FunctionRole::ExtEq if vargs.len() >= 2 => {
                // ext_eq(deep_flag, <type args>, a, b) — operands are the last two.
                let n = vargs.len();
                LiftedExpr::BinaryOp {
                    op: BinOp::ExtEq,
                    lhs: Box::new(self.lift(&vargs[n - 2])),
                    rhs: Box::new(self.lift(&vargs[n - 1])),
                }
            }
            FunctionRole::FieldAccessor { .. } if vargs.len() == 1 => LiftedExpr::FieldAccess {
                receiver: Box::new(self.lift(&vargs[0])),
                field: self.field_name(f),
            },
            FunctionRole::IndexOp { .. } if vargs.len() == 2 => LiftedExpr::Index {
                receiver: Box::new(self.lift(&vargs[0])),
                index: Box::new(self.lift(&vargs[1])),
            },
            FunctionRole::LenMethod { .. } if vargs.len() == 1 => LiftedExpr::FunctionCall {
                func: LiftedFunction {
                    source_name: "len".to_string(),
                    role: role.clone(),
                    type_arg_count: tac,
                },
                args: vec![self.lift(&vargs[0])],
            },
            FunctionRole::PushMethod { .. } if vargs.len() == 2 => LiftedExpr::MethodCall {
                receiver: Box::new(self.lift(&vargs[0])),
                method: "push".to_string(),
                args: vec![self.lift(&vargs[1])],
            },
            FunctionRole::AddOp { .. } if vargs.len() == 2 => LiftedExpr::MethodCall {
                receiver: Box::new(self.lift(&vargs[0])),
                method: "insert".to_string(),
                args: vec![self.lift(&vargs[1])],
            },
            FunctionRole::Clip | FunctionRole::IntCoerce | FunctionRole::SpecUnwrap
                if !vargs.is_empty() =>
            {
                self.lift(vargs.last().unwrap())
            }
            // A range invariant states the bounds a type already implies, so the source-level
            // reading is the value itself.
            FunctionRole::RangeInvariant if !vargs.is_empty() => {
                self.lift(vargs.last().unwrap())
            }
            // Binary bitwise operators are rendered infix.
            FunctionRole::BitBinOp | FunctionRole::ArithOp if vargs.len() == 2 => {
                let stripped = f.as_str().trim_start_matches(air_names::AIR_POLY_PREFIX);
                match bit_binop(stripped) {
                    Some(op) => LiftedExpr::BinaryOp {
                        op,
                        lhs: Box::new(self.lift(&vargs[0])),
                        rhs: Box::new(self.lift(&vargs[1])),
                    },
                    None => self.lift_call(f, args, tac, false),
                }
            }
            FunctionRole::BitShl if vargs.len() == 2 => LiftedExpr::BinaryOp {
                op: BinOp::Shl,
                lhs: Box::new(self.lift(&vargs[0])),
                rhs: Box::new(self.lift(&vargs[1])),
            },
            FunctionRole::BitShr if vargs.len() == 2 => LiftedExpr::BinaryOp {
                op: BinOp::Shr,
                lhs: Box::new(self.lift(&vargs[0])),
                rhs: Box::new(self.lift(&vargs[1])),
            },
            FunctionRole::BitNot if vargs.len() == 1 => LiftedExpr::UnaryOp {
                op: UnOp::BitNot,
                operand: Box::new(self.lift(&vargs[0])),
            },
            // A decreases check compares the measure before and after; the third argument says
            // whether equality is allowed.
            FunctionRole::TerminationCheck if vargs.len() >= 2 => {
                let allows_equal = matches!(
                    vargs.get(2).map(|e| &**e),
                    Some(ExprX::Const(Constant::Bool(true)))
                );
                LiftedExpr::BinaryOp {
                    op: if allows_equal { BinOp::Le } else { BinOp::Lt },
                    lhs: Box::new(self.lift(&vargs[0])),
                    rhs: Box::new(self.lift(&vargs[1])),
                }
            }
            FunctionRole::MutRefCurrent if vargs.len() == 1 => {
                LiftedExpr::UnaryOp { op: UnOp::Deref, operand: Box::new(self.lift(&vargs[0])) }
            }
            FunctionRole::VariantDiscriminant { .. } if vargs.len() == 1 => {
                LiftedExpr::FunctionCall {
                    func: LiftedFunction {
                        source_name: String::new(),
                        role: role.clone(),
                        type_arg_count: tac,
                    },
                    args: vec![self.lift(&vargs[0])],
                }
            }
            FunctionRole::MutRefFuture if vargs.len() == 1 => {
                // `mut_ref_future%(m)` is the surface `*final(m)`; the future value is
                // version-independent, so strip any `old(...)` wrapper.
                let inner = strip_old(self.lift(&vargs[0]));
                LiftedExpr::UnaryOp {
                    op: UnOp::Deref,
                    operand: Box::new(LiftedExpr::FunctionCall {
                        func: user_fn("final"),
                        args: vec![inner],
                    }),
                }
            }
            FunctionRole::ClosureEns if vargs.len() == 3 => LiftedExpr::FunctionCall {
                func: role_fn("call_ensures", FunctionRole::ClosureEns),
                args: vargs.iter().map(|a| self.lift(a)).collect(),
            },
            FunctionRole::ClosureReq if vargs.len() == 2 => LiftedExpr::FunctionCall {
                func: role_fn("call_requires", FunctionRole::ClosureReq),
                args: vargs.iter().map(|a| self.lift(a)).collect(),
            },
            FunctionRole::HasResolved if !vargs.is_empty() => LiftedExpr::FunctionCall {
                func: user_fn("has_resolved"),
                args: vec![self.lift(vargs.last().unwrap())],
            },
            // A tuple constructor reads as a tuple; a projection as positional field access.
            FunctionRole::TupleConstructor { .. } => {
                LiftedExpr::Tuple(vargs.iter().map(|a| self.lift(a)).collect())
            }
            FunctionRole::TupleProjection { index, .. } if !vargs.is_empty() => {
                LiftedExpr::TupleField {
                    receiver: Box::new(self.lift(&vargs[0])),
                    index: *index,
                }
            }
            // `Option::unwrap` reads as the method it is.
            FunctionRole::OptionUnwrap if !vargs.is_empty() => LiftedExpr::MethodCall {
                receiver: Box::new(self.lift(vargs.last().unwrap())),
                method: "unwrap".to_string(),
                args: vec![],
            },
            // Sequence slicing: `subrange(s, 0, n)` is `s.take(n)`, `subrange(s, n, s.len())`
            // is `s.skip(n)`, and otherwise `s.subrange(a, b)`.
            FunctionRole::SubrangeOp { .. } if vargs.len() == 3 => {
                let recv = self.lift(&vargs[0]);
                let starts_at_zero =
                    matches!(&*vargs[1], ExprX::Const(Constant::Nat(n)) if n.as_str() == "0");
                let ends_at_len = self.is_len_of(&vargs[2], &vargs[0]);
                if starts_at_zero {
                    LiftedExpr::MethodCall {
                        receiver: Box::new(recv),
                        method: "take".to_string(),
                        args: vec![self.lift(&vargs[2])],
                    }
                } else if ends_at_len {
                    LiftedExpr::MethodCall {
                        receiver: Box::new(recv),
                        method: "skip".to_string(),
                        args: vec![self.lift(&vargs[1])],
                    }
                } else {
                    LiftedExpr::MethodCall {
                        receiver: Box::new(recv),
                        method: "subrange".to_string(),
                        args: vec![self.lift(&vargs[1]), self.lift(&vargs[2])],
                    }
                }
            }
            // Membership: on a map's domain it reads as `m.contains_key(k)`, otherwise
            // `s.contains(k)`. The finite-to-infinite set conversion is machinery.
            FunctionRole::ContainsKeyOp { .. } if vargs.len() == 2 => {
                let set = self.peel_named_call(&vargs[0], "::to_iset");
                let key = self.lift(&vargs[1]);
                match self.named_call_receiver(set, "::dom") {
                    Some(map) => LiftedExpr::MethodCall {
                        receiver: Box::new(self.lift(map)),
                        method: "contains_key".to_string(),
                        args: vec![key],
                    },
                    None => LiftedExpr::MethodCall {
                        receiver: Box::new(self.lift(set)),
                        method: "contains".to_string(),
                        args: vec![key],
                    },
                }
            }
            // A constructor reads as it is written: `Type(a)` for a tuple form, `Type { f: a }`
            // for named fields, and a bare path for a unit variant.
            FunctionRole::VariantConstructor { field_names, is_struct, .. } => {
                let name = self.friendly(f);
                // A single-variant struct is written `Type`, not `Type::Type`.
                let name = if *is_struct {
                    match name.rsplit_once("::") {
                        Some((ty, var)) if ty.rsplit("::").next() == Some(var) => ty.to_string(),
                        _ => name,
                    }
                } else {
                    name
                };
                if field_names.is_empty() {
                    LiftedExpr::var(name)
                } else if field_names.iter().all(|n| n.chars().all(|c| c.is_ascii_digit())) {
                    LiftedExpr::FunctionCall {
                        func: user_fn(&name),
                        args: vargs.iter().map(|a| self.lift(a)).collect(),
                    }
                } else {
                    let fields = field_names
                        .iter()
                        .zip(vargs.iter())
                        .map(|(n, a)| (n.clone(), self.lift(a)))
                        .collect();
                    LiftedExpr::StructLiteral { name, fields }
                }
            }
            FunctionRole::UserDefined { is_method: true, .. } if !vargs.is_empty() => {
                LiftedExpr::MethodCall {
                    receiver: Box::new(self.lift(&vargs[0])),
                    method: self.method_name(f),
                    args: vargs[1..].iter().map(|a| self.lift(a)).collect(),
                }
            }
            FunctionRole::UserDefined { is_method, .. } => self.lift_call(f, args, tac, *is_method),
            // Bookkeeping / iterator machinery: render faithfully with the role PRESERVED,
            // so a consumer can filter by role. air_lift never drops (that is the consumer's
            // collection-level choice); Opaque is reserved for genuinely unmodeled structure.
            FunctionRole::IteratorBoilerplate => self.lift_call_role(f, args, tac, role.clone()),
            _ if role.is_bookkeeping() => self.lift_call_role(f, args, tac, role.clone()),
            // Remaining roles degrade to a plain call.
            _ => self.lift_call(f, args, tac, false),
        }
    }

    fn lift_bind(&self, bind: &air::ast::Bind, body: &Expr, _expr: &Expr) -> LiftedExpr {
        match &**bind {
            BindX::Quant(quant, binders, triggers, _qid) => {
                let kind = match quant {
                    Quant::Forall => QuantKind::Forall,
                    Quant::Exists => QuantKind::Exists,
                };
                let bs = binders
                    .iter()
                    .map(|b| {
                        let typ = self.ctx.binder_types.get(&b.name)
                            .map(|t| vir_typ_to_source(t))
                            .or_else(|| Some(air_typ_to_source(&b.a)));
                        LiftedName {
                            source_name: strip_binder_suffix(&clean_air_name(b.name.as_str())),
                            version: None,
                            version_line: None,
                            decl_line: None,
                            kind: NameKind::QuantBinder,
                            typ,
                        }
                    })
                    .collect();
                LiftedExpr::Quantifier {
                    kind,
                    binders: bs,
                    body: Box::new(self.lift(body)),
                    triggers: self.lift_triggers(triggers),
                }
            }
            BindX::Let(binders) => {
                // Inline the let-bindings, then lift.
                let mut inlined = body.clone();
                for b in binders.iter() {
                    inlined = expr_utils::subst_expr(&b.name, &b.a, &inlined);
                }
                self.lift(&inlined)
            }
            BindX::Lambda(binders, triggers, _qid) => LiftedExpr::Closure {
                params: binders.iter().map(|b| clean_air_name(b.name.as_str())).collect(),
                body: Box::new(self.lift(body)),
                triggers: self.lift_triggers(triggers),
            },
            BindX::Choose(binders, triggers, _qid, _cond) => {
                let bs = binders
                    .iter()
                    .map(|b| LiftedName {
                        source_name: strip_binder_suffix(&clean_air_name(b.name.as_str())),
                        version: None,
                        version_line: None,
                        decl_line: None,
                        kind: NameKind::QuantBinder,
                        typ: self.ctx.binder_types.get(&b.name)
                            .map(|t| vir_typ_to_source(t))
                            .or_else(|| Some(air_typ_to_source(&b.a))),
                    })
                    .collect();
                LiftedExpr::Choose {
                    binders: bs,
                    body: Box::new(self.lift(body)),
                    triggers: self.lift_triggers(triggers),
                }
            }
        }
    }

    /// Lift each AIR trigger group into lifted trigger groups. Triggers are source-level
    /// instantiation hints; they are carried on the binder for faithfulness but are not
    /// otherwise interpreted here.
    fn lift_triggers(&self, triggers: &air::ast::Triggers) -> Vec<Vec<LiftedExpr>> {
        triggers
            .iter()
            .map(|group| group.iter().map(|e| self.lift(e)).collect())
            .collect()
    }

    fn lift_call(&self, f: &Ident, args: &Exprs, tac: usize, is_method: bool) -> LiftedExpr {
        self.lift_call_role(f, args, tac, FunctionRole::UserDefined { type_arg_count: tac, is_method })
    }

    /// Build a faithful `FunctionCall` preserving the given role (drops the leading
    /// `tac` type args). Used for user calls and for role-preserving bookkeeping.
    fn lift_call_role(&self, f: &Ident, args: &Exprs, tac: usize, role: FunctionRole) -> LiftedExpr {
        let lifted_args: Vec<LiftedExpr> = args.iter().skip(tac).map(|a| self.lift(a)).collect();
        let source_name = if matches!(role, FunctionRole::UserDefined { is_method: true, .. }) {
            self.method_name(f)
        } else {
            self.friendly(f)
        };
        LiftedExpr::FunctionCall {
            func: LiftedFunction { source_name, role, type_arg_count: tac },
            args: lifted_args,
        }
    }

    /// Whether `e` is a length call on `receiver` (so `subrange(s, n, s.len())` is a skip).
    fn is_len_of(&self, e: &Expr, receiver: &Expr) -> bool {
        let ExprX::Apply(f, args) = &**e else { return false };
        let name = self.ctx.friendly_names.get(f).map(|s| s.as_str()).unwrap_or(f.as_str());
        if !(name.ends_with("::len") || name.ends_with("::spec_vec_len")) {
            return false;
        }
        args.last()
            .map(|a| expr_utils::expr_key(a) == expr_utils::expr_key(receiver))
            .unwrap_or(false)
    }

    /// Strip a wrapper call whose name ends with `suffix`, which is machinery rather than
    /// something written in source.
    fn peel_named_call<'e>(&self, e: &'e Expr, suffix: &str) -> &'e Expr {
        if let ExprX::Apply(f, args) = &**e {
            let name = self.ctx.friendly_names.get(f).map(|s| s.as_str()).unwrap_or(f.as_str());
            if name.ends_with(suffix)
                && let Some(inner) = args.last()
            {
                return inner;
            }
        }
        e
    }

    /// The receiver of a call whose name ends with `suffix`, if `e` is such a call.
    fn named_call_receiver<'e>(&self, e: &'e Expr, suffix: &str) -> Option<&'e Expr> {
        let ExprX::Apply(f, args) = &**e else { return None };
        let name = self.ctx.friendly_names.get(f).map(|s| s.as_str()).unwrap_or(f.as_str());
        if name.ends_with(suffix) { args.last() } else { None }
    }

    fn friendly(&self, f: &Ident) -> String {
        let name =
            self.ctx.friendly_names.get(f).cloned().unwrap_or_else(|| clean_air_name(f.as_str()));
        strip_crate_prefix(&name, self.ctx.current_crate.as_deref())
    }

    /// The name a method call carries at the source level: the final path segment, since the
    /// receiver supplies the rest (`x.val()`, not `x.Trait::val()`).
    fn method_name(&self, f: &Ident) -> String {
        let name = self.friendly(f);
        name.rsplit("::").next().unwrap_or(&name).to_string()
    }

    /// Clean source field name for a field-accessor function.
    fn field_name(&self, f: &Ident) -> String {
        self.ctx
            .datatype_field_names
            .get(f)
            .cloned()
            .or_else(|| self.ctx.friendly_names.get(f).cloned())
            .unwrap_or_else(|| clean_air_name(f.as_str()))
    }
}

fn lift_const(c: &Constant) -> LiftedExpr {
    match c {
        Constant::Bool(b) => LiftedExpr::Literal(LitValue::Bool(*b)),
        Constant::Nat(s) => LiftedExpr::Literal(LitValue::Int(s.to_string())),
        // A bitvector literal reads in hex at the source level.
        Constant::BitVec(v, _width) => LiftedExpr::Literal(LitValue::Int(
            v.parse::<u128>().map(|n| format!("{:#x}", n)).unwrap_or_else(|_| v.to_string()),
        )),
        Constant::Real(s) => LiftedExpr::Literal(LitValue::Real(s.to_string())),
    }
}

fn map_binop(op: &BinaryOp) -> Option<BinOp> {
    Some(match op {
        BinaryOp::BitAnd => BinOp::BitAnd,
        BinaryOp::BitOr => BinOp::BitOr,
        BinaryOp::BitXor => BinOp::BitXor,
        BinaryOp::Shl => BinOp::Shl,
        BinaryOp::LShr | BinaryOp::AShr => BinOp::Shr,
        BinaryOp::BitAdd => BinOp::Add,
        BinaryOp::BitSub => BinOp::Sub,
        BinaryOp::BitMul => BinOp::Mul,
        BinaryOp::BitUDiv | BinaryOp::BitSDiv => BinOp::Div,
        BinaryOp::BitURem | BinaryOp::BitSRem => BinOp::Mod,
        BinaryOp::BitULt | BinaryOp::BitSLt => BinOp::Lt,
        BinaryOp::BitUGt | BinaryOp::BitSGt => BinOp::Gt,
        BinaryOp::BitULe | BinaryOp::BitSLe => BinOp::Le,
        BinaryOp::BitUGe | BinaryOp::BitSGe => BinOp::Ge,
        BinaryOp::Eq => BinOp::Eq,
        BinaryOp::Le => BinOp::Le,
        BinaryOp::Ge => BinOp::Ge,
        BinaryOp::Lt => BinOp::Lt,
        BinaryOp::Gt => BinOp::Gt,
        BinaryOp::Implies => BinOp::Implies,
        BinaryOp::EuclideanDiv => BinOp::Div,
        BinaryOp::EuclideanMod => BinOp::Mod,
        BinaryOp::RealDiv => BinOp::Div,
        // No canonical Verus/Rust operator for these. Enumerated with no wildcard so a new
        // BinaryOp variant breaks the build: Relation (Z3 special relations), BitConcat
        // (bitvector concatenation), FieldUpdate (handled in normalize; Opaque here is honest),
        // and the Float family (SMT FP-theory ops; source float ops lower to `ieee_float_*`
        // functions, so these have no source operator).
        BinaryOp::Relation(..)
        | BinaryOp::BitConcat
        | BinaryOp::FieldUpdate(..)
        | BinaryOp::FloatAdd(..)
        | BinaryOp::FloatSub(..)
        | BinaryOp::FloatMul(..)
        | BinaryOp::FloatDiv(..)
        | BinaryOp::FloatEq
        | BinaryOp::FloatLt
        | BinaryOp::FloatGt
        | BinaryOp::FloatLe
        | BinaryOp::FloatGe => return None,
    })
}

/// Remove the encoding's crate qualifier so a same-crate call reads as it does in source
/// (`double(x)`, not `test_crate::double(x)`).
fn strip_crate_prefix(name: &str, current_crate: Option<&str>) -> String {
    let name = name.strip_prefix("crate::").unwrap_or(name);
    match current_crate {
        Some(cc) => name.strip_prefix(&format!("{}::", cc)).unwrap_or(name).to_string(),
        None => name.to_string(),
    }
}

/// The operator a bit-operation function name denotes.
fn bit_binop(name: &str) -> Option<BinOp> {
    Some(match name {
        n if n == air_names::BIT_AND => BinOp::BitAnd,
        n if n == air_names::BIT_OR => BinOp::BitOr,
        n if n == air_names::BIT_XOR => BinOp::BitXor,
        _ => return None,
    })
}

/// A binder that was renamed to avoid a clash carries a numeric suffix; the source name is
/// what reads.
fn strip_binder_suffix(name: &str) -> String {
    match name.rsplit_once('$') {
        Some((base, digits)) if !digits.is_empty() && digits.chars().all(|c| c.is_ascii_digit()) => {
            base.to_string()
        }
        _ => name.to_string(),
    }
}

fn opaque(expr: &Expr) -> LiftedExpr {
    LiftedExpr::Opaque(expr_utils::expr_key(expr))
}

/// A plain (non-method) source-level function of the given name.
fn user_fn(name: &str) -> LiftedFunction {
    LiftedFunction {
        source_name: name.to_string(),
        role: FunctionRole::UserDefined { type_arg_count: 0, is_method: false },
        type_arg_count: 0,
    }
}

/// A lifted function that renders as `name` but keeps its classified `role`. Used where
/// the source-level name differs from the AIR name yet the role still carries meaning a
/// consumer needs (e.g. `call_ensures`/`call_requires` keep `ClosureEns`/`ClosureReq`, so
/// a consumer can recognise a closure-contract fact without matching on the display name).
fn role_fn(name: &str, role: FunctionRole) -> LiftedFunction {
    LiftedFunction { source_name: name.to_string(), role, type_arg_count: 0 }
}

/// Strip an `old(...)` wrapper from a lifted variable (the future value is
/// version-independent), leaving the current-value name.
fn strip_old(e: LiftedExpr) -> LiftedExpr {
    match e {
        LiftedExpr::Var(mut n) if matches!(n.kind, NameKind::Old) => {
            n.kind = NameKind::Current;
            LiftedExpr::Var(n)
        }
        other => other,
    }
}

/// True if `expr` is a typing guard `has_type(..)` / `sized(..)` — the antecedent
/// of a `guard ==> body` that lifting drops (it is solver bookkeeping, not source).
fn is_type_guard(expr: &Expr) -> bool {
    if let ExprX::Apply(f, _) = &**expr {
        let s = f.as_str().trim_start_matches(air_names::AIR_POLY_PREFIX);
        s == air_names::HAS_TYPE || s == air_names::SIZED_BOUND
    } else {
        false
    }
}

/// Recover a type from the AIR-level Typ (lossy fallback when VIR type is not available).
fn air_typ_to_source(typ: &air::ast::Typ) -> String {
    use air::ast::TypX;
    match &**typ {
        TypX::Bool => "bool".to_string(),
        TypX::Int => "int".to_string(),
        TypX::Real => "real".to_string(),
        _ => "int".to_string(), // sound conservative fallback
    }
}

/// Convert a VIR type to its Verus source spelling. Used for quantifier binder annotations.
/// Falls back to `"int"` when the type has been erased (a sound conservative bound, since all
/// Verus integer types are subranges of `int`).
pub fn vir_typ_to_source(typ: &vir::ast::Typ) -> String {
    use vir::ast::TypX;
    match &**typ {
        TypX::Bool => "bool".to_string(),
        TypX::Int(range) => {
            use vir::ast::IntRange;
            match range {
                IntRange::Int => "int".to_string(),
                IntRange::Nat => "nat".to_string(),
                IntRange::U(8) => "u8".to_string(),
                IntRange::U(16) => "u16".to_string(),
                IntRange::U(32) => "u32".to_string(),
                IntRange::U(64) => "u64".to_string(),
                IntRange::U(128) => "u128".to_string(),
                IntRange::I(8) => "i8".to_string(),
                IntRange::I(16) => "i16".to_string(),
                IntRange::I(32) => "i32".to_string(),
                IntRange::I(64) => "i64".to_string(),
                IntRange::I(128) => "i128".to_string(),
                IntRange::USize => "usize".to_string(),
                IntRange::ISize => "isize".to_string(),
                IntRange::Char => "char".to_string(),
                _ => "int".to_string(),
            }
        }
        TypX::Real => "real".to_string(),
        TypX::Datatype(dt, _, _) => {
            vir::ast_util::path_as_friendly_rust_name(
                &match dt {
                    vir::ast::Dt::Path(p) => p.clone(),
                    vir::ast::Dt::Tuple(n) => {
                        return format!("tuple{}", n);
                    }
                },
            )
        }
        TypX::SpecFn(_, _) => "spec_fn".to_string(),
        _ => "int".to_string(), // sound conservative fallback
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lifted::{BinOp, LiftedExpr, LitValue};
    use air::ast::{BinaryOp, Constant, ExprX};
    use std::sync::Arc;

    fn ctx() -> PipelineContext {
        PipelineContext::default()
    }

    #[test]
    fn lifts_bool_constant() {
        let e: Expr = Arc::new(ExprX::Const(Constant::Bool(true)));
        assert_eq!(lift_expr(&e, &ctx()), LiftedExpr::Literal(LitValue::Bool(true)));
    }

    #[test]
    fn distinct_lifts_to_pairwise_inequality() {
        // distinct(a, b, c) reads as `a != b && a != c && b != c`.
        let e: Expr = Arc::new(ExprX::Multi(
            air::ast::MultiOp::Distinct,
            Arc::new(vec![var("a"), var("b"), var("c")]),
        ));
        let s = crate::render::render(&lift_expr(&e, &ctx()));
        assert!(s.contains("a != b"), "got: {}", s);
        assert!(s.contains("a != c"), "got: {}", s);
        assert!(s.contains("b != c"), "got: {}", s);
    }

    #[test]
    fn labeled_assertion_unwraps_to_inner() {
        // A labeled assertion carries a diagnostic message + filter (machinery); lifting peels
        // the label and returns the inner expression, not Opaque.
        let msg: air::messages::ArcDynMessage =
            Arc::new(()) as Arc<dyn std::any::Any + Send + Sync>;
        let inner = Arc::new(ExprX::Binary(BinaryOp::Lt, var("x"), var("y")));
        let e: Expr = Arc::new(ExprX::LabeledAssertion(None, msg, None, inner));
        assert!(
            matches!(lift_expr(&e, &ctx()), LiftedExpr::BinaryOp { op: BinOp::Lt, .. }),
            "labeled assertion did not unwrap to its inner expr"
        );
    }

    #[test]
    fn temporary_var_lifts_with_temporary_kind() {
        // A var classified VarInfo::Temporary lifts to NameKind::Temporary (carried, not
        // degraded to Current) and still renders by its cleaned name (`tmp%3` -> `tmp3`).
        use crate::lifted::NameKind;
        let mut c = PipelineContext::default();
        c.variable_info.insert(Arc::new("tmp%3".to_string()), VarInfo::Temporary);
        let e: Expr = Arc::new(ExprX::Var(Arc::new("tmp%3".to_string())));
        match lift_expr(&e, &c) {
            LiftedExpr::Var(n) => {
                assert_eq!(n.kind, NameKind::Temporary);
                assert_eq!(n.source_name, "tmp3");
            }
            other => panic!("expected Var, got {:?}", other),
        }
        assert_eq!(crate::render::render(&lift_expr(&e, &c)), "tmp3");
    }

    #[test]
    fn quantifier_captures_triggers_without_rendering_them() {
        // forall|i: int| #[trigger] (i < n) :: (i < n)
        // The trigger group is lifted and carried on the binder, but the rendered
        // string is exactly the untriggered form.
        use air::ast_util::{ident_binder, int_typ, mk_forall};
        let body = Arc::new(ExprX::Binary(BinaryOp::Lt, var("i"), var("n")));
        let binders = vec![ident_binder(&Arc::new("i".to_string()), &int_typ())];
        let triggers = vec![Arc::new(vec![body.clone()])]; // one group, one term: (i < n)
        let q = mk_forall(&binders, &triggers, None, &body);
        match lift_expr(&q, &ctx()) {
            LiftedExpr::Quantifier { triggers, body, .. } => {
                assert_eq!(triggers.len(), 1, "one trigger group expected");
                assert_eq!(triggers[0].len(), 1, "one trigger term expected");
                // The captured trigger is the lifted `i < n`.
                assert!(
                    matches!(&triggers[0][0], LiftedExpr::BinaryOp { op: BinOp::Lt, .. }),
                    "trigger term should be the lifted `i < n`, got {:?}",
                    triggers[0][0]
                );
                assert!(matches!(&*body, LiftedExpr::BinaryOp { op: BinOp::Lt, .. }));
            }
            other => panic!("expected Quantifier, got {:?}", other),
        }
        // Rendering ignores triggers: the output is the plain quantifier.
        assert_eq!(crate::render::render(&lift_expr(&q, &ctx())), "forall|i: int| i < n");
    }

    #[test]
    fn lifts_comparison_to_binaryop() {
        // x < 100  (Var and Const under an AIR Binary::Lt)
        let x: Expr = Arc::new(ExprX::Var(Arc::new("x".to_string())));
        let hundred: Expr = Arc::new(ExprX::Const(Constant::Nat(Arc::new("100".to_string()))));
        let lt: Expr = Arc::new(ExprX::Binary(BinaryOp::Lt, x, hundred));
        match lift_expr(&lt, &ctx()) {
            LiftedExpr::BinaryOp { op: BinOp::Lt, rhs, .. } => {
                assert_eq!(*rhs, LiftedExpr::Literal(LitValue::Int("100".to_string())));
            }
            other => panic!("expected BinaryOp Lt, got {:?}", other),
        }
    }

    #[test]
    fn lifts_real_constant() {
        let r: Expr = Arc::new(ExprX::Const(Constant::Real(Arc::new("1.5".to_string()))));
        assert_eq!(lift_expr(&r, &ctx()), LiftedExpr::Literal(LitValue::Real("1.5".to_string())));
    }

    use crate::types::FunctionRole;
    fn var(n: &str) -> Expr {
        Arc::new(ExprX::Var(Arc::new(n.to_string())))
    }
    fn apply(name: &str, args: Vec<Expr>) -> Expr {
        Arc::new(ExprX::Apply(Arc::new(name.to_string()), Arc::new(args)))
    }
    fn ctx_role(name: &str, role: FunctionRole) -> PipelineContext {
        let mut c = PipelineContext::default();
        c.function_roles.insert(Arc::new(name.to_string()), role);
        c
    }

    #[test]
    fn bookkeeping_role_lifts_faithfully_not_opaque() {
        // A bookkeeping call lifts to a role-PRESERVING FunctionCall (never Opaque),
        // so a consumer can filter by role.
        let c = ctx_role("fuel_bool", FunctionRole::Fuel);
        match lift_expr(&apply("fuel_bool", vec![var("g")]), &c) {
            LiftedExpr::FunctionCall { func, .. } => assert_eq!(func.role, FunctionRole::Fuel),
            other => panic!("expected role-preserving FunctionCall, got {:?}", other),
        }
    }

    #[test]
    fn closure_ens_lifts_with_role_preserved() {
        // call_ensures renders by its source name but keeps the ClosureEns role, so a
        // consumer can recognise a closure-contract fact structurally (not by name).
        let c = ctx_role("closure_ens", FunctionRole::ClosureEns);
        // closure_ens(ta0, ta1, ta2, id, args, ret): 3 leading type args are stripped.
        let e = apply(
            "closure_ens",
            vec![var("t0"), var("t1"), var("t2"), var("id"), var("args"), var("ret")],
        );
        match lift_expr(&e, &c) {
            LiftedExpr::FunctionCall { func, args } => {
                assert_eq!(func.source_name, "call_ensures");
                assert_eq!(func.role, FunctionRole::ClosureEns);
                assert_eq!(args.len(), 3);
            }
            other => panic!("expected FunctionCall, got {:?}", other),
        }
        // ClosureEns is not bookkeeping, so it survives noise filtering and renders.
        assert!(!FunctionRole::ClosureEns.is_bookkeeping());
    }

    #[test]
    fn promoted_array_index_lifts_to_index() {
        // Formerly Noise (rendered `true`); now a real IndexOp -> Index.
        let c = ctx_role("array_index", FunctionRole::IndexOp { type_arg_count: 0 });
        let e = apply("array_index", vec![var("a"), Arc::new(ExprX::Const(Constant::Nat(Arc::new("0".to_string()))))]);
        assert!(matches!(lift_expr(&e, &c), LiftedExpr::Index { .. }), "array_index -> Index");
        assert_eq!(crate::render::render(&lift_expr(&e, &c)), "a[0]");
    }

    #[test]
    fn promoted_strslice_len_lifts_and_renders_len() {
        // Formerly Noise; now a real LenMethod -> renders `.len()`.
        let c = ctx_role("strslice_len", FunctionRole::LenMethod { type_arg_count: 0 });
        assert_eq!(crate::render::render(&lift_expr(&apply("strslice_len", vec![var("s")]), &c)), "s.len()");
    }

    #[test]
    fn type_guard_stripped_in_guard_position() {
        // (has_type x) ==> P  lifts to just P (source-recovery).
        let guard = apply(air_names::HAS_TYPE, vec![var("x")]);
        let imp: Expr = Arc::new(ExprX::Binary(BinaryOp::Implies, guard, var("p")));
        assert_eq!(crate::render::render(&lift_expr(&imp, &ctx())), "p");
    }
}
