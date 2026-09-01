//! `render` — pretty-print a [`LiftedExpr`] to a compact Verus-like source string.
//!
//! Parenthesizes by precedence and uses Verus operator spellings (`==>`, `=~=`, …), so
//! rendered expressions read like source.
//!
//! This is a **display** rendering: the output reads like source but is not guaranteed
//! to be legal, parseable Verus — a [`LiftedExpr::Opaque`] node emits its raw fallback
//! text verbatim. To obtain a legal, injectable expression instead, lower to
//! `verus_syn::Expr` via [`crate::syn_bridge`].
//!
//! Names are rendered as they appear in source. A [`LiftedName`] records a version and the line
//! it was produced at, but that notation (`x@21`) is not Verus, so neither renderer here emits
//! it. Distinct versions of a variable therefore render alike; a caller that must tell them
//! apart supplies its own formatter through [`render_with`].

use crate::lifted::{
    BinOp, LiftedExpr, LiftedFunction, LiftedName, LitValue, NameKind, QuantKind, UnOp,
};
use crate::types::FunctionRole;

/// Binding-power levels (higher binds tighter).
mod prec {
    pub const LOWEST: u8 = 0;
    pub const IMPLY: u8 = 1;
    pub const OR: u8 = 2;
    pub const AND: u8 = 3;
    pub const CMP: u8 = 4;
    pub const BIT_OR: u8 = 5;
    pub const BIT_XOR: u8 = 6;
    pub const BIT_AND: u8 = 7;
    pub const SHIFT: u8 = 8;
    pub const ADD: u8 = 9;
    pub const MUL: u8 = 10;
    pub const CAST: u8 = 11;
    pub const UNARY: u8 = 12;
    pub const POSTFIX: u8 = 13;
}

/// Render a lifted expression to a source-level string, displaying each variable
/// occurrence by its source name (and `old(x)` for a pre-state value).
pub fn render(expr: &LiftedExpr) -> String {
    render_with(expr, &default_name)
}

/// Render a lifted expression, choosing how each variable occurrence is displayed.
///
/// A [`LiftedName`] carries more than a name — a version, the line the version was produced
/// at, the line the variable was declared at, and how the occurrence relates to the user's
/// variable. Which of that to show is the caller's decision: plain `x`, a versioned `x@21`,
/// or anything else. [`render`] shows the source name.
pub fn render_with(expr: &LiftedExpr, name_fmt: &dyn Fn(&LiftedName) -> String) -> String {
    let mut out = String::new();
    render_prec(&mut out, expr, prec::LOWEST, name_fmt);
    out
}

/// The default display for a variable occurrence: its source name, wrapped in `old(...)` for
/// a pre-state value.
pub fn default_name(name: &LiftedName) -> String {
    match name.kind {
        NameKind::Old => format!("old({})", name.source_name),
        _ => name.source_name.clone(),
    }
}

fn render_prec(out: &mut String, expr: &LiftedExpr, ctx: u8, name_fmt: &dyn Fn(&LiftedName) -> String) {
    match expr {
        LiftedExpr::Var(name) => out.push_str(&name_fmt(name)),
        LiftedExpr::Literal(LitValue::Bool(b)) => out.push_str(if *b { "true" } else { "false" }),
        LiftedExpr::Literal(LitValue::Int(s)) => out.push_str(s),
        LiftedExpr::Literal(LitValue::Real(s)) => out.push_str(s),
        LiftedExpr::BinaryOp { op, lhs, rhs } => {
            // Chained ascending comparison: `(a <= m) && (m <= c)` with a shared
            // middle term renders as the fluent `a <= m <= c`.
            if matches!(op, BinOp::And)
                && let (Some((la, lop, lm)), Some((rm, rop, rc))) =
                    (ascending_cmp(lhs), ascending_cmp(rhs))
                && lm == rm
            {
                let needs = ctx > prec::CMP;
                if needs {
                    out.push('(');
                }
                render_prec(out, la, prec::CMP, name_fmt);
                out.push(' ');
                out.push_str(lop);
                out.push(' ');
                render_prec(out, lm, prec::CMP, name_fmt);
                out.push(' ');
                out.push_str(rop);
                out.push(' ');
                render_prec(out, rc, prec::CMP, name_fmt);
                if needs {
                    out.push(')');
                }
                return;
            }
            let (s, op_prec, right_prec) = binop_info(*op);
            let needs = ctx > op_prec;
            if needs {
                out.push('(');
            }
            render_prec(out, lhs, op_prec, name_fmt);
            out.push(' ');
            out.push_str(s);
            out.push(' ');
            render_prec(out, rhs, right_prec, name_fmt);
            if needs {
                out.push(')');
            }
        }
        LiftedExpr::UnaryOp { op, operand } => {
            let s = match op {
                UnOp::Not => "!",
                UnOp::Neg => "-",
                UnOp::BitNot => "!",
                UnOp::Deref => "*",
            };
            let needs = ctx > prec::UNARY;
            if needs {
                out.push('(');
            }
            out.push_str(s);
            render_prec(out, operand, prec::UNARY, name_fmt);
            if needs {
                out.push(')');
            }
        }
        LiftedExpr::FieldAccess { receiver, field } => {
            // Field access dereferences on its own, so `(*x).f` reads as `x.f`.
            let base = match &**receiver {
                // `final` is only meaningful as `*final(e)`, so that dereference stays.
                LiftedExpr::UnaryOp { op: UnOp::Deref, operand } if !is_final_call(operand) => {
                    operand
                }
                other => other,
            };
            render_prec(out, base, prec::POSTFIX, name_fmt);
            out.push('.');
            out.push_str(field);
        }
        LiftedExpr::Index { receiver, index } => {
            render_prec(out, receiver, prec::POSTFIX, name_fmt);
            out.push('[');
            render_prec(out, index, prec::LOWEST, name_fmt);
            out.push(']');
        }
        LiftedExpr::FunctionCall { func, args } => render_call(out, func, args, name_fmt),
        LiftedExpr::Quantifier { kind, binders, body, .. } => {
            out.push_str(match kind {
                QuantKind::Forall => "forall",
                QuantKind::Exists => "exists",
            });
            out.push('|');
            for (i, b) in binders.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                out.push_str(&name_fmt(b));
                if let Some(ref t) = b.typ {
                    out.push_str(": ");
                    out.push_str(t);
                }
            }
            out.push_str("| ");
            if matches!(&**body, LiftedExpr::Quantifier { .. }) {
                out.push('(');
                render_prec(out, body, prec::LOWEST, name_fmt);
                out.push(')');
            } else {
                render_prec(out, body, prec::LOWEST, name_fmt);
            }
        }
        LiftedExpr::IfThenElse { cond, then_, else_ } => {
            out.push_str("if ");
            render_prec(out, cond, prec::LOWEST, name_fmt);
            out.push_str(" { ");
            render_prec(out, then_, prec::LOWEST, name_fmt);
            out.push_str(" } else { ");
            render_prec(out, else_, prec::LOWEST, name_fmt);
            out.push_str(" }");
        }
        LiftedExpr::Tuple(elems) => {
            out.push('(');
            render_arg_list(out, elems, name_fmt);
            if elems.len() == 1 {
                out.push(',');
            }
            out.push(')');
        }
        LiftedExpr::TupleField { receiver, index } => {
            render_prec(out, receiver, prec::POSTFIX, name_fmt);
            out.push('.');
            out.push_str(&index.to_string());
        }
        LiftedExpr::Cast { value, ty } => {
            let needs = ctx > prec::CAST;
            if needs {
                out.push('(');
            }
            render_prec(out, value, prec::CAST, name_fmt);
            out.push_str(" as ");
            out.push_str(ty);
            if needs {
                out.push(')');
            }
        }
        LiftedExpr::Closure { params, body, .. } => {
            out.push('|');
            out.push_str(&params.join(", "));
            out.push_str("| ");
            render_prec(out, body, prec::LOWEST, name_fmt);
        }
        LiftedExpr::StructLiteral { name, fields } => {
            out.push_str(name);
            out.push_str(" { ");
            for (i, (field, value)) in fields.iter().enumerate() {
                if i > 0 {
                    out.push_str(", ");
                }
                out.push_str(field);
                out.push_str(": ");
                render_prec(out, value, prec::LOWEST, name_fmt);
            }
            out.push_str(" }");
        }
        LiftedExpr::MethodCall { receiver, method, args } => {
            // A method call dereferences its receiver, so `(*x).m()` reads as `x.m()`.
            let base = match &**receiver {
                LiftedExpr::UnaryOp { op: UnOp::Deref, operand } if !is_final_call(operand) => {
                    operand
                }
                other => other,
            };
            render_prec(out, base, prec::POSTFIX, name_fmt);
            out.push('.');
            out.push_str(method);
            out.push('(');
            render_arg_list(out, args, name_fmt);
            out.push(')');
        }
        LiftedExpr::Apply { callee, args } => {
            render_prec(out, callee, prec::POSTFIX, name_fmt);
            out.push('(');
            render_arg_list(out, args, name_fmt);
            out.push(')');
        }
        LiftedExpr::Choose { binders, body, .. } => {
            out.push_str("choose|");
            for (i, b) in binders.iter().enumerate() {
                if i > 0 {                    out.push_str(", ");
                }
                out.push_str(&name_fmt(b));
                if let Some(ref t) = b.typ {
                    out.push_str(": ");
                    out.push_str(t);
                }
            }
            out.push_str("| ");
            render_prec(out, body, prec::LOWEST, name_fmt);
        }
        LiftedExpr::ArrayLiteral(elems) => {
            out.push('[');
            render_arg_list(out, elems, name_fmt);
            out.push(']');
        }
        LiftedExpr::Opaque(s) => out.push_str(s),
    }
}

/// Whether an expression is a call to `final`, whose only valid form is `*final(e)`.
fn is_final_call(e: &LiftedExpr) -> bool {
    matches!(e, LiftedExpr::FunctionCall { func, .. } if func.source_name == "final")
}

fn render_call(out: &mut String, func: &LiftedFunction, args: &[LiftedExpr], name_fmt: &dyn Fn(&LiftedName) -> String) {
    match &func.role {
        // `recv.len()`
        FunctionRole::LenMethod { .. } if args.len() == 1 => {
            render_prec(out, &args[0], prec::POSTFIX, name_fmt);
            out.push_str(".len()");
        }
        // Variant test: Option/Result -> `recv.is_some()` etc.; else `matches!(recv, T::V)`.
        FunctionRole::VariantDiscriminant { type_name, variant_name } if args.len() == 1 => {
            let method = match (type_name.as_str(), variant_name.as_str()) {
                ("Option", "Some") => Some("is_some"),
                ("Option", "None") => Some("is_none"),
                ("Result", "Ok") => Some("is_ok"),
                ("Result", "Err") => Some("is_err"),
                _ => None,
            };
            match method {
                Some(m) => {
                    render_prec(out, &args[0], prec::POSTFIX, name_fmt);
                    out.push('.');
                    out.push_str(m);
                    out.push_str("()");
                }
                None => {
                    out.push_str("matches!(");
                    render_prec(out, &args[0], prec::LOWEST, name_fmt);
                    out.push_str(", ");
                    out.push_str(type_name);
                    out.push_str("::");
                    out.push_str(variant_name);
                    out.push(')');
                }
            }
        }
        // `recv.method(rest..)`
        FunctionRole::UserDefined { is_method: true, .. } if !args.is_empty() => {
            render_prec(out, &args[0], prec::POSTFIX, name_fmt);
            out.push('.');
            out.push_str(&func.source_name);
            out.push('(');
            render_arg_list(out, &args[1..], name_fmt);
            out.push(')');
        }
        // `name(args..)`
        _ => {
            out.push_str(&func.source_name);
            out.push('(');
            render_arg_list(out, args, name_fmt);
            out.push(')');
        }
    }
}

fn render_arg_list(out: &mut String, args: &[LiftedExpr], name_fmt: &dyn Fn(&LiftedName) -> String) {
    for (i, a) in args.iter().enumerate() {
        if i > 0 {
            out.push_str(", ");
        }
        render_prec(out, a, prec::LOWEST, name_fmt);
    }
}

fn binop_info(op: BinOp) -> (&'static str, u8, u8) {
    use prec::*;
    match op {
        BinOp::Or => ("||", OR, OR + 1),
        BinOp::And => ("&&", AND, AND + 1),
        BinOp::Eq => ("==", CMP, CMP),
        BinOp::Ne => ("!=", CMP, CMP),
        BinOp::Lt => ("<", CMP, CMP),
        BinOp::Le => ("<=", CMP, CMP),
        BinOp::Gt => (">", CMP, CMP),
        BinOp::Ge => (">=", CMP, CMP),
        BinOp::Add => ("+", ADD, ADD + 1),
        BinOp::Sub => ("-", ADD, ADD + 1),
        BinOp::Mul => ("*", MUL, MUL + 1),
        BinOp::Div => ("/", MUL, MUL + 1),
        BinOp::Mod => ("%", MUL, MUL + 1),
        BinOp::Implies => ("==>", IMPLY, IMPLY),
        BinOp::ExtEq => ("=~=", CMP, CMP),
        BinOp::BitOr => ("|", BIT_OR, BIT_OR + 1),
        BinOp::BitXor => ("^", BIT_XOR, BIT_XOR + 1),
        BinOp::BitAnd => ("&", BIT_AND, BIT_AND + 1),
        BinOp::Shl => ("<<", SHIFT, SHIFT + 1),
        BinOp::Shr => (">>", SHIFT, SHIFT + 1),
    }
}

/// If `e` is an ascending comparison (`<` / `<=`), return `(left, op_str, right)`.
fn ascending_cmp(e: &LiftedExpr) -> Option<(&LiftedExpr, &'static str, &LiftedExpr)> {
    if let LiftedExpr::BinaryOp { op, lhs, rhs } = e {
        let s = match op {
            BinOp::Lt => "<",
            BinOp::Le => "<=",
            _ => return None,
        };
        Some((&**lhs, s, &**rhs))
    } else {
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lifted::{LiftedFunction, LiftedName, VersionReason};

    fn int(n: &str) -> LiftedExpr {
        LiftedExpr::Literal(LitValue::Int(n.to_string()))
    }
    fn old(name: &str) -> LiftedExpr {
        LiftedExpr::Var(LiftedName {
            source_name: name.to_string(),
            version: None,
            version_line: None,
            decl_line: None,
            kind: NameKind::Old,
            typ: None,
        })
    }
    fn bin(op: BinOp, l: LiftedExpr, r: LiftedExpr) -> LiftedExpr {
        LiftedExpr::BinaryOp { op, lhs: Box::new(l), rhs: Box::new(r) }
    }

    #[test]
    fn comparison() {
        assert_eq!(render(&bin(BinOp::Gt, LiftedExpr::var("x"), int("100"))), "x > 100");
    }

    #[test]
    fn old_form() {
        // *x == *old(x)  — idiomatic Verus for a &mut: deref current, deref old-ref.
        let deref = |n: &str| LiftedExpr::UnaryOp {
            op: UnOp::Deref,
            operand: Box::new(LiftedExpr::var(n)),
        };
        let rhs = LiftedExpr::UnaryOp { op: UnOp::Deref, operand: Box::new(old("x")) };
        assert_eq!(render(&bin(BinOp::Eq, deref("x"), rhs)), "*x == *old(x)");
    }

    #[test]
    fn precedence_parenthesizes() {
        // (a + b) * c  — Add is looser than Mul, so the left child needs parens.
        let sum = bin(BinOp::Add, LiftedExpr::var("a"), LiftedExpr::var("b"));
        assert_eq!(render(&bin(BinOp::Mul, sum, LiftedExpr::var("c"))), "(a + b) * c");
        // a + b * c — Mul binds tighter, no parens.
        let prod = bin(BinOp::Mul, LiftedExpr::var("b"), LiftedExpr::var("c"));
        assert_eq!(render(&bin(BinOp::Add, LiftedExpr::var("a"), prod)), "a + b * c");
    }

    #[test]
    fn len_method_and_field_and_index() {
        let v = LiftedExpr::var("v");
        let len = LiftedExpr::FunctionCall {
            func: LiftedFunction {
                source_name: "len".to_string(),
                role: FunctionRole::LenMethod { type_arg_count: 0 },
                type_arg_count: 0,
            },
            args: vec![v],
        };
        assert_eq!(render(&bin(BinOp::Eq, len, int("5"))), "v.len() == 5");

        let field = LiftedExpr::FieldAccess {
            receiver: Box::new(LiftedExpr::var("s")),
            field: "x".to_string(),
        };
        assert_eq!(render(&field), "s.x");

        let index = LiftedExpr::Index {
            receiver: Box::new(LiftedExpr::var("a")),
            index: Box::new(int("0")),
        };
        assert_eq!(render(&index), "a[0]");
    }

    #[test]
    fn quantifier() {
        let body = bin(BinOp::Lt, LiftedExpr::var("i"), LiftedExpr::var("n"));
        let q = LiftedExpr::Quantifier {
            kind: QuantKind::Forall,
            binders: vec![LiftedName {
                source_name: "i".to_string(),
                version: None,
                version_line: None,
                decl_line: None,
                kind: NameKind::QuantBinder,
                typ: None,
            }],
            body: Box::new(body),
            triggers: Vec::new(),
        };
        assert_eq!(render(&q), "forall|i| i < n");
    }

    #[test]
    fn implies_and_ext_eq() {
        let ee = bin(BinOp::ExtEq, LiftedExpr::var("s1"), LiftedExpr::var("s2"));
        assert_eq!(render(&ee), "s1 =~= s2");
        let imp = bin(BinOp::Implies, LiftedExpr::var("p"), LiftedExpr::var("q"));
        assert_eq!(render(&imp), "p ==> q");
    }

    #[test]
    fn opaque_passthrough() {
        assert_eq!(render(&LiftedExpr::Opaque("<blob>".to_string())), "<blob>");
        // silence unused-import warning for VersionReason in this test module
        let _ = VersionReason::Loop;
    }
    #[test]
    fn chained_comparison_fusion() {
        // (0 <= x) && (x <= 10) -> "0 <= x <= 10"
        let l = bin(BinOp::Le, int("0"), LiftedExpr::var("x"));
        let r = bin(BinOp::Le, LiftedExpr::var("x"), int("10"));
        assert_eq!(render(&bin(BinOp::And, l, r)), "0 <= x <= 10");
        // distinct middle terms stay the `&&` form
        let l2 = bin(BinOp::Le, int("0"), LiftedExpr::var("x"));
        let r2 = bin(BinOp::Le, LiftedExpr::var("y"), int("10"));
        assert_eq!(render(&bin(BinOp::And, l2, r2)), "0 <= x && y <= 10");
    }
    #[test]
    fn provided_rendering_uses_source_level_names() {
        // The renderers in this crate produce names as they appear in source. A version, and the
        // line it was produced at, are recorded on the name for a caller that wants to show them
        // (a diagnostic might print `x@21`), but that notation is not Verus and so is never
        // emitted here. The consequence is that distinct versions of a variable render alike;
        // a caller that must tell them apart supplies its own formatter.
        let versioned = LiftedExpr::Var(LiftedName {
            source_name: "x".to_string(),
            version: Some(3),
            version_line: Some(21),
            decl_line: Some(7),
            kind: NameKind::Intermediate { reason: VersionReason::Merge },
            typ: None,
        });
        assert_eq!(render(&versioned), "x");
        let cmp = bin(BinOp::Lt, versioned, int("100"));
        let out = render(&cmp);
        assert_eq!(out, "x < 100");
        assert!(!out.contains('@'), "version notation is not source-level: {}", out);
    }

    #[test]
    fn name_display_is_the_callers_choice() {
        // The default shows the source name; a caller can show the version instead.
        let versioned = LiftedExpr::Var(LiftedName {
            source_name: "x".to_string(),
            version: Some(3),
            version_line: Some(21),
            decl_line: None,
            kind: NameKind::Intermediate { reason: VersionReason::Merge },
            typ: None,
        });
        assert_eq!(render(&versioned), "x");
        let with_line = |n: &LiftedName| match n.version_line {
            Some(l) => format!("{}@{}", n.source_name, l),
            None => n.source_name.clone(),
        };
        assert_eq!(render_with(&versioned, &with_line), "x@21");
        // The choice applies inside nested structure too.
        let cmp = bin(BinOp::Lt, versioned, int("100"));
        assert_eq!(render_with(&cmp, &with_line), "x@21 < 100");
    }
}
