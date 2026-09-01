//! `syn_bridge` — lower a [`LiftedExpr`] to a legal `verus_syn::Expr`.
//!
//! The standard-AST output path: a consumer that needs standard Verus/Rust — for
//! example to inject a generated expression into a program — takes the
//! `verus_syn::Expr` directly. Precedence parentheses (`Expr::Paren`) are inserted
//! during construction, so the resulting AST tokenizes to correctly-parenthesized
//! Verus.
//!
//! For a compact, human-readable display string rather than an injectable AST, see
//! [`crate::render`].

use proc_macro2::Span;
use verus_syn::punctuated::Punctuated;
use verus_syn::token;
use verus_syn::{
    BinOp as SynBinOp, Expr, ExprBinary, ExprCall, ExprField, ExprIndex, ExprLit, ExprMethodCall,
    ExprParen, ExprPath, ExprUnary, Ident as SynIdent, Lit, LitBool, LitInt, Member, Path,
    PathArguments, PathSegment, UnOp as SynUnOp,
};

use crate::lifted::{
    BinOp, LiftedExpr, LiftedFunction, LiftedName, LitValue, NameKind, QuantKind, UnOp,
};
use crate::types::FunctionRole;

/// Binding-power levels (higher binds tighter). Mirror the renderer's scheme.
mod prec {
    pub const LOWEST: u8 = 0;
    pub const IMPLY: u8 = 1;
    pub const OR: u8 = 2;
    pub const AND: u8 = 3;
    pub const CMP: u8 = 4;
    pub const ADD: u8 = 5;
    pub const MUL: u8 = 6;
    pub const UNARY: u8 = 7;
    pub const POSTFIX: u8 = 8;
}

/// Lower a [`LiftedExpr`] into a legal `verus_syn::Expr`.
pub fn to_syn(expr: &LiftedExpr) -> Expr {
    to_syn_prec(expr, prec::LOWEST)
}

/// Lower to the injectable AST and render its tokens as a string (for probes/tests).
pub fn to_syn_string(expr: &LiftedExpr) -> String {
    use quote::ToTokens;
    to_syn(expr).to_token_stream().to_string()
}

/// True iff the injectable AST re-parses as a legal Verus expression (the `to_syn` contract).
pub fn to_syn_reparses(expr: &LiftedExpr) -> bool {
    use quote::ToTokens;
    verus_syn::parse2::<Expr>(to_syn(expr).to_token_stream()).is_ok()
}

fn to_syn_prec(expr: &LiftedExpr, ctx: u8) -> Expr {
    match expr {
        LiftedExpr::Var(name) => lower_name(name),
        LiftedExpr::Literal(LitValue::Bool(b)) => Expr::Lit(ExprLit {
            attrs: vec![],
            lit: Lit::Bool(LitBool { value: *b, span: Span::call_site() }),
        }),
        LiftedExpr::Literal(LitValue::Int(s)) => match verus_syn::parse_str::<LitInt>(s) {
            Ok(lit) => Expr::Lit(ExprLit { attrs: vec![], lit: Lit::Int(lit) }),
            // A non-canonical integer string would panic `LitInt::new`; degrade to verbatim
            // so `to_syn` stays total (mirrors the `Real` arm).
            Err(_) => verbatim(s),
        },
        LiftedExpr::Literal(LitValue::Real(s)) => verbatim(s),
        LiftedExpr::BinaryOp { op, lhs, rhs } => {
            let (vop, op_prec, right_prec) = binop_info(*op);
            let e = Expr::Binary(ExprBinary {
                attrs: vec![],
                left: Box::new(to_syn_prec(lhs, op_prec)),
                op: vop,
                right: Box::new(to_syn_prec(rhs, right_prec)),
            });
            maybe_paren(e, ctx > op_prec)
        }
        LiftedExpr::UnaryOp { op, operand } => {
            let e = Expr::Unary(ExprUnary {
                attrs: vec![],
                op: unop(*op),
                expr: Box::new(to_syn_prec(operand, prec::UNARY)),
            });
            maybe_paren(e, ctx > prec::UNARY)
        }
        LiftedExpr::FieldAccess { receiver, field } => Expr::Field(ExprField {
            attrs: vec![],
            base: Box::new(to_syn_prec(receiver, prec::POSTFIX)),
            dot_token: token::Dot::default(),
            member: Member::Named(safe_ident(field)),
        }),
        LiftedExpr::Index { receiver, index } => Expr::Index(ExprIndex {
            attrs: vec![],
            expr: Box::new(to_syn_prec(receiver, prec::POSTFIX)),
            bracket_token: token::Bracket::default(),
            index: Box::new(to_syn_prec(index, prec::LOWEST)),
        }),
        LiftedExpr::FunctionCall { func, args } => lower_call(func, args),
        LiftedExpr::Apply { callee, args } => func_call(
            to_syn_prec(callee, prec::POSTFIX),
            args.iter().map(|a| to_syn_prec(a, prec::LOWEST)).collect(),
        ),
        // Compound forms are built as real structured verus_syn nodes: sub-expressions are
        // lowered with `to_syn` (so an Opaque leaf becomes a local `_`, never collapsing the
        // whole form), assembled with typed binders, and parsed back into a structural `Expr`.
        LiftedExpr::Quantifier { kind, binders, body, .. } => {
            let k = match kind {
                QuantKind::Forall => "forall",
                QuantKind::Exists => "exists",
            };
            let bs = binders.iter().map(fmt_binder).collect::<Vec<_>>().join(", ");
            structural(&format!("{}|{}| {}", k, bs, src(body)))
        }
        LiftedExpr::IfThenElse { cond, then_, else_ } => structural(&format!(
            "if {} {{ {} }} else {{ {} }}",
            src(cond),
            src(then_),
            src(else_)
        )),
        LiftedExpr::Tuple(elems) => {
            let mut punct = Punctuated::new();
            for e in elems {
                punct.push(to_syn_prec(e, prec::LOWEST));
            }
            if elems.len() == 1 {
                punct.push_punct(token::Comma::default());
            }
            Expr::Tuple(verus_syn::ExprTuple {
                attrs: vec![],
                paren_token: token::Paren::default(),
                elems: punct,
            })
        }
        LiftedExpr::TupleField { receiver, index } => Expr::Field(ExprField {
            attrs: vec![],
            base: Box::new(to_syn_prec(receiver, prec::POSTFIX)),
            dot_token: token::Dot::default(),
            member: Member::Unnamed(verus_syn::Index {
                index: *index as u32,
                span: Span::call_site(),
            }),
        }),
        LiftedExpr::Cast { value, ty } => structural(&format!("{} as {}", src(value), ty)),
        LiftedExpr::Closure { params, body, .. } => {
            let ps =
                params.iter().map(|p| safe_ident(p).to_string()).collect::<Vec<_>>().join(", ");
            structural(&format!("|{}| {}", ps, src(body)))
        }
        LiftedExpr::StructLiteral { name, fields } => {
            let body = fields
                .iter()
                .map(|(f, v)| format!("{}: {}", safe_ident(f), src(v)))
                .collect::<Vec<_>>()
                .join(", ");
            structural(&format!("{} {{ {} }}", name, body))
        }
        LiftedExpr::MethodCall { receiver, method, args } => method_call(
            to_syn_prec(receiver, prec::POSTFIX),
            method,
            args.iter().map(|a| to_syn_prec(a, prec::LOWEST)).collect(),
        ),
        LiftedExpr::Choose { binders, body, .. } => {
            let bs = binders.iter().map(fmt_binder).collect::<Vec<_>>().join(", ");
            structural(&format!("choose|{}| {}", bs, src(body)))
        }
        LiftedExpr::ArrayLiteral(elems) => {
            let items = elems.iter().map(src).collect::<Vec<_>>().join(", ");
            structural(&format!("[{}]", items))
        }
        LiftedExpr::Opaque(s) => verbatim(s),
    }
}

fn maybe_paren(e: Expr, need: bool) -> Expr {
    if need {
        Expr::Paren(ExprParen {
            attrs: vec![],
            paren_token: token::Paren::default(),
            expr: Box::new(e),
        })
    } else {
        e
    }
}

fn lower_name(name: &LiftedName) -> Expr {
    let base = path_expr(&name.source_name);
    match name.kind {
        NameKind::Old => func_call(path_expr("old"), vec![base]),
        _ => base,
    }
}

fn lower_call(func: &LiftedFunction, args: &[LiftedExpr]) -> Expr {
    match &func.role {
        // recv.len()
        FunctionRole::LenMethod { .. } if args.len() == 1 => {
            method_call(to_syn_prec(&args[0], prec::POSTFIX), "len", vec![])
        }
        // recv.method(rest..)
        FunctionRole::UserDefined { is_method: true, .. } if !args.is_empty() => {
            let recv = to_syn_prec(&args[0], prec::POSTFIX);
            let rest = args[1..].iter().map(|a| to_syn_prec(a, prec::LOWEST)).collect();
            method_call(recv, &func.source_name, rest)
        }
        // name(args..)
        _ => {
            let a = args.iter().map(|a| to_syn_prec(a, prec::LOWEST)).collect();
            func_call(path_expr(&func.source_name), a)
        }
    }
}

// ---- small verus_syn builders -------------------------------------------------

/// Build a syntactically-legal identifier from an arbitrary AIR-derived string.
///
/// `SynIdent::new` panics on input that isn't a legal Rust identifier (e.g. a type
/// parameter's trailing `&`, giving `N&`). We sanitize instead: non-identifier chars become
/// `_`, a leading digit is prefixed with `_`, and the empty / lone-`_` cases are padded — so
/// the AIR->syn bridge never panics. Correct source spellings are recovered upstream by
/// name-cleaning; this is the last-resort net.
fn safe_ident(s: &str) -> SynIdent {
    let mut out: String =
        s.chars().map(|c| if c.is_alphanumeric() || c == '_' { c } else { '_' }).collect();
    match out.chars().next() {
        None => out.push_str("__"),
        Some(c) if c.is_ascii_digit() => out.insert(0, '_'),
        _ => {}
    }
    if out == "_" {
        out.push('_');
    }
    SynIdent::new(&out, Span::call_site())
}

fn path_expr(name: &str) -> Expr {
    let mut segments: Punctuated<PathSegment, token::PathSep> = Punctuated::new();
    for seg in name.split("::").filter(|s| !s.is_empty()) {
        segments.push(PathSegment {
            ident: safe_ident(seg),
            arguments: PathArguments::None,
        });
    }
    if segments.is_empty() {
        segments.push(PathSegment {
            ident: SynIdent::new("_", Span::call_site()),
            arguments: PathArguments::None,
        });
    }
    Expr::Path(ExprPath {
        attrs: vec![],
        qself: None,
        path: Path { leading_colon: None, segments },
    })
}

fn func_call(func: Expr, args: Vec<Expr>) -> Expr {
    let mut punct = Punctuated::new();
    for a in args {
        punct.push(a);
    }
    Expr::Call(ExprCall {
        attrs: vec![],
        func: Box::new(func),
        paren_token: token::Paren::default(),
        args: punct,
        atomically: None,
    })
}

fn method_call(receiver: Expr, method: &str, args: Vec<Expr>) -> Expr {
    let mut punct = Punctuated::new();
    for a in args {
        punct.push(a);
    }
    Expr::MethodCall(ExprMethodCall {
        attrs: vec![],
        receiver: Box::new(receiver),
        dot_token: token::Dot::default(),
        method: safe_ident(method),
        turbofish: None,
        paren_token: token::Paren::default(),
        args: punct,
        atomically: None,
    })
}

fn verbatim(s: &str) -> Expr {
    match s.parse::<proc_macro2::TokenStream>() {
        Ok(tokens) => Expr::Verbatim(tokens),
        Err(_) => path_expr("_"),
    }
}

/// Render a sub-expression to source text by lowering it through `to_syn` first, so that any
/// `Opaque` leaf degrades to a lexable `_` rather than injecting non-lexable raw text. This is
/// what keeps the compound forms free of the "verbatim cliff" (a bad leaf can no longer break
/// the whole enclosing form).
fn src(e: &LiftedExpr) -> String {
    use quote::ToTokens;
    to_syn_prec(e, prec::LOWEST).to_token_stream().to_string()
}

/// Parse assembled source into a real, structured `verus_syn::Expr`. Because every piece was
/// produced by `to_syn` (hence lexable), this parse succeeds and yields a structural node
/// rather than `Expr::Verbatim`; it falls back to verbatim only if parsing somehow fails, which
/// preserves totality. `Opaque` remains the only intentional verbatim output of `to_syn`.
fn structural(s: &str) -> Expr {
    verus_syn::parse_str::<Expr>(s).unwrap_or_else(|_| verbatim(s))
}

/// Format a quantifier/choose binder as `name` or `name: type`, emitting the source-level type
/// when it is known (so `to_syn` produces `forall|i: int| ...`, not the under-typed `forall|i|`).
fn fmt_binder(b: &LiftedName) -> String {
    let name = safe_ident(&b.source_name).to_string();
    match &b.typ {
        Some(t) => format!("{}: {}", name, t),
        None => name,
    }
}

fn binop_info(op: BinOp) -> (SynBinOp, u8, u8) {
    use prec::*;
    match op {
        BinOp::Or => (SynBinOp::Or(token::OrOr::default()), OR, OR + 1),
        BinOp::And => (SynBinOp::And(token::AndAnd::default()), AND, AND + 1),
        BinOp::Eq => (SynBinOp::Eq(token::EqEq::default()), CMP, CMP),
        BinOp::Ne => (SynBinOp::Ne(token::Ne::default()), CMP, CMP),
        BinOp::Lt => (SynBinOp::Lt(token::Lt::default()), CMP, CMP),
        BinOp::Le => (SynBinOp::Le(token::Le::default()), CMP, CMP),
        BinOp::Gt => (SynBinOp::Gt(token::Gt::default()), CMP, CMP),
        BinOp::Ge => (SynBinOp::Ge(token::Ge::default()), CMP, CMP),
        BinOp::Add => (SynBinOp::Add(token::Plus::default()), ADD, ADD + 1),
        BinOp::Sub => (SynBinOp::Sub(token::Minus::default()), ADD, ADD + 1),
        BinOp::Mul => (SynBinOp::Mul(token::Star::default()), MUL, MUL + 1),
        BinOp::Div => (SynBinOp::Div(token::Slash::default()), MUL, MUL + 1),
        BinOp::Mod => (SynBinOp::Rem(token::Percent::default()), MUL, MUL + 1),
        BinOp::Implies => (SynBinOp::Imply(token::Imply::default()), IMPLY, IMPLY),
        BinOp::ExtEq => (SynBinOp::ExtEq(token::TildeEq::default()), CMP, CMP),
        BinOp::BitOr => (SynBinOp::BitOr(token::Or::default()), CMP, CMP + 1),
        BinOp::BitXor => (SynBinOp::BitXor(token::Caret::default()), CMP, CMP + 1),
        BinOp::BitAnd => (SynBinOp::BitAnd(token::And::default()), CMP, CMP + 1),
        BinOp::Shl => (SynBinOp::Shl(token::Shl::default()), ADD, ADD + 1),
        BinOp::Shr => (SynBinOp::Shr(token::Shr::default()), ADD, ADD + 1),
    }
}

fn unop(op: UnOp) -> SynUnOp {
    match op {
        UnOp::Not => SynUnOp::Not(token::Not::default()),
        UnOp::Neg => SynUnOp::Neg(token::Minus::default()),
        UnOp::BitNot => SynUnOp::Not(token::Not::default()),
        UnOp::Deref => SynUnOp::Deref(token::Star::default()),
    }
}

/// Collapse the spacing `verus_syn`'s token printer inserts (`v . len ()` → `v.len()`).
pub fn compact_tokens_safe(s: &str) -> String {
    s.replace(" .", ".")
        .replace(". ", ".")
        .replace(" !", "!")
        .replace(" (", "(")
        .replace("( ", "(")
        .replace(" )", ")")
        .replace(" [", "[")
        .replace("[ ", "[")
        .replace(" ]", "]")
        .replace(" ,", ",")
        .replace(":: ", "::")
        .replace(" ::", "::")
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lifted::LiftedName;
    use quote::ToTokens;

    fn int(n: &str) -> LiftedExpr {
        LiftedExpr::Literal(LitValue::Int(n.to_string()))
    }
    fn bin(op: BinOp, l: LiftedExpr, r: LiftedExpr) -> LiftedExpr {
        LiftedExpr::BinaryOp { op, lhs: Box::new(l), rhs: Box::new(r) }
    }
    fn deref(e: LiftedExpr) -> LiftedExpr {
        LiftedExpr::UnaryOp { op: UnOp::Deref, operand: Box::new(e) }
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
    /// The bridge's contract: it produces a *legal* verus_syn::Expr — i.e. its
    /// tokens re-parse as a Verus expression. (Exact spelling is the client's
    /// printer's concern; see `crate::render` for the compact string form.)
    fn is_legal(e: &LiftedExpr) -> bool {
        verus_syn::parse2::<Expr>(to_syn(e).to_token_stream()).is_ok()
    }

    #[test]
    fn bridge_output_is_legal_verus() {
        assert!(is_legal(&bin(BinOp::Gt, LiftedExpr::var("x"), int("100"))));
        assert!(is_legal(&bin(BinOp::Eq, deref(LiftedExpr::var("x")), deref(old("x")))));
        assert!(is_legal(&bin(BinOp::ExtEq, LiftedExpr::var("s1"), LiftedExpr::var("s2"))));
        assert!(is_legal(&bin(BinOp::Implies, LiftedExpr::var("p"), LiftedExpr::var("q"))));
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
            body: Box::new(bin(BinOp::Lt, LiftedExpr::var("i"), LiftedExpr::var("n"))),
            triggers: Vec::new(),
        };
        assert!(is_legal(&q));
    }

    #[test]
    fn precedence_parens_in_ast() {
        // (a + b) * c — the bridge must insert a Paren node so it tokenizes correctly.
        let sum = bin(BinOp::Add, LiftedExpr::var("a"), LiftedExpr::var("b"));
        let s = to_syn(&bin(BinOp::Mul, sum, LiftedExpr::var("c"))).to_token_stream().to_string();
        assert!(s.contains('('), "expected precedence parens, got: {}", s);
    }

    // ---- to_syn totality & fidelity tests -----------------------------------------

    fn binder(name: &str, ty: Option<&str>) -> LiftedName {
        LiftedName {
            source_name: name.to_string(),
            version: None,
            version_line: None,
            decl_line: None,
            kind: NameKind::QuantBinder,
            typ: ty.map(str::to_string),
        }
    }
    fn user_fn(name: &str) -> LiftedFunction {
        LiftedFunction {
            source_name: name.to_string(),
            role: FunctionRole::UserDefined { type_arg_count: 0, is_method: false },
            type_arg_count: 0,
        }
    }
    fn tok(e: &LiftedExpr) -> String {
        to_syn(e).to_token_stream().to_string()
    }

    /// `to_syn` must never panic on names that aren't legal Rust identifiers (e.g. a
    /// type-parameter's trailing `&`); it must produce a legal `Expr` instead.
    #[test]
    fn to_syn_never_panics_on_undisplayable_names() {
        assert!(is_legal(&LiftedExpr::var("N&")), "type-param suffix name");
        assert!(is_legal(&LiftedExpr::var("has space")), "name with a space");
        assert!(is_legal(&LiftedExpr::var("")), "empty name");
        assert!(is_legal(&LiftedExpr::var("123")), "leading-digit name");
        assert!(
            is_legal(&LiftedExpr::FieldAccess {
                receiver: Box::new(LiftedExpr::var("s")),
                field: "f&".to_string(),
            }),
            "non-ident field"
        );
    }

    /// Quantifier/choose binder *types* must survive into `to_syn` output
    /// (`forall|i: int| ...`, not `forall|i| ...`).
    #[test]
    fn to_syn_emits_binder_types() {
        let q = LiftedExpr::Quantifier {
            kind: QuantKind::Forall,
            binders: vec![binder("i", Some("int"))],
            body: Box::new(bin(BinOp::Lt, LiftedExpr::var("i"), LiftedExpr::var("n"))),
            triggers: Vec::new(),
        };
        let s = tok(&q);
        assert!(s.contains("int"), "binder type dropped; got: {}", s);
    }

    /// An `Opaque` inside a quantifier must remain a *local* leaf, not collapse the whole
    /// form to `_`.
    #[test]
    fn to_syn_localizes_opaque_in_quantifier() {
        let q = LiftedExpr::Quantifier {
            kind: QuantKind::Forall,
            binders: vec![binder("i", Some("int"))],
            // Non-lexable raw text (unbalanced paren): under the verbatim shortcut this makes
            // the whole quantifier string fail to parse and collapse to `_`.
            body: Box::new(LiftedExpr::Opaque("f(x".to_string())),
            triggers: Vec::new(),
        };
        let s = tok(&q);
        assert!(s.contains("forall"), "whole quantifier collapsed to _; got: {}", s);
    }

    /// The six compound forms must be real `verus_syn` nodes, never `Expr::Verbatim`.
    /// Only `Opaque` may lower to verbatim.
    #[test]
    fn to_syn_compound_forms_are_structural() {
        let body = || Box::new(bin(BinOp::Lt, LiftedExpr::var("i"), int("1")));
        let compound = vec![
            LiftedExpr::Quantifier {
                kind: QuantKind::Forall,
                binders: vec![binder("i", Some("int"))],
                body: body(),
                triggers: vec![],
            },
            LiftedExpr::Choose {
                binders: vec![binder("i", Some("int"))],
                body: body(),
                triggers: vec![],
            },
            LiftedExpr::IfThenElse {
                cond: Box::new(LiftedExpr::var("c")),
                then_: Box::new(int("1")),
                else_: Box::new(int("2")),
            },
            LiftedExpr::Cast { value: Box::new(LiftedExpr::var("x")), ty: "int".to_string() },
            LiftedExpr::Closure { params: vec!["a".to_string()], body: body(), triggers: vec![] },
            LiftedExpr::StructLiteral {
                name: "S".to_string(),
                fields: vec![("f".to_string(), int("1"))],
            },
        ];
        for e in &compound {
            assert!(
                !matches!(to_syn(e), Expr::Verbatim(_)),
                "compound form lowered to verbatim, not a structural node: {:?}",
                e
            );
        }
    }

    /// Totality: every `LiftedExpr` variant lowers without panic to legal Verus.
    #[test]
    fn to_syn_matrix_is_total() {
        let v = || LiftedExpr::var("x");
        let b = || Box::new(v());
        let corpus = vec![
            v(),
            LiftedExpr::Literal(LitValue::Bool(true)),
            LiftedExpr::Literal(LitValue::Int(
                "340282366920938463463374607431768211456".into(), // bignum (> u128)
            )),
            LiftedExpr::Literal(LitValue::Int("1.5".into())), // malformed int: must not panic
            LiftedExpr::Literal(LitValue::Real("1.5".into())),
            bin(BinOp::Add, v(), v()),
            LiftedExpr::UnaryOp { op: UnOp::Deref, operand: b() },
            LiftedExpr::FunctionCall { func: user_fn("f"), args: vec![v()] },
            LiftedExpr::Apply { callee: b(), args: vec![v()] },
            LiftedExpr::FieldAccess { receiver: b(), field: "f".into() },
            LiftedExpr::Index { receiver: b(), index: b() },
            LiftedExpr::Quantifier {
                kind: QuantKind::Forall,
                binders: vec![binder("i", Some("int"))],
                body: b(),
                triggers: vec![],
            },
            LiftedExpr::IfThenElse { cond: b(), then_: b(), else_: b() },
            LiftedExpr::Tuple(vec![v(), v()]),
            LiftedExpr::TupleField { receiver: b(), index: 0 },
            LiftedExpr::Cast { value: b(), ty: "int".into() },
            LiftedExpr::Closure { params: vec!["a".into()], body: b(), triggers: vec![] },
            LiftedExpr::StructLiteral { name: "S".into(), fields: vec![("f".into(), v())] },
            LiftedExpr::MethodCall { receiver: b(), method: "m".into(), args: vec![] },
            LiftedExpr::Choose {
                binders: vec![binder("i", Some("int"))],
                body: b(),
                triggers: vec![],
            },
            LiftedExpr::ArrayLiteral(vec![v(), v()]),
            LiftedExpr::Opaque("x + 1".into()),
        ];
        // Exhaustiveness reminder: adding a `LiftedExpr` variant breaks this match until the
        // corpus above is extended to cover it.
        for e in &corpus {
            match e {
                LiftedExpr::Var(_)
                | LiftedExpr::Literal(_)
                | LiftedExpr::BinaryOp { .. }
                | LiftedExpr::UnaryOp { .. }
                | LiftedExpr::FunctionCall { .. }
                | LiftedExpr::Apply { .. }
                | LiftedExpr::FieldAccess { .. }
                | LiftedExpr::Index { .. }
                | LiftedExpr::Quantifier { .. }
                | LiftedExpr::IfThenElse { .. }
                | LiftedExpr::Tuple(_)
                | LiftedExpr::TupleField { .. }
                | LiftedExpr::Cast { .. }
                | LiftedExpr::Closure { .. }
                | LiftedExpr::StructLiteral { .. }
                | LiftedExpr::MethodCall { .. }
                | LiftedExpr::Choose { .. }
                | LiftedExpr::ArrayLiteral(_)
                | LiftedExpr::Opaque(_) => {}
            }
        }
        for e in &corpus {
            assert!(is_legal(e), "not legal Verus: {:?}", e);
        }
    }
}
