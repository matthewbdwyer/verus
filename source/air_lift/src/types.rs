//! Core classification types: function roles and variable classification.


/// Roles for AIR functions, used during lifting.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FunctionRole {
    FieldAccessor { type_arg_count: usize },
    VariantConstructor {
        variant_name: String,
        field_names: Vec<String>,
        type_arg_count: usize,
        /// True for a single-variant struct (variant name == type name), where
        /// the idiomatic form is `Type { .. }` / `Type(..)` rather than the
        /// enum-style `Type::Variant`. False for enum variants.
        is_struct: bool,
        /// AIR field-accessor function names, parallel to `field_names`. Used to
        /// decompose `X == Ctor { f: e, .. }` into `X.f == e` conjuncts.
        field_accessors: Vec<String>,
    },
    IteratorBoilerplate,
    /// Type/sizedness predicate (`has_type`, `sized`). Source-recovery: implicit in
    /// source binder types, so guard-stripped (`… ==> P` → `P`).
    TypeGuard,
    /// Fuel bookkeeping (`fuel_bool`, `fuel_bool_default`) — no source form.
    Fuel,
    /// Integer/char range invariants (`uHi`, `iLo`, `charInv`, …) — no source form.
    RangeInvariant,
    /// Recursion-height bookkeeping (`height`, `height_lt`, …) — no source form.
    RecursionHeight,
    /// Assorted solver-internal artifacts (`const_bool`, `arbitrary`, …) — no source
    /// form. Objective residual (replaces the former opinionated `Noise` catch-all).
    SolverInternal,
    TerminationCheck,
    ExtEq,
    LenMethod { type_arg_count: usize },
    IndexOp { type_arg_count: usize },
    PushMethod { type_arg_count: usize },
    AddOp { type_arg_count: usize },
    ContainsKeyOp { type_arg_count: usize },
    SubrangeOp { type_arg_count: usize },
    BitNot,
    BitShr,
    BitShl,
    UserDefined { type_arg_count: usize, is_method: bool },
    VariantDiscriminant { type_name: String, variant_name: String },
    Clip,
    IntCoerce,
    SpecUnwrap,
    TupleConstructor { _arity: usize },
    TupleProjection { _arity: usize, index: usize },
    OptionUnwrap,
    ArithOp,
    BitBinOp,
    /// `mut_ref_current%(m)` — the current value of a `&mut`; renders `*m`
    /// (field access auto-derefs: `(*p).f` → `p.f`).
    MutRefCurrent,
    /// `mut_ref_future%(m)` — prophecy future value; renders `mut_ref_future(m)`.
    MutRefFuture,
    /// `mut_ref_update_current%(m, v)` — `m` with its current value set to `v`.
    MutRefUpdateCurrent,
    /// `has_resolved`/`resolved(dcr, typ, m)` — prophecy resolution predicate;
    /// renders `has_resolved(m)` (2 leading type/decoration args stripped).
    HasResolved,
    /// `closure_ens(<3 type args>, closure, args_tuple, ret)` — the postcondition
    /// of a `Fn`-value call. Renders `call_ensures(closure, args, ret)` (abstract),
    /// or is instantiated against the closure's definition axiom when known.
    ClosureEns,
    /// `closure_req(<3 type args>, closure, args_tuple)` — the precondition of a
    /// `Fn`-value call. Renders `call_requires(closure, args)`.
    ClosureReq,
}

impl FunctionRole {
    pub fn type_arg_count(&self) -> usize {
        match self {
            FunctionRole::UserDefined { type_arg_count, .. }
            | FunctionRole::LenMethod { type_arg_count }
            | FunctionRole::IndexOp { type_arg_count }
            | FunctionRole::PushMethod { type_arg_count }
            | FunctionRole::AddOp { type_arg_count }
            | FunctionRole::ContainsKeyOp { type_arg_count }
            | FunctionRole::SubrangeOp { type_arg_count }
            | FunctionRole::FieldAccessor { type_arg_count, .. }
            | FunctionRole::VariantConstructor { type_arg_count, .. } => *type_arg_count,
            // resolved(decoration, typ, m) — strip the 2 leading type args.
            FunctionRole::HasResolved => 2,
            // closure_ens/closure_req carry 3 leading type/decoration args before
            // the closure value / args-tuple / ret.
            FunctionRole::ClosureEns | FunctionRole::ClosureReq => 3,
            _ => 0,
        }
    }

    /// True for roles that are solver bookkeeping with no source form. `air_lift`
    /// source-recovers these *within* expressions (strips them from conjunctions /
    /// guards); collection-level filtering of whole assumptions is the consumer's.
    pub fn is_bookkeeping(&self) -> bool {
        matches!(
            self,
            FunctionRole::TypeGuard
                | FunctionRole::Fuel
                | FunctionRole::RangeInvariant
                | FunctionRole::RecursionHeight
                | FunctionRole::SolverInternal
        )
    }
}

/// Pre-computed variable classification for rendering.
#[derive(Debug, Clone)]
pub enum VarInfo {
    Current { clean_name: String },
    Old { clean_name: String },
    Intermediate { clean_name: String, line: u32, kind: IntermediateKind },
    Temporary,
    Noise,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IntermediateKind {
    Loop,
    Merge,
    Mutation,
    QuantBinder,
}

/// Classifies the source-level origin of a span_map entry.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum SpanKind {
    LoopEntry,
    Other,
}

impl SpanKind {
    pub fn is_loop(&self) -> bool {
        matches!(self, SpanKind::LoopEntry)
    }
}
