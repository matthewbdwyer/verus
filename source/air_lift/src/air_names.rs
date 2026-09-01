//! AIR name parsing, encoding helpers, and the AIR/VIR encoding constants used when
//! lifting.
//!
//! Constants that `vir::def` or `air::def` export are re-exported below. The remainder
//! duplicate definitions those crates keep private, and are annotated with their source
//! so the two can be kept in step.

// Re-exported from vir::def (pub)
pub use vir::def::{
    ADD, ARCH_SIZE, ARRAY_INDEX, ARRAY_NEW, AS_TYPE, AUTOSPEC_FUNC_SUFFIX, BIT_AND, BIT_NOT,
    BIT_OR, BIT_SHL, BIT_SHR, BIT_XOR, BOX_BOOL, BOX_INT, CHAR_CLIP, CHAR_INV,
    CHECK_DECREASE_HEIGHT, CLOSURE_ENS, CLOSURE_REQ, CONST_BOOL, CONST_INT, DECORATE_ARC,
    DECORATE_BOX, DECORATE_DST_INHERIT, DECORATE_NIL_SIZED, DECORATE_RC, DECORATE_REF,
    DECORATION, DEFAULT_ENSURES, EUC_DIV, EUC_MOD, EXT_EQ, FNDEF_SINGLETON, FUEL_BOOL,
    FUEL_BOOL_DEFAULT, FUEL_DEFAULTS, HAS_TYPE, HEIGHT, HEIGHT_LT, HEIGHT_REC_FUN, I_CLIP, I_HI,
    I_INV, I_LO, MK_FUN, MUL, MUT_REF_CURRENT, MUT_REF_FUTURE, MUT_REF_UPDATE_CURRENT, NAT_CLIP,
    POLY, RADD, RDIV, RETURN_VALUE, RMUL, RSUB, STRSLICE_GET_CHAR, STRSLICE_LEN,
    STRSLICE_NEW_STRLIT, SUB, SUFFIX_PARAM, TYPE_ID_ARRAY, TYPE_ID_BOOL, TYPE_ID_CONST_INT,
    TYPE_ID_INT, TYPE_ID_NAT, TYPE_ID_SINT, TYPE_ID_UINT, U_CLIP, U_HI, U_INV,
};

// from vir::def (pub) — prophecy resolution predicate
pub use vir::def::HAS_RESOLVED;

// from vir::def (private: DUMMY_PARAM)
pub const DUMMY_PARAM: &str = "no%param";

// from air::def (private module)
// The following six duplicate constants of the same name in `air::def`, which is a private
// module and so cannot be re-exported. Reconsider if `air::def` becomes public.
pub const LAMBDA: &str = "%%lambda%%";
pub const APPLY: &str = "%%apply%%";
pub const SWITCH_LABEL: &str = "%%switch_label%%";
pub const PREFIX_LABEL: &str = "%%location_label%%";
pub const GLOBAL_PREFIX_LABEL: &str = "%%global_location_label%%";

// from vir::def (private)
pub const SUFFIX_GLOBAL: &str = "?";
pub const SUFFIX_GLOBAL_CHAR: char = '?';
pub const SUFFIX_PARAM_CHAR: char = '!';
pub const SUFFIX_LOCAL_STMT: &str = "@";
pub const SUFFIX_LOCAL_STMT_CHAR: char = '@';
pub const SUFFIX_LOCAL_EXPR: &str = "$";
pub const SUFFIX_LOCAL_EXPR_CHAR: char = '$';
/// vir's `SUFFIX_TYPE_PARAM` — type parameters (including const generics) are encoded with a
/// trailing `&`, e.g. a const generic `N` becomes the AIR name `N&`.
pub const SUFFIX_TYPE_PARAM: &str = "&";
pub const SUFFIX_TYPE_PARAM_CHAR: char = '&';

// from vir::def (private)
pub const PREFIX_ENSURES: &str = "ens%";
pub const PREFIX_REQUIRES: &str = "req%";
pub const PREFIX_FUEL: &str = "fuel%"; // pub as FUEL_PARAM in vir::def
// Duplicates the private `vir::def::PREFIX_TEMP_VAR`. Note that `ast_simplify` introduces a
// second family of temporaries under `vir::def::PREFIX_SIMPLIFY_TEMP_VAR` ("tmp%%"), which
// this prefix also matches. Reconsider if either becomes public.
pub const PREFIX_TMP_VAR: &str = "tmp%";
pub const PREFIX_TMP_LET: &str = "tmp%%";
pub const PREFIX_DECREASE_INIT: &str = "decrease%init";
pub const PREFIX_TRAIT_BOUND: &str = "tr_bound%";
pub const AUTOSPEC_SUFFIX: &str = "%autospec";

pub const PREFIX_BOXED: &str = "Poly%";
pub const PREFIX_UNBOXED: &str = "%Poly%";

// Duplicates the private `vir::def::PREFIX_IMPL_IDENT`, the prefix of the idents
// `vir::def::impl_ident` generates for impl blocks. Reconsider if it becomes public.
pub const PREFIX_IMPL_IDENT: &str = "impl&%";
pub const PREFIX_RECURSIVE: &str = "rec%";
pub const TRAIT_DEFAULT_SEPARATOR: &str = "%default%";

pub const RETURN_CLEAN_NAME: &str = "result";

pub const SIZED_BOUND: &str = "sized";
pub const UNKNOWN_VAR: &str = "_unknown";
pub const SPEC_UNWRAP: &str = "spec_unwrap";
pub const FOR_LOOP_GHOST_ITERATOR: &str = "ForLoopGhostIterator";
/// The wrapper struct the for-loop desugaring introduces around an iterator
/// (`vstd::std_specs::iter::VerusForLoopWrapper`). Its accessors/relations
/// (e.g. `.iter`, the prophetic `initial_value_relation`) are machinery.
pub const FOR_LOOP_WRAPPER: &str = "VerusForLoopWrapper";
pub const SNAPSHOT_INITIAL: &str = "__initial__";

pub const OPTION_SOME_VARIANT_FIELD: &str = "/Some/0";
pub const IS_VARIANT_PREFIX: &str = "is-";

pub const HOLE: &str = "%%hole%%";
pub const CHOOSE: &str = "%%choose%%";

// Synthetic function name for collapsed reveal_strlit rendering
pub const REVEAL_STRLIT: &str = "reveal_strlit";

pub const EXPAND_PREFIX: &str = "expand%";
pub const CLOSURE_RETURN_PREFIX: &str = "%closure_return";
pub const CLOSURE_PREFIX: &str = "closure%";
pub const IMPL_PREFIX: &str = "impl%";

pub const VERUS_LOOP_RESULT: &str = "VERUS_loop_result";
pub const VERUS_GHOST_ITER: &str = "VERUS_ghost_iter";
pub const VERUS_LOOP_NEXT: &str = "VERUS_loop_next";
pub const VERUS_LOOP_VAL: &str = "VERUS_loop_val";
pub const VERUS_ITER: &str = "VERUS_iter";
pub const VERUS_OLD_ITER: &str = "VERUS_old_iter";
pub const VERUS_TMP_PREFIX: &str = "verus_tmp";

pub const VERUS_LOOP_VARS: &[&str] = &[
    VERUS_LOOP_RESULT,
    VERUS_GHOST_ITER,
    VERUS_LOOP_NEXT,
    VERUS_LOOP_VAL,
    VERUS_ITER,
    VERUS_OLD_ITER,
];

/// Method/spec-function names from the vstd `IteratorSpec` machinery that a
/// `for` loop desugars into. These are auto-generated for `for x in it`
/// (the user never writes them), so they are boilerplate.
/// (A *custom* iterator's implementations of these are user-written, but they are
/// filtered the same way.)
pub const ITERATOR_SPEC_METHODS: &[&str] = &[
    "obeys_prophetic_iter_laws",
    "will_return_none",
    "initial_value_relation",
    "trigger_peek_implications",
    "peek",
    "remaining",
];


// ---------------------------------------------------------------------------
// AIR encoding characters and helpers
// ---------------------------------------------------------------------------

pub const AIR_POLY_PREFIX: &str = "%";
pub const AIR_IMPL_IDENT_CHAR: char = '&';
pub const AIR_PATH_SEPARATOR_CHAR: char = '.';
pub const AIR_DECORATE_TYPE_PARAM: &str = "&.";
pub const AIR_SUBST_RENAME_SEP: &str = "$$";

pub const PREFIX_TYPE_ID: &str = "TYPE%";
pub const SUFFIX_CLIP: &str = "Clip";
pub const PREFIX_TUPLE: &str = "tuple%";

pub const SENTINEL_LOOP: &str = "__LOOP__";
pub const SENTINEL_INIT: &str = "__INIT__";

/// Returns true if the name contains AIR encoding characters (%)
/// but is not a legitimate Verus path component.
pub fn is_air_internal(s: &str) -> bool {
    s.contains(AIR_POLY_PREFIX)
        && !s.contains(PREFIX_IMPL_IDENT)
        && !s.contains(PREFIX_RECURSIVE)
        && !s.contains(TRAIT_DEFAULT_SEPARATOR)
}

pub const AIR_SUFFIX_CHARS: &[char] = &[
    SUFFIX_LOCAL_STMT_CHAR,
    SUFFIX_PARAM_CHAR,
    SUFFIX_GLOBAL_CHAR,
    SUFFIX_LOCAL_EXPR_CHAR,
    SUFFIX_TYPE_PARAM_CHAR,
    AIR_PATH_SEPARATOR_CHAR,
    AIR_IMPL_IDENT_CHAR,
];

// ---------------------------------------------------------------------------
// AirName: structured AIR name parser
// ---------------------------------------------------------------------------

#[derive(Debug, PartialEq)]
pub enum AirName<'a> {
    Requires(&'a str),
    Ensures(&'a str),
    Fuel(&'a str),
    TmpVar(&'a str),
    Lambda(u32),
    Apply(u32),
    SwitchLabel(u32),
    LocationLabel(u32),
    GlobalLocationLabel(u32),
    Boxed(&'a str),
    Unboxed(&'a str),
    TypeId(&'a str),
    Clip,
    DecreaseInit,
    TraitBound,
    Plain(&'a str),
}

impl<'a> AirName<'a> {
    pub fn parse(s: &'a str) -> Self {
        if let Some(rest) = s.strip_prefix(PREFIX_REQUIRES) {
            return AirName::Requires(rest);
        }
        if let Some(rest) = s.strip_prefix(PREFIX_ENSURES) {
            return AirName::Ensures(rest);
        }
        if let Some(rest) = s.strip_prefix(PREFIX_FUEL) {
            return AirName::Fuel(rest);
        }
        if s.starts_with(PREFIX_TMP_VAR) {
            return AirName::TmpVar(s);
        }
        if s.starts_with(PREFIX_DECREASE_INIT) {
            return AirName::DecreaseInit;
        }
        if s.starts_with(PREFIX_TRAIT_BOUND) {
            return AirName::TraitBound;
        }
        if s.ends_with(SUFFIX_CLIP) {
            return AirName::Clip;
        }
        if let Some(rest) = s.strip_prefix(LAMBDA)
            && let Ok(n) = rest.parse::<u32>()
        {
            return AirName::Lambda(n);
        }
        if let Some(rest) = s.strip_prefix(APPLY)
            && let Ok(n) = rest.parse::<u32>()
        {
            return AirName::Apply(n);
        }
        if let Some(rest) = s.strip_prefix(SWITCH_LABEL)
            && let Ok(n) = rest.parse::<u32>()
        {
            return AirName::SwitchLabel(n);
        }
        if let Some(rest) = s.strip_prefix(GLOBAL_PREFIX_LABEL)
            && let Ok(n) = rest.parse::<u32>()
        {
            return AirName::GlobalLocationLabel(n);
        }
        if let Some(rest) = s.strip_prefix(PREFIX_LABEL)
            && let Ok(n) = rest.parse::<u32>()
        {
            return AirName::LocationLabel(n);
        }
        if let Some(rest) = s.strip_prefix(PREFIX_UNBOXED) {
            return AirName::Unboxed(rest);
        }
        if let Some(rest) = s.strip_prefix(PREFIX_BOXED) {
            return AirName::Boxed(rest);
        }
        if let Some(rest) = s.strip_prefix(PREFIX_TYPE_ID) {
            return AirName::TypeId(rest);
        }
        AirName::Plain(s)
    }

    pub fn is_location_label(&self) -> bool {
        matches!(
            self,
            AirName::LocationLabel(_) | AirName::GlobalLocationLabel(_) | AirName::SwitchLabel(_)
        )
    }
}

// ---------------------------------------------------------------------------
// Solver noise detection
// ---------------------------------------------------------------------------

pub fn is_solver_noise(s: &str) -> bool {
    s.starts_with(SWITCH_LABEL)
        || s.starts_with(PREFIX_LABEL)
        || s.starts_with(GLOBAL_PREFIX_LABEL)
        || s.starts_with(PREFIX_TYPE_ID)
        || s == FUEL_DEFAULTS
        || s == DECORATION
        || s == DECORATE_NIL_SIZED
        || s.ends_with(AIR_DECORATE_TYPE_PARAM)
}

/// Clean an AIR-encoded name for display: strip structural prefixes,
/// encoding characters, and suffix chars.
pub fn clean_air_name(s: &str) -> String {
    let base = match AirName::parse(s) {
        AirName::Boxed(rest) | AirName::Unboxed(rest) | AirName::TypeId(rest) => rest.to_string(),
        _ => s.to_string(),
    };
    let trimmed = base.trim_end_matches(AIR_SUFFIX_CHARS);
    let cleaned = trimmed.replace(AIR_POLY_PREFIX, "");
    cleaned.replace(AIR_IMPL_IDENT_CHAR, "_")
}
