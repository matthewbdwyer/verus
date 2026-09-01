//! Pure `FunctionRole` classifier: `vir` krate/datatypes -> role + friendly-name maps.
//!
//! Holds no observer state: classification is a pure function of the krate, and so is
//! independently testable (feed a function or datatype, assert the classified role).
//! Invoked once per krate from `AirLift`'s `VirObserver::on_krate`
//! (see `crate::accumulate`).

use std::collections::HashMap;
use std::sync::Arc;

use air::ast::Ident;
use vir::ast::{Dt, Krate};
use vir::ast_util::{fun_as_friendly_rust_name, path_as_friendly_rust_name};
use vir::def::{NameCtxt, encode_dt_as_path, suffix_global_id};
use vir::vir_observer::line_from_span;

use crate::air_names::*;
use crate::state::GlobalAnnotations;
use crate::types::FunctionRole;

fn insert_role(fr: &mut HashMap<Ident, FunctionRole>, name: &str, role: FunctionRole) {
    fr.insert(Arc::new(name.to_string()), role.clone());
    fr.insert(Arc::new(format!("%{}", name)), role);
}

/// Build GlobalAnnotations from the full krate.
pub fn build_global_annotations(
    krate: &Krate,
    name_ctxt: &NameCtxt,
    current_crate: &vir::ast::CrateId,
) -> GlobalAnnotations {
    let mut fr: HashMap<Ident, FunctionRole> = HashMap::new();
    let mut friendly_names: HashMap<Ident, String> = HashMap::new();
    let mut dt_fields: HashMap<Ident, String> = HashMap::new();
    let mut field_update_names: HashMap<Ident, String> = HashMap::new();

    // --- Built-in roles ---
    register_builtin_roles(&mut fr);

    // --- Functions ---
    for func in &krate.functions {
        register_function(func, name_ctxt, &mut fr, &mut friendly_names);
    }

    // --- Datatypes ---
    for dt in &krate.datatypes {
        register_datatype(
            dt,
            name_ctxt,
            &mut fr,
            &mut friendly_names,
            &mut dt_fields,
            &mut field_update_names,
        );
    }

    // --- Tuple constructors/projections (built-in, arity 0..=12) ---
    for arity in 0..=12usize {
        let tuple_type = format!("{}{}", PREFIX_TUPLE, arity);
        let ctor = format!("{}./{}", tuple_type, tuple_type);
        insert_role(&mut fr, &ctor, FunctionRole::TupleConstructor { _arity: arity });
        for k in 0..arity {
            let proj = format!("{}./{}/{}", tuple_type, tuple_type, k);
            insert_role(&mut fr, &proj, FunctionRole::TupleProjection { _arity: arity, index: k });
        }
    }

    // --- Option unwrap ---
    {
        let option_some_field = format!("core!option.Option.{}", OPTION_SOME_VARIANT_FIELD);
        insert_role(&mut fr, &option_some_field, FunctionRole::OptionUnwrap);
    }

    // --- User-facing rename aliases ---
    for (vir_path, name) in &krate.path_as_rust_names {
        let air_string = name_ctxt.path_to_string(vir_path);
        friendly_names.insert(Arc::new(air_string), name.clone());
    }

    // --- Return binding lines ---
    let mut ret_binding_lines: HashMap<Ident, u32> = HashMap::new();
    for func in &krate.functions {
        if func.x.ens_has_return {
            if let Some(line) = line_from_span(&func.x.ret.span) {
                let air_name = vir::def::suffix_local_unique_id(&func.x.ret.x.name);
                ret_binding_lines.insert(air_name, line);
            }
        }
    }

    GlobalAnnotations {
        function_roles: fr,
        friendly_names,
        datatype_field_names: dt_fields,
        field_update_names,
        ret_binding_lines,
        current_crate: Some(name_ctxt.krate_to_string(current_crate)),
    }
}

/// Register all built-in AIR function roles.
fn register_builtin_roles(fr: &mut HashMap<Ident, FunctionRole>) {
    use FunctionRole::*;
    let builtins: &[(&str, FunctionRole)] = &[
        (HAS_TYPE, TypeGuard),
        (SIZED_BOUND, TypeGuard),
        (AS_TYPE, IntCoerce),
        (CONST_INT, IntCoerce),
        (CONST_BOOL, SolverInternal),
        (FUEL_BOOL, Fuel),
        (FUEL_BOOL_DEFAULT, Fuel),
        (CHECK_DECREASE_HEIGHT, TerminationCheck),
        (BIT_NOT, BitNot),
        (BIT_SHR, BitShr),
        (BIT_SHL, BitShl),
        (EXT_EQ, ExtEq),
        (U_CLIP, Clip),
        (I_CLIP, Clip),
        (NAT_CLIP, Clip),
        (CHAR_CLIP, Clip),
        (U_INV, RangeInvariant),
        (I_INV, RangeInvariant),
        (BOX_INT, IntCoerce),
        (BOX_BOOL, IntCoerce),
        (MK_FUN, Clip),
        (SPEC_UNWRAP, SpecUnwrap),
        (ADD, ArithOp),
        (SUB, ArithOp),
        (MUL, ArithOp),
        (EUC_DIV, ArithOp),
        (EUC_MOD, ArithOp),
        (RADD, ArithOp),
        (RSUB, ArithOp),
        (RMUL, ArithOp),
        (RDIV, ArithOp),
        (BIT_XOR, BitBinOp),
        (BIT_AND, BitBinOp),
        (BIT_OR, BitBinOp),
        (CHAR_INV, RangeInvariant),
        (U_HI, RangeInvariant),
        (I_LO, RangeInvariant),
        (I_HI, RangeInvariant),
        (HEIGHT, RecursionHeight),
        (HEIGHT_LT, RecursionHeight),
        (HEIGHT_REC_FUN, RecursionHeight),
        (STRSLICE_LEN, LenMethod { type_arg_count: 0 }),
        (STRSLICE_GET_CHAR, IndexOp { type_arg_count: 0 }),
        (STRSLICE_NEW_STRLIT, UserDefined { type_arg_count: 0, is_method: false }),
        (CLOSURE_REQ, ClosureReq),
        (CLOSURE_ENS, ClosureEns),
        (DEFAULT_ENSURES, SolverInternal),
        (crate::air_names::MUT_REF_CURRENT, MutRefCurrent),
        (crate::air_names::MUT_REF_FUTURE, MutRefFuture),
        (crate::air_names::MUT_REF_UPDATE_CURRENT, MutRefUpdateCurrent),
        (crate::air_names::HAS_RESOLVED, HasResolved),
        (FNDEF_SINGLETON, SolverInternal),
        (ARRAY_NEW, UserDefined { type_arg_count: 0, is_method: false }),
        (ARRAY_INDEX, IndexOp { type_arg_count: 0 }),
    ];
    for (name, role) in builtins {
        insert_role(fr, name, role.clone());
    }
}

/// Determine the number of AIR type arguments for a function.
/// DECORATE=true: each type param contributes Dcr + Type = 2 args.
fn type_arg_count_for_func(func: &vir::ast::Function) -> usize {
    // Each type parameter contributes two AIR arguments, a decoration and the type.
    // This mirrors vir::def::types(), which is pub(crate) and so cannot be referenced;
    // the arity is replicated here and assumes vir's decoration encoding.
    const TYPES_PER_PARAM: usize = 2;
    let mut count = func.x.typ_params.len() * TYPES_PER_PARAM;
    // The dummy no%param added by ast_simplify for zero-param functions
    // becomes I(0) in AIR — count it as a type arg so the renderer skips it.
    if func.x.params.iter().any(|p| p.x.name.0.as_str() == crate::air_names::DUMMY_PARAM) {
        count += 1;
    }
    count
}

/// Register a single function's role and friendly name.
fn register_function(
    func: &vir::ast::Function,
    name_ctxt: &NameCtxt,
    fr: &mut HashMap<Ident, FunctionRole>,
    friendly_names: &mut HashMap<Ident, String>,
) {
    let air_name = Arc::new(name_ctxt.fun_to_string(&func.x.name));
    let air_name_q = suffix_global_id(&air_name);
    let type_arg_count = type_arg_count_for_func(func);

    let friendly = resolve_friendly_name(func);
    friendly_names.insert(air_name.clone(), friendly.clone());
    friendly_names.insert(air_name_q.clone(), friendly.clone());

    if friendly.contains(FOR_LOOP_GHOST_ITERATOR) {
        fr.insert(air_name, FunctionRole::IteratorBoilerplate);
        fr.insert(air_name_q, FunctionRole::IteratorBoilerplate);
        return;
    }

    let base = friendly
        .trim_end_matches(crate::air_names::AUTOSPEC_FUNC_SUFFIX)
        .trim_end_matches(AUTOSPEC_SUFFIX);

    let special_role = match base {
        s if s.ends_with("::arbitrary") => Some(FunctionRole::SolverInternal),
        s if s.ends_with("::len") || s.ends_with("::spec_vec_len") => {
            Some(FunctionRole::LenMethod { type_arg_count })
        }
        s if s.ends_with("::index") || s.ends_with("::spec_index") => {
            Some(FunctionRole::IndexOp { type_arg_count })
        }
        s if s.ends_with("::push") => Some(FunctionRole::PushMethod { type_arg_count }),
        s if s.ends_with("::add") && (s.contains("Seq") || s.contains("Map")) => {
            Some(FunctionRole::AddOp { type_arg_count })
        }
        s if s.ends_with("::contains") && s.contains("Set") => {
            Some(FunctionRole::ContainsKeyOp { type_arg_count })
        }
        s if s.ends_with("::subrange") && s.contains("Seq") => {
            Some(FunctionRole::SubrangeOp { type_arg_count })
        }
        _ => None,
    };

    let role = if let Some(r) = special_role {
        r
    } else {
        // `print_as_method` is Verus's own signal for `x.f()` call syntax (see
        // `FunctionAttrs::print_as_method` and vir's `to_user_string`). It is true only when
        // the function actually takes a `self` receiver, so a trait *associated* function
        // (no `self`) correctly renders as `Trait::f(x)` rather than `x.f()`.
        let is_method = func.x.attrs.print_as_method;
        FunctionRole::UserDefined { type_arg_count, is_method }
    };

    fr.insert(air_name, role.clone());
    fr.insert(air_name_q, role);
}

/// Marks an impl-block path segment. `vir::def` generates these as
/// `impl&%<disambiguator>` (`vir::def::impl_ident`), but its prefix constant is private,
/// so the shared `impl&` portion is matched here.
const AIR_IMPL_IDENT_SUBSTR: &str = "impl&%";

/// Resolve the friendly Rust name for a function, handling impl-block paths.
fn resolve_friendly_name(func: &vir::ast::Function) -> String {
    let raw = fun_as_friendly_rust_name(&func.x.name);
    if !raw.contains(AIR_IMPL_IDENT_SUBSTR) {
        return raw;
    }
    let type_name = func
        .x
        .owning_module
        .as_ref()
        .and_then(|m| {
            let s = path_as_friendly_rust_name(m);
            if s.split("::")
                .last()
                .and_then(|seg| seg.chars().next())
                .map(|c| c.is_uppercase())
                .unwrap_or(false)
            {
                Some(s)
            } else {
                None
            }
        })
        .or_else(|| {
            if let vir::ast::TypX::Datatype(Dt::Path(ret_path), _, _) = &*func.x.ret.x.typ {
                Some(path_as_friendly_rust_name(ret_path))
            } else {
                None
            }
        })
        .or_else(|| {
            func.x.params.first().and_then(|p| {
                if let vir::ast::TypX::Datatype(Dt::Path(path), _, _) = &*p.x.typ {
                    Some(path_as_friendly_rust_name(path))
                } else {
                    None
                }
            })
        })
        .unwrap_or_default();
    let method = func.x.name.path.segments.last().map(|s| s.as_str()).unwrap_or("");
    if !type_name.is_empty() && !method.is_empty() {
        format!("{}::{}", type_name, method)
    } else {
        raw
    }
}

/// Register a single datatype's field accessors, constructors, and discriminants.
fn register_datatype(
    dt: &vir::ast::Datatype,
    name_ctxt: &NameCtxt,
    fr: &mut HashMap<Ident, FunctionRole>,
    friendly_names: &mut HashMap<Ident, String>,
    dt_fields: &mut HashMap<Ident, String>,
    field_update_names: &mut HashMap<Ident, String>,
) {
    let Dt::Path(path) = &dt.x.name else { return };
    let air_string = name_ctxt.path_to_string(path);
    let dt_friendly = path_as_friendly_rust_name(path);
    let type_name = dt_friendly.rsplit("::").next().unwrap_or(&dt_friendly).to_string();
    friendly_names.insert(Arc::new(air_string.clone()), dt_friendly);

    for variant in dt.x.variants.iter() {
        // Variant discriminant
        let disc_name = name_ctxt.is_variant_ident(&dt.x.name, &variant.name);
        fr.insert(
            disc_name,
            FunctionRole::VariantDiscriminant {
                type_name: type_name.clone(),
                variant_name: variant.name.to_string(),
            },
        );

        // Variant constructor
        let ctor_name = name_ctxt.variant_ident(&dt.x.name, &variant.name);
        let field_names: Vec<String> = variant.fields.iter().map(|f| f.name.to_string()).collect();
        // AIR field-accessor names, parallel to field_names (for X == Ctor{..}
        // decomposition). Matches the accessor keys registered below.
        let field_accessors: Vec<String> = variant
            .fields
            .iter()
            .map(|f| format!("{}/{}/{}", air_string, variant.name, f.name))
            .collect();
        // Single-variant datatype whose variant is named after the type is a
        // Rust struct — render idiomatically as `Type { .. }` / `Type(..)`
        // rather than the enum-style `Type::Variant`.
        let is_struct = dt.x.variants.len() == 1 && variant.name.to_string() == type_name;
        let ctor_role = FunctionRole::VariantConstructor {
            variant_name: variant.name.to_string(),
            field_names,
            type_arg_count: 0,
            is_struct,
            field_accessors,
        };
        let no_crate_ctor = if let Some(pos) = ctor_name.as_str().find('!') {
            Arc::new(ctor_name.as_str()[pos + 1..].to_string())
        } else {
            ctor_name.clone()
        };
        fr.insert(ctor_name.clone(), ctor_role.clone());
        fr.insert(no_crate_ctor, ctor_role);
        let ctor_friendly = format!("{}::{}", type_name, variant.name);
        friendly_names.insert(name_ctxt.variant_ident(&dt.x.name, &variant.name), ctor_friendly);

        // Field accessors
        for field in variant.fields.iter() {
            let base_key = format!("{}/{}/{}", air_string, variant.name, field.name);
            let field_name = field.name.to_string();
            // DECORATE=true: each type param contributes Dcr + Type = 2 args
            // But only when num_variants >= 2 (has_field_typ_args guard)
            let type_arg_count = if dt.x.variants.len() >= 2 {
                dt.x.typ_params.len() * 2 // Dcr + Type per param
            } else {
                0
            };

            // FieldUpdate ident
            let fu_key = name_ctxt.variant_field_ident_internal(
                &encode_dt_as_path(&dt.x.name),
                &variant.name,
                &field.name,
                true,
            );
            field_update_names.insert(fu_key, field_name.clone());

            let no_crate = if let Some(pos) = base_key.find(SUFFIX_PARAM_CHAR) {
                base_key[pos + 1..].to_string()
            } else {
                base_key.clone()
            };
            for key in [
                base_key.clone(),
                format!("{}{}", base_key, SUFFIX_GLOBAL),
                no_crate.clone(),
                format!("{}{}", no_crate, SUFFIX_GLOBAL),
            ] {
                dt_fields.insert(Arc::new(key.clone()), field_name.clone());
                fr.insert(Arc::new(key), FunctionRole::FieldAccessor { type_arg_count });
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn builtin_roles_are_classified() {
        // The builtin table is pure (no krate needed) — audit the taxonomy.
        let mut fr: HashMap<Ident, FunctionRole> = HashMap::new();
        register_builtin_roles(&mut fr);
        let role = |n: &str| fr.get(&Arc::new(n.to_string())).cloned();

        // Coercions.
        assert_eq!(role("as_type"), Some(FunctionRole::IntCoerce));
        // insert_role registers both plain and %-prefixed keys.
        assert_eq!(role("%as_type"), Some(FunctionRole::IntCoerce));

        // Explicit bookkeeping roles (formerly the generic `Noise` bucket).
        assert_eq!(role(HAS_TYPE), Some(FunctionRole::TypeGuard));
        assert_eq!(role(SIZED_BOUND), Some(FunctionRole::TypeGuard));
        assert_eq!(role("fuel_bool"), Some(FunctionRole::Fuel));
        assert_eq!(role("uHi"), Some(FunctionRole::RangeInvariant));
        assert_eq!(role("height"), Some(FunctionRole::RecursionHeight));
        assert_eq!(role("const_bool"), Some(FunctionRole::SolverInternal));
        // …all report as bookkeeping.
        assert!(role(HAS_TYPE).unwrap().is_bookkeeping());
        assert!(role("fuel_bool").unwrap().is_bookkeeping());

        // Real ops previously MASKED as Noise are now promoted to faithful roles.
        assert_eq!(role(STRSLICE_LEN), Some(FunctionRole::LenMethod { type_arg_count: 0 }));
        assert_eq!(role(STRSLICE_GET_CHAR), Some(FunctionRole::IndexOp { type_arg_count: 0 }));
        assert_eq!(role("array_index"), Some(FunctionRole::IndexOp { type_arg_count: 0 }));
        assert_eq!(
            role("array_new"),
            Some(FunctionRole::UserDefined { type_arg_count: 0, is_method: false })
        );
        // …and they are NOT bookkeeping (won't be filtered).
        assert!(!role(STRSLICE_LEN).unwrap().is_bookkeeping());
        assert!(!role("array_index").unwrap().is_bookkeeping());
    }
}
