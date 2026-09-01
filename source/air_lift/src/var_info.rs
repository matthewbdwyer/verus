//! Classification of AIR variable occurrences for source-level lifting.
//!
//! Ported from air::var_to_const — only the classification logic,
//! not the lowering/renaming passes.

use std::collections::{HashMap, HashSet};
use std::sync::Arc;

use air::ast::{Axiom, BindX, DeclX, Expr, ExprX, Ident, Query, Snapshots, Stmt, StmtX};
use indexmap::IndexMap;

use crate::air_names::*;
use crate::types::{IntermediateKind, SpanKind, VarInfo};

/// Parse a versioned AIR name like `"x@3"` into `("x@", Some(3))`.
/// Returns `(name, None)` if no version suffix is present.
pub fn parse_versioned(name: &str) -> (&str, Option<u32>) {
    if let Some(at) = name.rfind(SUFFIX_LOCAL_STMT_CHAR)
        && let Ok(n) = name[at + 1..].parse::<u32>()
    {
        return (&name[..at + 1], Some(n));
    }
    (name, None)
}

/// Strip version suffix to get the base with trailing `@`.
/// E.g., `"x@3"` → `"x@"`, `"result@0"` → `"result@"`.
pub fn strip_to_base_with_at(name: &str) -> &str {
    parse_versioned(name).0
}

/// Strip all known AIR suffixes to recover the user-visible clean name.
fn strip_air_suffixes(s: &str) -> &str {
    // A type parameter / const generic carries a trailing `&` (vir's SUFFIX_TYPE_PARAM):
    // `N&` -> `N`.
    let s = s.strip_suffix(SUFFIX_TYPE_PARAM).unwrap_or(s);
    let s = s.strip_suffix(SUFFIX_LOCAL_STMT).unwrap_or(s);
    let s = s.strip_suffix(SUFFIX_PARAM).unwrap_or(s);
    let s = s.strip_suffix(SUFFIX_GLOBAL).unwrap_or(s);
    if let Some(pos) = s.rfind(SUFFIX_LOCAL_EXPR) {
        let suffix = &s[pos + 1..];
        if suffix.chars().all(|c| c.is_ascii_digit()) {
            let base = &s[..pos];
            return base
                .strip_suffix(SUFFIX_PARAM)
                .or_else(|| base.strip_suffix(SUFFIX_GLOBAL))
                .unwrap_or(base);
        }
    }
    s
}

/// Solver-internal temporaries: tmp%N, decrease%init, verus_tmp, %%hole%%
fn is_temporary(s: &str) -> bool {
    matches!(AirName::parse(s), AirName::TmpVar(_) | AirName::DecreaseInit)
        || s.starts_with(VERUS_TMP_PREFIX)
        || s.starts_with(HOLE)
        || s.starts_with(EXPAND_PREFIX)
        || s.starts_with(CLOSURE_RETURN_PREFIX)
}

/// Solver-internal noise: switch/location labels, fuel_defaults, type artifacts,
/// closure/impl type params, fuel versioned vars
fn is_noise(s: &str) -> bool {
    is_solver_noise(s)
        || s.starts_with(CLOSURE_PREFIX)
        || s.starts_with(IMPL_PREFIX)
        || s.starts_with(PREFIX_FUEL)
}

/// If `s` has a versioned counterpart in `versions`, return the clean name for Old.
fn find_versioned_counterpart<'a>(s: &'a str, versions: &IndexMap<Ident, u32>) -> Option<&'a str> {
    let key = Arc::new(format!("{}{}", s, SUFFIX_LOCAL_STMT));
    if versions.contains_key(&key) { Some(strip_air_suffixes(s)) } else { None }
}

/// Look up a line number for a versioned variable from all available sources.
///
/// The span_map is keyed by the **unversioned** AIR name (e.g. "sum@") produced by
/// `suffix_local_unique_id` in the observer callbacks. The versioned name (e.g. "sum@0")
/// is produced by `var_to_const`. Multiple key formats are tried to find a match.
fn lookup_span(
    versioned_name: &Ident,
    base_with_at: &str,
    span_map: &HashMap<Ident, (u32, SpanKind)>,
    variable_def_lines: &HashMap<Ident, u32>,
) -> Option<(u32, SpanKind)> {
    let base_key = Arc::new(base_with_at.to_string());
    // Try the versioned name directly (versioned span_map entries from on_wp_version_created)
    if let Some(&entry) = span_map.get(versioned_name) {
        return Some(entry);
    }
    // Try the unversioned base name — but NOT for expression-local binders
    let base_no_at = base_with_at.strip_suffix('@').unwrap_or(base_with_at);
    if !base_no_at.contains('$')
        && let Some(&entry) = span_map.get(&base_key)
    {
        return Some(entry);
    }
    // Fallback to variable_def_lines
    if let Some(&line) = variable_def_lines.get(versioned_name) {
        return Some((line, SpanKind::Other));
    }
    if let Some(&line) = variable_def_lines.get(&base_key) {
        return Some((line, SpanKind::Other));
    }
    None
}

/// Build a variable classification map from a query and observer-collected metadata.
///
/// `span_map` maps versioned variable names to `(line, SpanKind)` — populated by
/// the observer's lowering callbacks (Havoc, Assign, Switch merge, Breakable merge).
///
/// `binder_lines` and `variable_def_lines` provide additional line info from the observer.
pub fn build_var_info(
    query: &Query,
    _snapshots: &Snapshots,
    span_map: &HashMap<Ident, (u32, SpanKind)>,
    binder_lines: &HashMap<Ident, u32>,
    variable_def_lines: &HashMap<Ident, u32>,
) -> HashMap<Ident, VarInfo> {
    // Compute max version for each raw base name (e.g. "x@", "x$1@", "x$2@").
    // Also track the globally latest versioned name per clean name so that only
    // one variable per user-visible name is classified as Current.
    let mut versions: IndexMap<Ident, u32> = IndexMap::new();
    // Map from clean name → (raw_base_key, max_global_version)
    // where max_global_version is the sum of all versions across raw bases
    // to determine which raw base holds the "latest" value.
    let mut latest_per_clean: HashMap<String, (Ident, u32)> = HashMap::new();
    for decl in query.local.iter() {
        let name = match &**decl {
            DeclX::Const(name, _) => name,
            _ => continue,
        };
        let (base, version) = parse_versioned(name.as_str());
        if let Some(v) = version {
            let raw = &base[..base.len() - 1]; // strip trailing '@'
            let clean = strip_air_suffixes(raw);
            // Track per raw base
            let raw_key = Arc::new(base.to_string());
            let entry = versions.entry(raw_key.clone()).or_insert(0);
            *entry = (*entry).max(v + 1);
            // Track global latest per clean name: the raw base with the highest
            // version seen is the "latest" (Current).
            let global_entry =
                latest_per_clean.entry(clean.to_string()).or_insert((raw_key.clone(), 0));
            if v + 1 > global_entry.1 || (v + 1 == global_entry.1 && raw_key > global_entry.0) {
                *global_entry = (raw_key, v + 1);
            }
        }
    }

    let mut info: HashMap<Ident, VarInfo> = HashMap::new();

    if tracing::enabled!(tracing::Level::DEBUG) {
        for (k, v) in span_map.iter() {
            tracing::debug!(
                "[var-class] span_map[{}] = (line={}, is_loop={})",
                k,
                v.0,
                v.1.is_loop()
            );
        }
        for (k, v) in versions.iter() {
            tracing::debug!("[var-class] versions[{}] = {}", k, v);
        }
    }

    for decl in query.local.iter() {
        let name = match &**decl {
            DeclX::Const(name, _) => name,
            _ => continue,
        };
        let s = name.as_str();

        // VERUS_ loop machinery — skip
        if VERUS_LOOP_VARS.iter().any(|p| s.starts_with(p)) {
            continue;
        }

        let vi = if is_temporary(s) {
            VarInfo::Temporary
        } else if is_noise(s) {
            VarInfo::Noise
        } else if s.starts_with(RETURN_VALUE) {
            VarInfo::Current { clean_name: RETURN_CLEAN_NAME.to_string() }
        } else if let (base_with_at, Some(v)) = parse_versioned(s) {
            // Versioned variable (base@N)
            let base = &base_with_at[..base_with_at.len() - 1];
            let is_param = base.ends_with(SUFFIX_PARAM);
            let clean = strip_air_suffixes(base);
            let raw_key = Arc::new(base_with_at.to_string());
            if let Some(&max_v) = versions.get(&raw_key) {
                // Check if this is the globally latest version for this clean name
                let is_current = v == max_v - 1
                    && latest_per_clean.get(clean).map(|(k, _)| k == &raw_key).unwrap_or(false);
                if is_current {
                    VarInfo::Current { clean_name: clean.to_string() }
                } else if is_param && v == 0 {
                    VarInfo::Old { clean_name: clean.to_string() }
                } else if let Some((line, span_kind)) =
                    lookup_span(name, base_with_at, span_map, variable_def_lines)
                {
                    let kind = if span_kind.is_loop() {
                        IntermediateKind::Loop
                    } else {
                        IntermediateKind::Merge
                    };
                    VarInfo::Intermediate { clean_name: clean.to_string(), line, kind }
                } else {
                    // Check binder_lines for the base name (handles Skolemized
                    // variables like i$1@0 where the binder line is known).
                    // Strip $N renumbering suffix: i$1 → i$
                    let base_key: Ident = Arc::new(base_with_at.to_string());
                    let base_no_at = base_with_at.strip_suffix('@').unwrap_or(base_with_at);
                    let base_bare: Ident = Arc::new(base_no_at.to_string());
                    let base_stripped = if let Some(pos) = base_no_at.rfind('$') {
                        let after = &base_no_at[pos + 1..];
                        if !after.is_empty() && after.chars().all(|c| c.is_ascii_digit()) {
                            Arc::new(format!("{}$", &base_no_at[..pos]))
                        } else {
                            base_bare.clone()
                        }
                    } else {
                        base_bare.clone()
                    };
                    if let Some(&line) = binder_lines
                        .get(&base_key)
                        .or_else(|| binder_lines.get(&base_bare))
                        .or_else(|| binder_lines.get(&base_stripped))
                    {
                        VarInfo::Intermediate {
                            clean_name: clean.to_string(),
                            line,
                            kind: IntermediateKind::QuantBinder,
                        }
                    } else if let Some(pos) = base_no_at.rfind('$') {
                        // $N suffix fallback: use N as line proxy
                        let after = &base_no_at[pos + 1..];
                        if !after.is_empty() && after.chars().all(|c| c.is_ascii_digit()) {
                            VarInfo::Intermediate {
                                clean_name: clean.to_string(),
                                line: after.parse().unwrap_or(0),
                                kind: IntermediateKind::QuantBinder,
                            }
                        } else {
                            VarInfo::Intermediate {
                                clean_name: clean.to_string(),
                                line: v,
                                kind: IntermediateKind::Mutation,
                            }
                        }
                    } else {
                        VarInfo::Intermediate {
                            clean_name: clean.to_string(),
                            line: v,
                            kind: IntermediateKind::Mutation,
                        }
                    }
                }
            } else {
                continue;
            }
        } else if let Some(clean) = find_versioned_counterpart(s, &versions) {
            VarInfo::Old { clean_name: clean.to_string() }
        } else {
            let clean = strip_air_suffixes(s);
            VarInfo::Current { clean_name: clean.to_string() }
        };

        info.insert(name.clone(), vi.clone());
        tracing::debug!(var = s, classification = ?vi, "var-class result");
    }

    // Classify DeclX::Var temporaries (tmp%N, verus_tmp) not in DeclX::Const.
    for decl in query.local.iter() {
        let name = match &**decl {
            DeclX::Var(name, _) => name,
            _ => continue,
        };
        if is_temporary(name.as_str()) {
            info.entry(name.clone()).or_insert(VarInfo::Temporary);
        }
    }

    // Classify free Var nodes in the assertion and local axioms that aren't in query.local.
    classify_free_stmt_vars(&query.assertion, &mut info);
    for decl in query.local.iter() {
        if let DeclX::Axiom(Axiom { expr, .. }) = &**decl {
            classify_free_vars_in_expr(expr, &mut info);
        }
    }

    // TRACE: dump all entries (post-disambiguation)
    for (name, vi) in info.iter() {
        tracing::debug!(%name, ?vi, "build_var_info final");
    }

    info
}

/// Classify free Var nodes in a statement tree.
fn classify_free_stmt_vars(stmt: &Stmt, info: &mut HashMap<Ident, VarInfo>) {
    match &**stmt {
        StmtX::Assume(e) | StmtX::Assert(_, _, _, e) => classify_free_vars_in_expr(e, info),
        StmtX::Havoc(_) | StmtX::Assign(_, _) | StmtX::Snapshot(_) | StmtX::Break(_) => {}
        StmtX::Block(stmts) | StmtX::Switch(stmts) => {
            for s in stmts.iter() {
                classify_free_stmt_vars(s, info);
            }
        }
        StmtX::DeadEnd(s) | StmtX::Breakable(_, s) => classify_free_stmt_vars(s, info),
    }
}

/// Classify binder names in a variable info map.
pub fn register_binder_name(name: &Ident, info: &mut HashMap<Ident, VarInfo>) {
    let s = name.as_str();
    if matches!(AirName::parse(s), AirName::TmpVar(_)) || s.starts_with(HOLE) {
        info.entry(name.clone()).or_insert(VarInfo::Temporary);
        return;
    }
    if let Some(dollar_pos) = s.rfind(SUFFIX_LOCAL_EXPR) {
        let suffix = &s[dollar_pos + 1..];
        if suffix.chars().all(|c: char| c.is_ascii_digit()) {
            let clean = s[..dollar_pos].trim_end_matches(AIR_SUFFIX_CHARS).to_string();
            if !clean.is_empty() {
                let vi = VarInfo::Current { clean_name: clean };
                // Insert if not already classified (don't override disambiguation)
                info.entry(name.clone()).or_insert(vi.clone());
                // Also register versioned forms that may appear in the expression
                let with_at = Arc::new(format!("{}@", s));
                info.entry(with_at.clone()).or_insert(vi.clone());
                let with_at0 = Arc::new(format!("{}@0", s));
                info.entry(with_at0).or_insert(vi.clone());
            }
        }
    }
}

/// Classify free Var nodes and binder names in an expression.
pub fn classify_free_vars_in_expr(expr: &Expr, info: &mut HashMap<Ident, VarInfo>) {
    match &**expr {
        ExprX::Var(name) if !info.contains_key(name) => {
            let s = name.as_str();
            if matches!(AirName::parse(s), AirName::TmpVar(_))
                || s.starts_with(HOLE)
                || s.contains(AIR_POLY_PREFIX)
            {
                return;
            }
            if is_solver_noise(s) {
                info.insert(name.clone(), VarInfo::Noise);
                return;
            }
            let (base_with_at, version) = parse_versioned(s);
            let base = if version.is_some() {
                let b = &base_with_at[..base_with_at.len() - 1];
                b.strip_suffix(SUFFIX_PARAM)
                    .or_else(|| b.strip_suffix(SUFFIX_GLOBAL))
                    .or_else(|| b.strip_suffix(SUFFIX_LOCAL_STMT_CHAR).map(|s| s as &str))
                    .unwrap_or(b)
            } else {
                ""
            };
            let clean = if !base.is_empty() {
                Some(base)
            } else {
                s.strip_suffix(SUFFIX_LOCAL_STMT_CHAR)
                    .map(|s| s as &str)
                    .or_else(|| s.strip_suffix(SUFFIX_PARAM))
                    .or_else(|| s.strip_suffix(SUFFIX_GLOBAL))
                    .or_else(|| {
                        if let Some(dollar_pos) = s.rfind(SUFFIX_LOCAL_EXPR) {
                            let suffix = &s[dollar_pos + 1..];
                            if suffix.chars().all(|c| c.is_ascii_digit()) {
                                return Some(s[..dollar_pos].trim_end_matches(AIR_SUFFIX_CHARS));
                            }
                        }
                        None
                    })
            };
            if let Some(clean) = clean
                && !clean.is_empty()
            {
                if let Some(v) = version {
                    info.insert(
                        name.clone(),
                        VarInfo::Intermediate {
                            clean_name: clean.to_string(),
                            line: v,
                            kind: IntermediateKind::Mutation,
                        },
                    );
                } else {
                    info.insert(name.clone(), VarInfo::Current { clean_name: clean.to_string() });
                }
            }
        }
        ExprX::Apply(_, args) | ExprX::Multi(_, args) | ExprX::Array(args) => {
            for a in args.iter() {
                classify_free_vars_in_expr(a, info);
            }
        }
        ExprX::Unary(_, e) => classify_free_vars_in_expr(e, info),
        ExprX::Binary(_, l, r) => {
            classify_free_vars_in_expr(l, info);
            classify_free_vars_in_expr(r, info);
        }
        ExprX::IfElse(c, t, e) => {
            classify_free_vars_in_expr(c, info);
            classify_free_vars_in_expr(t, info);
            classify_free_vars_in_expr(e, info);
        }
        ExprX::Bind(bind, body) => {
            match &**bind {
                BindX::Let(bs) => {
                    for b in bs.iter() {
                        register_binder_name(&b.name, info);
                    }
                }
                BindX::Quant(_, bs, _, _) | BindX::Lambda(bs, _, _) => {
                    for b in bs.iter() {
                        register_binder_name(&b.name, info);
                    }
                }
                BindX::Choose(bs, _, _, cond) => {
                    for b in bs.iter() {
                        register_binder_name(&b.name, info);
                    }
                    classify_free_vars_in_expr(cond, info);
                }
            }
            classify_free_vars_in_expr(body, info);
        }
        ExprX::LabeledAxiom(_, _, inner) | ExprX::LabeledAssertion(_, _, _, inner) => {
            classify_free_vars_in_expr(inner, info);
        }
        _ => {}
    }
}

/// Disambiguate variables that share a clean name but have different AIR base names.
/// Ported from VerusVerifier's context.rs disambiguation pass.
/// Runs AFTER build_var_info and classify_free_vars_in_expr, so all entries are present.
pub fn disambiguate_var_info(
    info: &mut HashMap<Ident, VarInfo>,
    variable_def_lines: &HashMap<Ident, u32>,
    binder_lines: &HashMap<Ident, u32>,
    binder_decl_names: &HashSet<Ident>,
) {
    let def_lines_get = |key: &Ident| -> Option<&u32> {
        variable_def_lines.get(key).or_else(|| binder_lines.get(key))
    };

    // Group variables by (clean_name → set of base names)
    let mut clean_to_bases: HashMap<String, HashSet<String>> = HashMap::new();
    for (air_name, vi) in info.iter() {
        let clean = match vi {
            VarInfo::Current { clean_name }
            | VarInfo::Old { clean_name }
            | VarInfo::Intermediate { clean_name, .. } => clean_name.clone(),
            _ => continue,
        };
        // Skip already-disambiguated names (contain @return or @digit)
        if clean.contains('@') {
            continue;
        }
        let base = air_name.split('@').next().unwrap_or(air_name.as_str()).to_string();
        clean_to_bases.entry(clean).or_default().insert(base);
    }

    // For clean names with multiple DIFFERENT bases, disambiguate
    let colliding_cleans: HashSet<String> = clean_to_bases
        .into_iter()
        .filter(|(_, bases)| bases.len() > 1)
        .map(|(clean, _)| clean)
        .collect();

    if colliding_cleans.is_empty() {
        return;
    }
    let dl_keys: Vec<_> = variable_def_lines
        .keys()
        .chain(binder_lines.keys())
        .filter(|k| !k.contains("tmp") && !k.contains("fuel") && !k.contains("%%"))
        .map(|k| k.as_str())
        .collect();
    tracing::debug!(?colliding_cleans, ?dl_keys, "DISAMBIG_ENTRY");

    // Pre-pass: build a map from Skolemized AIR names to binder lines.
    // Replicates VerusVerifier's prefix-matching logic in sst_to_air.rs.
    // For each $N-suffixed entry (e.g., "i$1@0"), find the binder line by
    // searching binder_lines for keys starting with the same prefix ("i$"),
    // using assigned_lines to avoid reusing the same line.
    let mut skolem_lines: HashMap<String, u32> = HashMap::new();
    {
        // Use binder_decl_names (from on_quantifier_binder_decl) to know
        // which Skolemized copies exist. Sort by $N suffix for consistent
        // line assignment order.
        let mut skolem_bases: Vec<(String, u32)> = Vec::new();
        for decl_name in binder_decl_names.iter() {
            let base = decl_name.split('@').next().unwrap_or(decl_name.as_str());
            if let Some(pos) = base.rfind('$') {
                let after = &base[pos + 1..];
                if !after.is_empty() && after.chars().all(|c| c.is_ascii_digit()) {
                    let n: u32 = after.parse().unwrap_or(0);
                    skolem_bases.push((base.to_string(), n));
                }
            }
        }
        skolem_bases.sort_by_key(|(_, n)| *n);

        let mut assigned_lines: HashSet<u32> = HashSet::new();
        for (base, _n) in &skolem_bases {
            let prefix = if let Some(pos) = base.rfind('$') {
                format!("{}$", &base[..pos])
            } else {
                continue;
            };
            // Search binder_lines for keys starting with prefix, pick first unassigned
            // Only use prefix matching when there are multiple binder_lines entries
            // for this prefix (indicating multiple binders with the same name).
            // When there's only one, the $N fallback gives the correct line.
            let prefix_matches: Vec<_> =
                binder_lines.iter().filter(|(k, _)| k.starts_with(&prefix)).collect();
            // Check if the original binder (prefix itself) is in info —
            // if so, it will consume the line via the main lookup chain,
            // and this Skolemized copy should use the $N fallback instead.
            let _original_in_info = info.contains_key(&Arc::new(prefix.clone()) as &Ident)
                || info.contains_key(&Arc::new(format!("{}@", prefix)) as &Ident);
            let line = if !prefix_matches.is_empty() {
                prefix_matches.iter().find(|(_, l)| !assigned_lines.contains(l)).map(|(_, l)| **l)
            } else {
                None
            };
            if let Some(line) = line {
                assigned_lines.insert(line);
                skolem_lines.insert(base.clone(), line);
            }
        }
    }

    let updates: Vec<(Ident, VarInfo)> = info
        .iter()
        .filter_map(|(air_name, vi)| {
            let clean = match vi {
                VarInfo::Current { clean_name }
                | VarInfo::Old { clean_name }
                | VarInfo::Intermediate { clean_name, .. } => clean_name.clone(),
                _ => return None,
            };
            if !colliding_cleans.contains(&clean) {
                return None;
            }
            let base = air_name.split('@').next().unwrap_or(air_name.as_str());
            let base_id = Arc::new(format!("{}@", base));
            let base_bare = Arc::new(base.to_string());
            let base_dollar = Arc::new(format!("{}$", base));
            // Also try $N-stripped form: "i$1" → "i$"
            let _base_stripped_dollar: Option<Ident> = if let Some(pos) = base.rfind('$') {
                let after = &base[pos + 1..];
                if !after.is_empty() && after.chars().all(|c| c.is_ascii_digit()) {
                    Some(Arc::new(format!("{}$", &base[..pos])))
                } else {
                    None
                }
            } else {
                None
            };
            let found = def_lines_get(&base_id)
                .or_else(|| def_lines_get(&base_bare))
                .or_else(|| def_lines_get(&base_dollar))
                .or_else(|| def_lines_get(air_name))
                .or_else(|| skolem_lines.get(base));
            tracing::debug!(
                air_name = %air_name, base = %base,
                base_id = %base_id, base_dollar = %base_dollar,
                found = ?found,
                "DISAMBIG_LOOKUP"
            );
            if let Some(&line) = found {
                // Check if this is a quantifier binder
                let is_binder = binder_lines.contains_key(air_name)
                    || binder_lines.contains_key(&base_id)
                    || binder_lines.contains_key(&base_bare)
                    || binder_lines.contains_key(&base_dollar)
                    || skolem_lines.contains_key(base);
                if is_binder {
                    Some((
                        air_name.clone(),
                        VarInfo::Intermediate {
                            clean_name: clean,
                            line,
                            kind: IntermediateKind::QuantBinder,
                        },
                    ))
                } else {
                    let is_param = base.contains(crate::air_names::SUFFIX_PARAM_CHAR);
                    match vi {
                        VarInfo::Intermediate { .. } | VarInfo::Old { .. } => None,
                        VarInfo::Current { .. } => {
                            if is_param {
                                // Return binding with known line — disambiguate
                                let new_clean = format!("{}@{}", clean, line);
                                Some((air_name.clone(), VarInfo::Current { clean_name: new_clean }))
                            } else {
                                // Check if all other colliding Current entries are params.
                                let needs_disambiguation = info.iter().any(|(other_name, other_vi)| {
                                    if other_name == air_name { return false; }
                                    let other_clean = match other_vi {
                                        VarInfo::Current { clean_name } => clean_name.as_str(),
                                        _ => return false,
                                    };
                                    other_clean == clean
                                        && !other_name.contains(crate::air_names::SUFFIX_PARAM_CHAR)
                                });
                                if needs_disambiguation {
                                    let new_clean = format!("{}@{}", clean, line);
                                    Some((air_name.clone(), VarInfo::Current { clean_name: new_clean }))
                                } else {
                                    None
                                }
                            }
                        }
                        _ => None,
                    }
                }
            } else {
                // No def_lines entry.
                let is_param = base.contains(crate::air_names::SUFFIX_PARAM_CHAR);
                if is_param {
                    return None; // param never co-occurs with local in the same query
                }
                // Check for $N suffix (quantifier binder)
                if let Some(pos) = base.rfind('$') {
                    let after = &base[pos + 1..];
                    if !after.is_empty() && after.chars().all(|c| c.is_ascii_digit()) {
                        let line = skolem_lines
                            .get(base)
                            .copied()
                            .unwrap_or_else(|| after.parse().unwrap_or(0));
                        return Some((
                            air_name.clone(),
                            VarInfo::Intermediate {
                                clean_name: clean,
                                line,
                                kind: IntermediateKind::QuantBinder,
                            },
                        ));
                    }
                }
                None
            }
        })
        .collect();

    for (name, new_vi) in updates {
        info.insert(name, new_vi);
    }
}
