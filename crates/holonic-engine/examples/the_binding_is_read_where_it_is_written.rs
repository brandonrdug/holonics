//! The orbit instrument for the reader repair, and it is run **before** the repair so the repair
//! has something to move.
//!
//! `blueprint/THE_TYPED_TRANSPORT_ATLAS.md` names four defects in
//! [`crate::lean_development`], each with a measured population, and makes the movement's
//! completion conditional on exhibiting what changed. A repair wave that reports no movement has
//! done bookkeeping, and this driver is what makes that statement checkable rather than a promise.
//!
//! Every population below is a **reader return** over the whole library, not a regex estimate.
//!
//! ```text
//! cargo run --release -p holonic-engine --example the_binding_is_read_where_it_is_written
//! ```
//!
//! # What each row is, and which repair owns it
//!
//! - **empty recruitment** — a destructuring cohort's recruitment reaches only its last binder, so
//!   the others carry nothing. A step with an empty map can never be the *target* of an arrival, so
//!   this population is missing arrival edges by construction. Owned by *a cohort shares its
//!   recruitment*.
//! - **statement opens with `with`** — a `with`-form tactic takes the **scrutinee** as its binder and
//!   the `with` clause as its statement, on a tactic that carries no ascription at all. Owned by
//!   *`with` is a cut, not a pattern*.
//! - **line does not carry its own former** — `ProofStep::line` is derived by adding an offset into a
//!   filtered line vector to the declaration's start, which assumes a contiguity the material does
//!   not have. Owned by *`line` is the true source line*.
//! - **statement is bracket-unbalanced** — the binder pattern is cut at the first `:` regardless of
//!   depth, so a binder carrying its own parameters cuts inside the parameter group. Owned by *the
//!   binder pattern respects bracket depth*.
//! - **declared names sunk into `local_bindings`** — the `with` cut also runs in `founded_names`, so
//!   a scrutinee's head symbol is founded and its uses land in `local_bindings` instead of
//!   `recruited`. When that symbol is a declaration the library itself makes, a real
//!   declaration-to-declaration edge has been deleted.

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use holonic_engine::lean_development::{
    BinderGrain, DeclarationGrain, DeclaredForm, read_development_at,
};
use holonic_engine::move_species::{MoveComplex, MoveOccurrence};

const GEOMETRY: &str = "Mathlib/Geometry/Euclidean/Triangle.lean";

fn repository_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("the crate sits two levels under the repository root")
        .to_path_buf()
}

fn material_root(root: &Path) -> PathBuf {
    root.join("soma/formal/elementary-holonics/.lake/packages/mathlib")
}

fn balanced(text: &str) -> bool {
    let mut round = 0i64;
    let mut curly = 0i64;
    let mut square = 0i64;
    for character in text.chars() {
        match character {
            '(' => round += 1,
            ')' => round -= 1,
            '{' => curly += 1,
            '}' => curly -= 1,
            '[' => square += 1,
            ']' => square -= 1,
            _ => {}
        }
        if round < 0 || curly < 0 || square < 0 {
            return false;
        }
    }
    round == 0 && curly == 0 && square == 0
}

#[derive(Default)]
struct Census {
    files: usize,
    declarations: usize,
    steps: usize,
    empty_recruitment: usize,
    in_multi_binder_cohort: usize,
    statement_opens_with_with: usize,
    line_misses_its_former: usize,
    statement_unbalanced: usize,
    statement_empty: usize,
}

fn census_of(form: &DeclaredForm, lines: &[&str], census: &mut Census) {
    let mut cohort_extent: BTreeMap<usize, usize> = BTreeMap::new();
    for step in &form.steps {
        *cohort_extent.entry(step.cohort).or_insert(0) += 1;
    }
    for step in &form.steps {
        census.steps += 1;
        if step.recruited.is_empty() {
            census.empty_recruitment += 1;
        }
        if cohort_extent.get(&step.cohort).copied().unwrap_or(0) > 1 {
            census.in_multi_binder_cohort += 1;
        }
        let statement = step.statement.trim();
        if statement.is_empty() {
            census.statement_empty += 1;
        } else {
            if statement.starts_with("with") {
                census.statement_opens_with_with += 1;
            }
            if !balanced(statement) {
                census.statement_unbalanced += 1;
            }
        }
        // The line the reader recorded must carry the former that founded the step.
        let carries = step
            .line
            .checked_sub(1)
            .and_then(|index| lines.get(index))
            .is_some_and(|line| {
                line.trim_start_matches([' ', '\t', '·', '.'])
                    .starts_with(&step.former)
            });
        if !carries {
            census.line_misses_its_former += 1;
        }
    }
}

fn main() {
    let root = repository_root();
    let material = material_root(&root);
    println!("THE BINDING IS READ WHERE IT IS WRITTEN — the orbit instrument");
    println!("  material {}", material.display());
    if !material.exists() {
        println!("  the library is not materialised here.");
        println!("  recover it with:  cd soma/formal/elementary-holonics && lake exe cache get");
        std::process::exit(2);
    }

    let mut paths: Vec<PathBuf> = Vec::new();
    let mut stack = vec![material.join("Mathlib")];
    while let Some(directory) = stack.pop() {
        let Ok(entries) = fs::read_dir(&directory) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                stack.push(path);
            } else if path.extension().is_some_and(|kind| kind == "lean") {
                paths.push(path);
            }
        }
    }
    paths.sort();

    let mut census = Census::default();
    // Declared names, so a name sunk into `local_bindings` can be recognised as a real declaration.
    let mut declared: BTreeSet<String> = BTreeSet::new();
    let mut local_binding_names: BTreeMap<String, usize> = BTreeMap::new();
    for path in &paths {
        let Ok(text) = fs::read_to_string(path) else {
            continue;
        };
        let lines: Vec<&str> = text.lines().collect();
        let reading = read_development_at(
            &text,
            DeclarationGrain::EveryTopLevelDeclaration,
            BinderGrain::EveryBinder,
        );
        census.files += 1;
        census.declarations += reading.declarations.len();
        for form in &reading.declarations {
            declared.insert(form.name.clone());
            census_of(form, &lines, &mut census);
            for name in form.local_bindings.keys() {
                *local_binding_names.entry(name.clone()).or_insert(0) += 1;
            }
        }
    }
    let sunk: Vec<&String> = local_binding_names
        .keys()
        .filter(|name| declared.contains(*name))
        .collect();

    println!("\n=== the reader over the whole library");
    println!(
        "  files                                     {:>8}",
        census.files
    );
    println!(
        "  declarations                              {:>8}",
        census.declarations
    );
    println!(
        "  proof steps                               {:>8}",
        census.steps
    );
    println!("\n=== the four populations the repair must move");
    println!(
        "  empty recruitment (cannot be an arrival target) {:>8}   of {}",
        census.empty_recruitment, census.steps
    );
    println!(
        "  in a multi-binder cohort                        {:>8}",
        census.in_multi_binder_cohort
    );
    println!(
        "  statement opens with `with`                     {:>8}",
        census.statement_opens_with_with
    );
    println!(
        "  line does not carry its own former              {:>8}",
        census.line_misses_its_former
    );
    println!(
        "  statement is bracket-unbalanced                 {:>8}",
        census.statement_unbalanced
    );
    println!(
        "  statement empty (the tactic carried no `:`)     {:>8}",
        census.statement_empty
    );
    println!(
        "\n  declared names sunk into local_bindings         {:>8}   of {} distinct",
        sunk.len(),
        local_binding_names.len()
    );
    for name in sunk.iter().take(8) {
        println!("      {name}");
    }

    // ------------------------------------------------------------------ the species populations
    println!("\n=== what the species reading sits on — {GEOMETRY}");
    match fs::read_to_string(material.join(GEOMETRY)) {
        Ok(text) => {
            let reading = read_development_at(
                &text,
                DeclarationGrain::EveryTopLevelDeclaration,
                BinderGrain::EveryBinder,
            );
            let complex = MoveComplex::found(&reading.declarations);
            let isolated: BTreeSet<MoveOccurrence> = complex.isolated().into_iter().collect();
            println!(
                "  moves {} · arrivals {} · connected {} · isolated {} · unconsumed {}",
                complex.moves(),
                complex.arrivals(),
                complex.connected().len(),
                isolated.len(),
                complex.unconsumed().len()
            );
            println!("  THE FALSIFIER: these must move after the repair. If they do not, the four");
            println!(
                "  defects were not load-bearing for the species reading and the movement must"
            );
            println!("  say so rather than presenting a green suite as evidence.");
        }
        Err(error) => println!("  absent: {error}"),
    }
}
