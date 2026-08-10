//! `derivation_atlas::read_derivation` against material it was never built for, and against the
//! material it was.
//!
//! ## What this measures
//!
//! The reading opens one artifact as one `theorem`, has no comment lexer, and knows one naming
//! former. Pointed at a development a person wrote it did not fail — it **returned**, and returned
//! something clean-looking: a name, a normalized statement, and a recruitment multiset. Every atlas
//! and every `RebaseInvariants` figure computed through it on real Lean was that fiction carried
//! forward, and nothing in the type said so.
//!
//! `crate::derivation_atlas::DerivationApertureRefusal` is the aperture made refusable. This driver
//! runs both sides of it:
//!
//! - a **foreign corpus** — a file list of real Lean, mathlib — where every clause should fire and
//!   the return should be nothing at all;
//! - the **machine's own deposit**, where no clause may fire, because a refusal that also refused
//!   the deposit would have replaced a fiction with a silence.
//!
//! Both are needed. `CLAUDE.md` §8: *a check whose material cannot vary the property under test is
//! the same defect as a check that cannot fail.*
//!
//! ```text
//! cargo run --example the_reader_refuses_what_it_cannot_read -- <lean-file-list> <deposit-root>
//! ```

use std::collections::BTreeMap;
use std::fs;
use std::path::Path;

use holonic_engine::derivation_atlas::{
    derivation_aperture_obstructions, read_derivation, read_derivation_within_aperture,
    DerivationApertureRefusal,
};

fn species(refusal: &DerivationApertureRefusal) -> &'static str {
    match refusal {
        DerivationApertureRefusal::CommentText { .. } => "comment-text",
        DerivationApertureRefusal::PluralNamingDeclarations { .. } => "plural-naming",
        DerivationApertureRefusal::NoTheoremDeclared => "no-theorem",
    }
}

struct Reading {
    files: usize,
    returned: usize,
    refused: usize,
    by_species: BTreeMap<&'static str, usize>,
    by_first_clause: BTreeMap<&'static str, usize>,
    absorbed_declarations: usize,
    /// Files the **historical** gate would have returned a `Derivation` for: it named the last line
    /// whose trimmed head was `theorem `, and returned `None` only when there was none. Recomputed
    /// here from that one condition rather than by keeping the unguarded parse alive, because
    /// `CLAUDE.md` §13 rule 3 removes superseded production machinery rather than deprecating it.
    would_have_returned: usize,
    /// Of those, the ones that are now refused. The fiction population, exactly.
    fictions_withdrawn: usize,
    exhibited: Vec<(String, String)>,
}

fn read(paths: &[String], exhibit: usize) -> Reading {
    let mut carried = Reading {
        files: paths.len(),
        returned: 0,
        refused: 0,
        by_species: BTreeMap::new(),
        by_first_clause: BTreeMap::new(),
        absorbed_declarations: 0,
        would_have_returned: 0,
        fictions_withdrawn: 0,
        exhibited: Vec::new(),
    };
    for path in paths {
        let Ok(text) = fs::read_to_string(path) else {
            continue;
        };
        let historically = text
            .lines()
            .any(|line| line.trim().starts_with("theorem "));
        if historically {
            carried.would_have_returned += 1;
        }
        let obstructions = derivation_aperture_obstructions(&text);
        for refusal in &obstructions {
            *carried.by_species.entry(species(refusal)).or_insert(0) += 1;
            if let DerivationApertureRefusal::PluralNamingDeclarations { names, .. } = refusal {
                // Every naming declaration past the one the reading returns is a derivation the
                // historical reading absorbed without saying so.
                carried.absorbed_declarations += names.len().saturating_sub(1);
            }
        }
        match read_derivation_within_aperture(&text) {
            Ok(_) => {
                carried.returned += 1;
                assert!(read_derivation(&text).is_some(), "the two entries agree");
            }
            Err(first) => {
                carried.refused += 1;
                if historically {
                    carried.fictions_withdrawn += 1;
                }
                *carried.by_first_clause.entry(species(&first)).or_insert(0) += 1;
                assert!(
                    read_derivation(&text).is_none(),
                    "a refused text returns no Derivation: {path}"
                );
                if carried.exhibited.len() < exhibit {
                    carried
                        .exhibited
                        .push((path.clone(), format!("{first}")));
                }
            }
        }
    }
    carried
}

fn lean_under(root: &Path, into: &mut Vec<String>) {
    let Ok(entries) = fs::read_dir(root) else {
        return;
    };
    let mut found: Vec<_> = entries.flatten().map(|entry| entry.path()).collect();
    found.sort();
    for path in found {
        if path.is_dir() {
            lean_under(&path, into);
        } else if path.extension().and_then(|value| value.to_str()) == Some("lean") {
            into.push(path.display().to_string());
        }
    }
}

fn main() {
    let mut args = std::env::args().skip(1);
    let listing = args.next().expect("a listing of Lean files");
    let deposit = args.next().expect("the machine's own deposit root");

    let foreign: Vec<String> = fs::read_to_string(&listing)
        .expect("listing")
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(str::to_owned)
        .collect();
    let mut own = Vec::new();
    lean_under(Path::new(&deposit), &mut own);

    let far = read(&foreign, 6);
    let near = read(&own, 6);

    println!("THE READER REFUSES WHAT IT CANNOT READ");
    println!("======================================\n");

    println!("  a development nobody here wrote — {listing}");
    println!("    files                                {}", far.files);
    println!("    returned a Derivation                {}", far.returned);
    println!("    refused by the aperture              {}", far.refused);
    println!("    top-level derivations it absorbed    {}", far.absorbed_declarations);
    println!("    clauses that fired, by species:");
    for (name, count) in &far.by_species {
        println!("      {name:<16} {count:>6}");
    }
    println!("    the clause each refusal returned first:");
    for (name, count) in &far.by_first_clause {
        println!("      {name:<16} {count:>6}");
    }

    println!("\n    the obstruction, verbatim, on the first files that carry one:");
    for (path, refusal) in &far.exhibited {
        let short = path.rsplit("/Mathlib/").next().unwrap_or(path);
        println!("      {short}");
        println!("        {refusal}");
    }

    println!("\n  the machine's own deposit — {deposit}");
    println!("    files                                {}", near.files);
    println!("    returned a Derivation                {}", near.returned);
    println!("    refused by the aperture              {}", near.refused);
    if near.refused == 0 {
        println!("    no clause fires: the aperture is exact on the material it was built for");
    } else {
        println!("    CLAUSES FIRED ON THE DEPOSIT — the aperture is too narrow:");
        for (path, refusal) in &near.exhibited {
            println!("      {path}\n        {refusal}");
        }
    }

    println!("\n  what the refusal withdrew");
    println!(
        "    the historical gate returned a Derivation for  {} of {} foreign files",
        far.would_have_returned, far.files
    );
    println!(
        "    of those, now refused instead                 {}",
        far.fictions_withdrawn
    );
    println!(
        "    and on the deposit it withdrew                {} of {}",
        near.fictions_withdrawn, near.would_have_returned
    );
}
