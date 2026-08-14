//! `corpus_census` over a corpus this repository did not write, under both declared species.
//!
//! ## What this measures
//!
//! Two defects, one repair each, and the second is only visible because of the first.
//!
//! **The corpus was the organ's.** `CorpusCensus::read` joined its root with four `&'static str`
//! paths compiled into the module, and `admit` was private, so **every corpus that was not this
//! repository returned `EmptyStratum`**. The strata are now the caller's: this driver declares four
//! frames over four areas of mathlib — four genuinely different mathematical materials, which is
//! what `CLAUDE.md` §0's fourth lesson asks a frame population to be — and hands them in.
//!
//! **The lexer was the organ's too, and on Lean it shatters.** `LexicalSpecies::Prose` reads word
//! runs as `[A-Za-z0-9_]` over **bytes**: `Nat.succ` becomes three surfaces and a dot, `h₁` becomes
//! two, and a copyright header's English is indistinguishable from what the source named. The
//! species is now declared at the call, and this driver runs the same bytes under both so the
//! difference is a measurement rather than a claim.
//!
//! Nothing here selects, ranks, thresholds or prunes. Every figure is a count of what occurred.
//!
//! ```text
//! cargo run --example the_census_is_pointed_at_a_foreign_corpus -- <mathlib-root>
//! ```

use std::path::Path;

use holonic_engine::corpus_census::{
    CorpusCensus, Kind, LexicalSpecies, Stratum, StratumDeclaration, SurfaceId,
};

/// **The caller's corpus.** Four areas of mathlib, declared here in the driver, because a corpus is
/// a caller's declaration and this caller is not this repository's own writing.
const MATHLIB_AREAS: [StratumDeclaration; 4] = [
    StratumDeclaration {
        stratum: Stratum(0),
        label: "logic",
        relative_root: "Mathlib/Logic",
        extension: "lean",
        recursive: true,
    },
    StratumDeclaration {
        stratum: Stratum(1),
        label: "dynamics",
        relative_root: "Mathlib/Dynamics",
        extension: "lean",
        recursive: true,
    },
    StratumDeclaration {
        stratum: Stratum(2),
        label: "computability",
        relative_root: "Mathlib/Computability",
        extension: "lean",
        recursive: true,
    },
    StratumDeclaration {
        stratum: Stratum(3),
        label: "probability",
        relative_root: "Mathlib/Probability",
        extension: "lean",
        recursive: true,
    },
];

/// A surface every one of whose characters is a Unicode subscript. Under `Prose` these are the
/// splinters `h₁` left behind; under `LeanSource` an identifier keeps them.
fn is_bare_subscript(surface: &str) -> bool {
    !surface.is_empty()
        && surface.chars().all(|character| {
            ('\u{2080}'..='\u{209C}').contains(&character)
                || ('\u{1D62}'..='\u{1D6A}').contains(&character)
        })
}

struct Reading {
    species: &'static str,
    wholes: usize,
    total: u64,
    word: u64,
    markup: u64,
    distinct: usize,
    dot_occurrences: u64,
    dot_rank: Option<usize>,
    bare_subscript_occurrences: u64,
    bare_subscript_surfaces: usize,
    /// `₁` standing alone, which is what an ASCII word rule leaves of `h₁`.
    one_subscript: u64,
    /// Every bare subscript surface with its count, most recurrent first, so the residue is
    /// exhibited rather than asserted to be notation.
    bare_subscripts: Vec<(String, u64)>,
    qualified_surfaces: usize,
    comment_occurrences: u64,
    comment_surfaces: usize,
    top: Vec<(String, u64, Kind)>,
}

fn measure(census: &CorpusCensus, species: &'static str) -> Reading {
    let mut ordered: Vec<(u64, SurfaceId)> = census
        .all_surfaces()
        .map(|id| (census.occurrences(id), id))
        .collect();
    ordered.sort_by(|left, right| right.0.cmp(&left.0).then(left.1.cmp(&right.1)));

    let dot = census.lookup(".");
    let dot_rank = dot.and_then(|id| ordered.iter().position(|(_, other)| *other == id));

    let mut bare_subscript_occurrences = 0u64;
    let mut bare_subscript_surfaces = 0usize;
    let mut bare_subscripts: Vec<(String, u64)> = Vec::new();
    let mut qualified_surfaces = 0usize;
    for id in census.all_surfaces() {
        let surface = census.surface(id);
        if is_bare_subscript(surface) {
            bare_subscript_surfaces += 1;
            bare_subscript_occurrences += census.occurrences(id);
            bare_subscripts.push((surface.to_owned(), census.occurrences(id)));
        }
        if census.kind(id).is_word() && surface.contains('.') {
            qualified_surfaces += 1;
        }
    }

    let comments = census.comment_bound(0);
    Reading {
        species,
        wholes: census.wholes().len(),
        total: census.total_occurrences(),
        word: census.word_occurrences(),
        markup: census.total_occurrences() - census.word_occurrences(),
        distinct: census.all_surfaces().count(),
        dot_occurrences: dot.map(|id| census.occurrences(id)).unwrap_or(0),
        dot_rank: dot_rank.map(|at| at + 1),
        bare_subscript_occurrences,
        bare_subscript_surfaces,
        one_subscript: census
            .lookup("\u{2081}")
            .map(|id| census.occurrences(id))
            .unwrap_or(0),
        bare_subscripts: {
            bare_subscripts.sort_by(|left, right| right.1.cmp(&left.1).then(left.0.cmp(&right.0)));
            bare_subscripts
        },
        qualified_surfaces,
        comment_occurrences: comments
            .comment_occurrences
            .to_u64_digits()
            .first()
            .copied()
            .unwrap_or(0),
        comment_surfaces: comments.distinct_comment_surfaces,
        top: ordered
            .iter()
            .take(12)
            .map(|(count, id)| (census.surface(*id).to_owned(), *count, census.kind(*id)))
            .collect(),
    }
}

fn percent(part: u64, whole: u64) -> String {
    if whole == 0 {
        return "-".to_owned();
    }
    // Exact integer arithmetic to one decimal place. No float is constructed anywhere.
    let tenths = part.saturating_mul(1000) / whole;
    format!("{}.{}%", tenths / 10, tenths % 10)
}

fn main() {
    let root = std::env::args()
        .nth(1)
        .expect("the root of a corpus this repository did not write");
    let root = Path::new(&root);

    println!("THE CENSUS IS POINTED AT A FOREIGN CORPUS");
    println!("=========================================\n");

    println!("  the caller's declaration — root {}", root.display());
    for declaration in MATHLIB_AREAS {
        println!(
            "    frame {}  {:<14} {:<26} *.{}",
            declaration.stratum.index(),
            declaration.label,
            declaration.relative_root,
            declaration.extension
        );
    }

    // The control that names what was broken: this repository's own four strata against a root
    // that is not this repository.
    match CorpusCensus::read(root) {
        Ok(_) => println!("\n  NOTE: this repository's own four strata resolve under that root"),
        Err(error) => println!("\n  this repository's own four strata, against that root: {error}"),
    }

    let mut readings = Vec::new();
    for (species, name) in [
        (LexicalSpecies::Prose, "prose"),
        (LexicalSpecies::LeanSource, "lean-source"),
    ] {
        let census = match CorpusCensus::read_declared(root, &MATHLIB_AREAS, species) {
            Ok(census) => census,
            Err(error) => {
                println!("\n  the declared corpus refused: {error}");
                return;
            }
        };
        for declaration in MATHLIB_AREAS {
            let wholes = census
                .wholes()
                .iter()
                .filter(|whole| whole.stratum == declaration.stratum)
                .count();
            if wholes == 0 {
                println!("  frame {} is empty", declaration.label);
            }
        }
        readings.push(measure(&census, name));
    }

    println!("\n  the same bytes, under the two declared species");
    println!(
        "    {:<28} {:>14} {:>14}",
        "", readings[0].species, readings[1].species
    );
    let rows: [(&str, Box<dyn Fn(&Reading) -> String>); 11] = [
        ("wholes", Box::new(|r: &Reading| r.wholes.to_string())),
        (
            "tokens in the stream",
            Box::new(|r: &Reading| r.total.to_string()),
        ),
        ("word tokens", Box::new(|r: &Reading| r.word.to_string())),
        (
            "markup tokens",
            Box::new(|r: &Reading| r.markup.to_string()),
        ),
        (
            "markup share",
            Box::new(|r: &Reading| percent(r.markup, r.total)),
        ),
        (
            "distinct surfaces",
            Box::new(|r: &Reading| r.distinct.to_string()),
        ),
        (
            "`.` occurrences (rank)",
            Box::new(|r: &Reading| match r.dot_rank {
                Some(rank) => format!("{} (#{rank})", r.dot_occurrences),
                None => "0 (absent)".to_owned(),
            }),
        ),
        (
            "`\u{2081}` standing alone",
            Box::new(|r: &Reading| r.one_subscript.to_string()),
        ),
        (
            "bare-subscript occurrences",
            Box::new(|r: &Reading| {
                format!(
                    "{} / {}",
                    r.bare_subscript_occurrences, r.bare_subscript_surfaces
                )
            }),
        ),
        (
            "qualified word surfaces",
            Box::new(|r: &Reading| r.qualified_surfaces.to_string()),
        ),
        (
            "comment population",
            Box::new(|r: &Reading| format!("{} / {}", r.comment_occurrences, r.comment_surfaces)),
        ),
    ];
    for (label, read) in rows {
        println!(
            "    {label:<28} {:>14} {:>14}",
            read(&readings[0]),
            read(&readings[1])
        );
    }

    println!("\n  the most recurrent surfaces, each species in its own order");
    println!(
        "    {:<34} {:<34}",
        readings[0].species, readings[1].species
    );
    for index in 0..12 {
        let left = readings[0]
            .top
            .get(index)
            .map(|(surface, count, kind)| format!("{surface:<18} {count:>7} {}", kind.name()))
            .unwrap_or_default();
        let right = readings[1]
            .top
            .get(index)
            .map(|(surface, count, kind)| format!("{surface:<18} {count:>7} {}", kind.name()))
            .unwrap_or_default();
        println!("    {left:<34} {right:<34}");
    }

    println!("\n  what moved");
    println!(
        "    the `.` was surface #{} under prose and is {} under lean-source",
        readings[0]
            .dot_rank
            .map(|r| r.to_string())
            .unwrap_or_else(|| "-".to_owned()),
        match readings[1].dot_rank {
            Some(rank) => format!("#{rank}"),
            None => "absent from the corpus".to_owned(),
        }
    );
    println!(
        "    {} qualified names such as `Nat.succ` exist as surfaces under lean-source and {} under prose",
        readings[1].qualified_surfaces, readings[0].qualified_surfaces
    );
    println!(
        "    {} subscript splinters became {}; `\u{2081}` alone went {} -> {}",
        readings[0].bare_subscript_occurrences,
        readings[1].bare_subscript_occurrences,
        readings[0].one_subscript,
        readings[1].one_subscript
    );
    println!("    the residue, exhibited rather than asserted to be notation:");
    for reading in &readings {
        let exhibited: Vec<String> = reading
            .bare_subscripts
            .iter()
            .take(8)
            .map(|(surface, count)| format!("{surface}:{count}"))
            .collect();
        println!("      {:<12} {}", reading.species, exhibited.join("  "));
    }
    println!(
        "    {} comment tokens left the stream and are returned by `comment_bound`, not dropped",
        readings[1].comment_occurrences
    );
}
