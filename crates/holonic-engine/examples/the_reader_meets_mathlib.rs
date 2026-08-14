//! Measure what `lean_development::read_development` and `derivation_atlas::read_derivation`
//! actually recover from mathlib, against an independent ground truth taken outside this crate.
//!
//! This driver **measures**; it changes nothing and tunes nothing. Every population it prints is
//! read straight off the returned carriers.
//!
//! ```text
//! cargo run --release --example the_reader_meets_mathlib -- <file-list> <out-prefix>
//! ```
//!
//! Emitted, all TSV, all keyed by absolute path so a second route can join on it:
//!
//! ```text
//! <prefix>.decl.tsv    path line former name ns_depth namespace recruited tactics steps locals stmt_len
//! <prefix>.unopened.tsv path line former name
//! <prefix>.pops.tsv    path decls commentary_kinds commentary_occ preamble_kinds preamble_occ
//!                           scoping_kinds scoping_occ ambiguous singles
//! <prefix>.edges.tsv   path from to
//! <prefix>.single.tsv  path name holder
//! <prefix>.deriv.tsv   path name recruited          (the one-theorem reader)
//! <prefix>.cost.tsv    files lines bytes parse_nanos
//! <prefix>.tokens.tsv  the census tokenizer's split over the same bytes
//! ```

use std::collections::BTreeMap;
use std::fs;
use std::io::Write;
use std::time::Instant;

use holonic_engine::corpus_census::{Kind, classify, tokenize};
use holonic_engine::derivation_atlas::read_derivation;
use holonic_engine::lean_development::{DeclarationGrain, read_development};

fn main() {
    let mut args = std::env::args().skip(1);
    let listing = args.next().expect("file list");
    let prefix = args.next().expect("out prefix");
    // A whole-corpus run must not write hundreds of megabytes of per-declaration rows to a tmpfs.
    let summary_only = std::env::var("SUMMARY_ONLY").is_ok();
    let paths: Vec<String> = fs::read_to_string(&listing)
        .expect("listing")
        .lines()
        .filter(|line| !line.trim().is_empty())
        .map(str::to_owned)
        .collect();

    // Read every whole first, so the timed region is the reading and not the disk.
    let mut texts: Vec<(String, String)> = Vec::with_capacity(paths.len());
    let mut bytes = 0usize;
    let mut lines = 0usize;
    for path in &paths {
        let text = fs::read_to_string(path).unwrap_or_default();
        bytes += text.len();
        lines += text.lines().count();
        texts.push((path.clone(), text));
    }

    let mut decl = open(&format!("{prefix}.decl.tsv"));
    let mut unopened = open(&format!("{prefix}.unopened.tsv"));
    let mut pops = open(&format!("{prefix}.pops.tsv"));
    let mut edges = open(&format!("{prefix}.edges.tsv"));
    let mut single = open(&format!("{prefix}.single.tsv"));
    let mut deriv = open(&format!("{prefix}.deriv.tsv"));
    let mut recruit = open(&format!("{prefix}.recruit.tsv"));
    let mut stmt = open(&format!("{prefix}.stmt.tsv"));
    let mut vocab = open(&format!("{prefix}.vocab.tsv"));

    // ------------------------------------------------------------------ the timed reading
    let start = Instant::now();
    let readings: Vec<_> = texts
        .iter()
        .map(|(_, text)| read_development(text, DeclarationGrain::EveryTopLevelDeclaration))
        .collect();
    let parse_nanos = start.elapsed().as_nanos();

    let start_one = Instant::now();
    let one: Vec<_> = texts
        .iter()
        .map(|(_, text)| read_derivation(text))
        .collect();
    let one_nanos = start_one.elapsed().as_nanos();

    // A second grain, to show what the one-artifact aperture does to a development.
    let one_grain: Vec<_> = texts
        .iter()
        .map(|(_, text)| read_development(text, DeclarationGrain::OneArtifactOneDeclaration))
        .collect();

    // ------------------------------------------------------------------ what came back
    let mut terms: BTreeMap<String, u64> = BTreeMap::new();
    let mut tactic_vocab: BTreeMap<String, u64> = BTreeMap::new();
    let mut local_vocab: BTreeMap<String, u64> = BTreeMap::new();
    let mut comment_vocab: BTreeMap<String, u64> = BTreeMap::new();
    let mut preamble_vocab: BTreeMap<String, u64> = BTreeMap::new();
    let mut arrivals_total = 0usize;
    let mut steps_total = 0usize;
    let mut open_projection_total = 0usize;

    for ((path, _), reading) in texts.iter().zip(readings.iter()) {
        open_projection_total += reading.open_projections().len();
        for (name, count) in &reading.commentary {
            *comment_vocab.entry(name.clone()).or_insert(0) += *count as u64;
        }
        for (name, count) in &reading.preamble {
            *preamble_vocab.entry(name.clone()).or_insert(0) += *count as u64;
        }
        for form in &reading.declarations {
            arrivals_total += form.internal_arrivals().len();
            steps_total += form.steps.len();
            if !summary_only {
                writeln!(
                    stmt,
                    "{path}\t{}\t{}\t{}",
                    form.line,
                    form.name,
                    form.statement.replace('\t', " ")
                )
                .unwrap();
            }
            for (symbol, count) in &form.recruited {
                *terms.entry(symbol.clone()).or_insert(0) += *count as u64;
                if !summary_only {
                    writeln!(recruit, "{path}\t{}\t{symbol}\t{count}", form.name).unwrap();
                }
            }
            for (symbol, count) in &form.tactics {
                *tactic_vocab.entry(symbol.clone()).or_insert(0) += *count as u64;
            }
            for (symbol, count) in &form.local_bindings {
                *local_vocab.entry(symbol.clone()).or_insert(0) += *count as u64;
            }
        }
    }
    for (label, table) in [
        ("term", &terms),
        ("tactic", &tactic_vocab),
        ("local", &local_vocab),
        ("commentary", &comment_vocab),
        ("preamble", &preamble_vocab),
    ] {
        let mut ranked: Vec<_> = table.iter().collect();
        ranked.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
        let occ: u64 = table.values().sum();
        writeln!(
            vocab,
            "#{label}\tdistinct\t{}\toccurrences\t{occ}",
            table.len()
        )
        .unwrap();
        for (symbol, count) in ranked.iter().take(120) {
            writeln!(vocab, "{label}\t{symbol}\t{count}").unwrap();
        }
    }

    for ((path, _), reading) in texts.iter().zip(readings.iter()) {
        for form in &reading.declarations {
            let recruited: u32 = form.recruited.values().sum();
            let tactics: u32 = form.tactics.values().sum();
            let locals: u32 = form.local_bindings.values().sum();
            writeln!(
                decl,
                "{path}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
                form.line,
                form.former,
                form.name,
                form.namespace_path.len(),
                form.namespace_path.join("."),
                recruited,
                tactics,
                form.steps.len(),
                locals,
                form.statement.chars().count()
            )
            .unwrap();
        }
        for lost in &reading.unopened {
            writeln!(
                unopened,
                "{path}\t{}\t{}\t{}",
                lost.line, lost.former, lost.name
            )
            .unwrap();
        }
        let commentary_occ: u32 = reading.commentary.values().sum();
        let preamble_occ: u32 = reading.preamble.values().sum();
        let scoping_occ: u32 = reading.scoping.values().sum();
        let singles = reading.single_occurrence_terms();
        writeln!(
            pops,
            "{path}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}\t{}",
            reading.declarations.len(),
            reading.commentary.len(),
            commentary_occ,
            reading.preamble.len(),
            preamble_occ,
            reading.scoping.len(),
            scoping_occ,
            reading.ambiguous_short_names.len(),
            singles.len()
        )
        .unwrap();
        if !summary_only {
            for (from, to) in reading.declared_recruitment() {
                for target in to {
                    writeln!(edges, "{path}\t{from}\t{target}").unwrap();
                }
            }
            for (name, holder) in singles {
                writeln!(single, "{path}\t{name}\t{holder}").unwrap();
            }
        }
    }

    for ((path, _), read) in texts.iter().zip(one.iter()) {
        if summary_only {
            break;
        }
        match read {
            Some(derivation) => writeln!(
                deriv,
                "{path}\t{}\t{}",
                derivation.name,
                derivation.recruited.len()
            )
            .unwrap(),
            None => writeln!(deriv, "{path}\t<none>\t0").unwrap(),
        }
    }

    // ------------------------------------------------------------------ the census tokenizer
    let start_tok = Instant::now();
    let mut kinds: BTreeMap<&'static str, u64> = BTreeMap::new();
    let mut markup_forms: BTreeMap<String, u64> = BTreeMap::new();
    let mut total = 0u64;
    for (_, text) in &texts {
        for surface in tokenize(text) {
            total += 1;
            let kind = classify(surface);
            *kinds.entry(kind.name()).or_insert(0) += 1;
            if kind == Kind::Markup {
                *markup_forms.entry(surface.to_owned()).or_insert(0) += 1;
            }
        }
    }
    let token_nanos = start_tok.elapsed().as_nanos();
    let mut tokens = open(&format!("{prefix}.tokens.tsv"));
    writeln!(tokens, "#total\t{total}").unwrap();
    for (kind, count) in &kinds {
        writeln!(tokens, "kind\t{kind}\t{count}").unwrap();
    }
    let mut ranked: Vec<_> = markup_forms.iter().collect();
    ranked.sort_by(|a, b| b.1.cmp(a.1).then(a.0.cmp(b.0)));
    writeln!(tokens, "#distinct_markup\t{}", markup_forms.len()).unwrap();
    for (surface, count) in ranked.iter().take(80) {
        writeln!(tokens, "markup\t{surface}\t{count}").unwrap();
    }

    let mut cost = open(&format!("{prefix}.cost.tsv"));
    writeln!(cost, "files\t{}", paths.len()).unwrap();
    writeln!(cost, "lines\t{lines}").unwrap();
    writeln!(cost, "bytes\t{bytes}").unwrap();
    writeln!(cost, "read_development_nanos\t{parse_nanos}").unwrap();
    writeln!(cost, "read_derivation_nanos\t{one_nanos}").unwrap();
    writeln!(cost, "tokenize_nanos\t{token_nanos}").unwrap();
    let declarations: usize = readings.iter().map(|r| r.declarations.len()).sum();
    writeln!(cost, "declarations\t{declarations}").unwrap();
    writeln!(cost, "proof_steps\t{steps_total}").unwrap();
    writeln!(cost, "internal_arrivals\t{arrivals_total}").unwrap();
    writeln!(cost, "open_projections\t{open_projection_total}").unwrap();
    let one_opened: usize = one_grain.iter().map(|r| r.declarations.len()).sum();
    let one_unopened: usize = one_grain.iter().map(|r| r.unopened.len()).sum();
    writeln!(cost, "one_artifact_opened\t{one_opened}").unwrap();
    writeln!(cost, "one_artifact_unopened\t{one_unopened}").unwrap();
    eprintln!(
        "files {} lines {lines} declarations {declarations} read_development {:.3}s",
        paths.len(),
        parse_nanos as f64 / 1e9
    );
}

fn open(path: &str) -> std::io::BufWriter<fs::File> {
    std::io::BufWriter::new(fs::File::create(path).expect("create"))
}
