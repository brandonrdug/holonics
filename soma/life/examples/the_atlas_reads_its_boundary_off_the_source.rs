//! THE ATLAS READS ITS BOUNDARY OFF THE SOURCE — the orbit of three excised authored levels.
//!
//! `soma/life/src/laboratory_language/repository.rs` carried three numeric bounds that decided what
//! entered the laboratory source atlas and in what pieces:
//!
//! ```text
//!   const BLOCK_LINES: usize = 24          cut a blank-line-free Rust run at twenty-four lines
//!   if !(5..=96).contains(&words)          SILENTLY DROPPED every theory sentence outside 5..=96
//! ```
//!
//! Nothing derived any of the three. The first decided the section population, and therefore the
//! feature incidence a leader recruits over; the other two deleted returned material with no
//! receipt, which is the species `CLAUDE.md` §9 forbids outright.
//!
//! They are replaced by the source's own delimiters: a blank line or the **brace depth returning to
//! zero** for Rust, and *carries a word* — a predicate, not a length — for a theory sentence.
//!
//! This driver exists because no `LaboratorySourceAtlas` was constructed anywhere in the tree, so
//! the excision had no orbit until something mounted a declared fixture. It mounts one built from
//! REAL live material, reproduces the retired law verbatim beside the live one, and exhibits the
//! difference. Both routes are printed where they disagree; nothing here is a summary of a
//! measurement.
//!
//! Run: `cargo run -p life --example the_atlas_reads_its_boundary_off_the_source`

use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use life::causal_language::{lexical_tokens, render_tokens};
use life::laboratory_language::{text_features, LaboratoryResearchLeader, LaboratorySourceAtlas};

/// The theory material — real live canon, copied into the fixture's `src/soma/RESEARCH`.
const DECLARED_THEORY: &[&str] = &[
    "canon/THE_AUTHORED_LEVEL.md",
    "canon/THE_CONTAMINANT_PROTOCOL.md",
    "canon/THE_DOCUMENT_LAW.md",
    "canon/EPISTEMIC_GRADES.md",
];

/// The Rust material — real live owners, copied into the fixture's `src/soma/body`.
/// `lean_mathematics/syntax.rs` is here on purpose: it carries `'{'` and `'}'` as character
/// literals, which is exactly what separates a delimiter reader from a brace counter.
const DECLARED_RUST: &[&str] = &[
    "soma/body/src/law.rs",
    "soma/body/src/place.rs",
    "soma/body/src/num.rs",
    "soma/life/src/lean_mathematics/syntax.rs",
    "soma/life/src/laboratory_language/repository.rs",
];

/// The leader's declared region — plain words that occur in both materials, so the recruitment
/// figure is about the sectioning and not about whether the feature exists.
const DECLARED_REGION: &[&str] = &["grip", "boundary", "level", "source"];

fn main() {
    let root = repository_root();
    let fixture = std::env::temp_dir().join("holonics-atlas-boundary-fixture");
    let _ = fs::remove_dir_all(&fixture);

    // ── STATION 1 — the declared fixture ────────────────────────────────────────────────────
    let mut theory_bytes = 0usize;
    let mut rust_bytes = 0usize;
    fs::create_dir_all(fixture.join("src/soma/RESEARCH")).expect("fixture research root");
    fs::create_dir_all(fixture.join("src/soma/body")).expect("fixture rust root");
    let mut theory_at = Vec::new();
    for named in DECLARED_THEORY {
        let from = root.join(named);
        let into = fixture
            .join("src/soma/RESEARCH")
            .join(Path::new(named).file_name().expect("a file name"));
        let text = fs::read_to_string(&from).unwrap_or_else(|e| panic!("{}: {e}", from.display()));
        theory_bytes += text.len();
        fs::write(&into, &text).expect("fixture theory write");
        theory_at.push((relative(&fixture, &into), text));
    }
    let mut rust_at = Vec::new();
    for named in DECLARED_RUST {
        let from = root.join(named);
        let into = fixture
            .join("src/soma/body")
            .join(Path::new(named).file_name().expect("a file name"));
        let text = fs::read_to_string(&from).unwrap_or_else(|e| panic!("{}: {e}", from.display()));
        rust_bytes += text.len();
        fs::write(&into, &text).expect("fixture rust write");
        rust_at.push((relative(&fixture, &into), text));
    }
    println!("STATION 1 — THE DECLARED FIXTURE");
    println!("  root                 {}", fixture.display());
    println!(
        "  theory               {} files, {theory_bytes} octets",
        DECLARED_THEORY.len()
    );
    println!(
        "  rust                 {} files, {rust_bytes} octets",
        DECLARED_RUST.len()
    );
    for (source, _) in theory_at.iter().chain(rust_at.iter()) {
        println!("    {source}");
    }

    // ── STATION 2 — mounted under the live law ──────────────────────────────────────────────
    let atlas = LaboratorySourceAtlas::mount_repository(&fixture).expect("the fixture mounts");
    let receipt = atlas.receipt();
    println!("\nSTATION 2 — MOUNTED UNDER THE LIVE LAW");
    println!("  source_files         {}", receipt.source_files);
    println!("  theory_sections      {}", receipt.theory_sections);
    println!("  rust_source_sections {}", receipt.rust_source_sections);
    println!("  indexed_features     {}", receipt.indexed_features);

    // ── STATION 3 — the retired law, reproduced verbatim ────────────────────────────────────
    let mut retired_theory = Vec::new();
    for (source, text) in &theory_at {
        retired_theory_sections(source, text, &mut retired_theory);
    }
    let mut live_theory = Vec::new();
    for (source, text) in &theory_at {
        live_theory_sections(source, text, &mut live_theory);
    }
    let mut retired_rust = Vec::new();
    let mut live_rust = Vec::new();
    let mut naive_rust = Vec::new();
    for (source, text) in &rust_at {
        retired_rust_sections(source, text, &mut retired_rust);
        live_rust_sections(source, text, Delimiters::Lexical, &mut live_rust);
        live_rust_sections(source, text, Delimiters::NaiveBraces, &mut naive_rust);
    }
    println!("\nSTATION 3 — THE RETIRED LAW, REPRODUCED, AND THE REPRODUCTION CHECKED");
    println!(
        "  theory   retired {:>5}   live {:>5}",
        retired_theory.len(),
        live_theory.len()
    );
    println!(
        "  rust     retired {:>5}   live {:>5}",
        retired_rust.len(),
        live_rust.len()
    );
    // The reproduction is only worth anything if it reproduces. Check the LIVE half of it against
    // the library's own return, identity for identity.
    let every_feature = live_theory
        .iter()
        .chain(live_rust.iter())
        .flat_map(|section| section.features.iter().cloned())
        .collect::<BTreeSet<_>>();
    let (library_identities, reached) = atlas_identities(&atlas, every_feature);
    let held = receipt.theory_sections + receipt.rust_source_sections;
    assert_eq!(
        reached, held,
        "the whole-atlas region reached every section the receipt says the atlas holds"
    );
    let reproduced_identities = live_theory
        .iter()
        .chain(live_rust.iter())
        .map(|section| section.identity.clone())
        .collect::<BTreeSet<_>>();
    let only_library = library_identities
        .difference(&reproduced_identities)
        .count();
    let only_reproduced = reproduced_identities
        .difference(&library_identities)
        .count();
    println!(
        "  library holds {held} sections, all {reached} reached; driver reproduces {}",
        reproduced_identities.len()
    );
    println!("  library-only {only_library}, driver-only {only_reproduced}");
    assert_eq!(only_library, 0, "the driver reproduces the library's law");
    assert_eq!(only_reproduced, 0, "and adds nothing to it");

    // ── STATION 4 — the orbit, theory ───────────────────────────────────────────────────────
    let retired_ids = retired_theory
        .iter()
        .map(|s| s.identity.clone())
        .collect::<BTreeSet<_>>();
    let dropped = live_theory
        .iter()
        .filter(|s| !retired_ids.contains(&s.identity))
        .collect::<Vec<_>>();
    let below = dropped.iter().filter(|s| s.words < 5).count();
    let above = dropped.iter().filter(|s| s.words > 96).count();
    println!("\nSTATION 4 — THE ORBIT, THEORY");
    println!(
        "  the retired range deleted {} of {} sentences  ({below} below five words, {above} above ninety-six)",
        dropped.len(),
        live_theory.len()
    );
    // reproduction fidelity: every retired section obeys the retired law, by construction.
    assert!(
        retired_theory.iter().all(|s| (5..=96).contains(&s.words)),
        "the reproduced retired law admits only 5..=96"
    );
    // and the orbit is non-trivial: the live return contains what the retired law refused.
    assert!(
        !dropped.is_empty(),
        "CONTROL REFUSES ITSELF: the retired range deleted nothing on this material"
    );
    let mut histogram = BTreeMap::<usize, usize>::new();
    for section in &dropped {
        *histogram.entry(section.words).or_default() += 1;
    }
    println!("  by word count          {histogram:?}");
    let widest = live_theory.iter().map(|s| s.words).max().unwrap_or(0);
    println!(
        "  the widest sentence on this material is {widest} words, so the retired UPPER bound of \
         ninety-six was inert here"
    );
    println!(
        "  material that would hit it: a paragraph whose sentence splitter never fires — a table \
         row or a long list rendered as prose"
    );
    // THE ARTIFACT, returned rather than counted. Every deleted sentence at the widest deleted
    // length, whole — the selection is derived from the population, not a truncation of it.
    let widest_deleted = dropped.iter().map(|s| s.words).max().unwrap_or(0);
    if let Some(shortest) = dropped.iter().min_by_key(|s| (s.words, s.identity.clone())) {
        println!(
            "  the narrowest deleted  [{} words] {}\n    {}",
            shortest.words, shortest.identity, shortest.text
        );
    }
    println!("  every deleted sentence at the widest deleted length ({widest_deleted} words):");
    for section in dropped.iter().filter(|s| s.words == widest_deleted) {
        println!("    {}\n      {}", section.identity, section.text);
    }
    // WHAT THE LEVEL WAS MASKING. A fragment this short is not prose the author wrote; it is the
    // sentence splitter firing on the `.` inside a file extension. The retired bound deleted the
    // evidence of that instead of the fragment's cause.
    let extension_artifacts = dropped
        .iter()
        .filter(|section| section.text.starts_with("rs ") || section.text.starts_with("md "))
        .count();
    println!(
        "  of the deleted, {extension_artifacts} open with `rs ` or `md ` — the splitter firing on \
         the `.` inside a path like `soma/body/src/law.rs`, which the retired bound was hiding \
         rather than fixing"
    );

    // ── STATION 5 — the orbit, Rust ─────────────────────────────────────────────────────────
    println!("\nSTATION 5 — THE ORBIT, RUST");
    let retired_longest = retired_rust.iter().map(|s| s.lines).max().unwrap_or(0);
    let live_longest = live_rust.iter().map(|s| s.lines).max().unwrap_or(0);
    assert!(
        retired_longest <= 24,
        "the reproduced retired law never exceeds twenty-four lines"
    );
    let past_the_count = live_rust.iter().filter(|s| s.lines > 24).count();
    println!(
        "  longest section        retired {retired_longest} lines   live {live_longest} lines"
    );
    println!(
        "  sections past the retired count: {past_the_count} of {}",
        live_rust.len()
    );
    assert!(
        past_the_count > 0,
        "CONTROL REFUSES ITSELF: nothing on this material exceeded twenty-four lines"
    );
    // THE DISTINGUISHING WORD: the first place the retired count cut and the live delimiter did not.
    let mut retired_starts = BTreeMap::<String, BTreeSet<usize>>::new();
    for section in &retired_rust {
        retired_starts
            .entry(section.source.clone())
            .or_default()
            .insert(section.line);
    }
    let mut exhibited = 0usize;
    for section in live_rust.iter().filter(|s| s.lines > 24) {
        let cut_at = section.line + 24;
        let starts = retired_starts.get(&section.source);
        if starts.is_some_and(|s| s.contains(&cut_at)) {
            println!(
                "  {} — the retired law opened a new section at line {cut_at}; the live law runs {}..{} and closes at the brace",
                section.source,
                section.line,
                section.line + section.lines - 1
            );
            println!("    line {:>5}  {}", cut_at - 1, section.line_at(24 - 1));
            println!(
                "    line {:>5}  {}   <- the retired cut",
                cut_at,
                section.line_at(24)
            );
            println!(
                "    line {:>5}  {}   <- the live boundary",
                section.line + section.lines - 1,
                section.line_at(section.lines - 1)
            );
            exhibited += 1;
            if exhibited == 1 {
                break;
            }
        }
    }
    assert_eq!(exhibited, 1, "one cut exhibited whole");
    // AND THE BRACE ITSELF. The exhibit above closes on a blank line, which the retired law also
    // had; the level that replaced twenty-four is the depth returning to zero. Two figures: how
    // many sections the brace closed at all, and how many of those the blank line did NOT also
    // cover — the second is the only one that measures what the depth rule adds.
    let mut brace_closed = 0usize;
    let mut brace_only = 0usize;
    let mut brace_shown = false;
    for (source, text) in &rust_at {
        let lines = text.lines().collect::<Vec<_>>();
        let closes = closings(text, Delimiters::Lexical);
        for section in live_rust.iter().filter(|s| &s.source == source) {
            let last = section.line + section.lines - 1;
            if !closes.get(last - 1).copied().unwrap_or(false) {
                continue;
            }
            brace_closed += 1;
            let next_is_blank = lines.get(last).is_some_and(|line| line.trim().is_empty());
            if next_is_blank || last >= lines.len() {
                continue;
            }
            brace_only += 1;
            if !brace_shown {
                println!(
                    "  {source} — a section the BRACE closed where no blank line would have: {}..{last}",
                    section.line
                );
                println!(
                    "    line {:>5}  {}   <- depth returns to zero",
                    last,
                    lines[last - 1]
                );
                println!(
                    "    line {:>5}  {}   <- the next section opens here",
                    last + 1,
                    lines[last]
                );
                brace_shown = true;
            }
        }
    }
    println!(
        "  sections whose last line closed a brace group: {brace_closed}; of those, \
         {brace_only} where no blank line followed — the depth rule's own contribution"
    );
    assert!(
        brace_only > 0,
        "CONTROL REFUSES ITSELF: the depth rule added no boundary the blank line did not already \
         give, so only the blank line is doing work on this material"
    );
    // the widest live section, named — the material's own answer to what the retired count capped.
    if let Some(widest) = live_rust
        .iter()
        .max_by_key(|s| (s.lines, s.identity.clone()))
    {
        println!(
            "  the widest live section is {} lines: {} — the retired law returned it as {} pieces",
            widest.lines,
            widest.identity,
            widest.lines.div_ceil(24)
        );
    }
    // and the line tally: one closing entry per line, or the boundary indices are off by a line.
    for (source, text) in &rust_at {
        assert_eq!(
            closings(text, Delimiters::Lexical).len(),
            text.lines().count(),
            "{source}: one closing entry per line"
        );
    }

    // ── STATION 6 — the incidence, and what a leader recruits ───────────────────────────────
    let live_incidence = incidence(live_theory.iter().chain(live_rust.iter()));
    let retired_incidence = incidence(retired_theory.iter().chain(retired_rust.iter()));
    let live_features = live_incidence.keys().cloned().collect::<BTreeSet<_>>();
    let retired_features = retired_incidence.keys().cloned().collect::<BTreeSet<_>>();
    println!("\nSTATION 6 — THE INCIDENCE A LEADER RECRUITS OVER");
    println!(
        "  features               retired {}   live {}   live-only {}   retired-only {}",
        retired_features.len(),
        live_features.len(),
        live_features.difference(&retired_features).count(),
        retired_features.difference(&live_features).count()
    );
    let region = DECLARED_REGION
        .iter()
        .map(|word| (*word).to_owned())
        .collect::<BTreeSet<_>>();
    let live_recruited = union_population(&live_incidence, &region);
    let retired_recruited = union_population(&retired_incidence, &region);
    println!(
        "  leader region {region:?}\n    complete_population    retired {retired_recruited}   live {live_recruited}"
    );
    for feature in &region {
        println!(
            "    {feature:<10} retired {:>5}   live {:>5}",
            retired_incidence.get(feature).map_or(0, BTreeSet::len),
            live_incidence.get(feature).map_or(0, BTreeSet::len),
        );
    }
    // and through the library's own organ, on the same region.
    let leader = LaboratoryResearchLeader {
        identity: "the-boundary-leader".to_owned(),
        question: "what decides a section boundary".to_owned(),
        region: region.clone(),
        horizon: u64::MAX,
        generation: 0,
        caused_by_clauses: BTreeSet::new(),
    };
    let returned = atlas.enact(&leader).expect("the leader returns");
    println!(
        "    library enact          complete_population {}   sections {}   omitted {}",
        returned.complete_population,
        returned.sections.len(),
        returned.omitted_population
    );
    assert_eq!(
        returned.complete_population, live_recruited,
        "the library's union and the driver's union agree"
    );

    // ── STATION 7 — the delimiter reader against a brace counter ────────────────────────────
    println!("\nSTATION 7 — THE DELIMITER READER AGAINST A BRACE COUNTER");
    let lexical_ids = live_rust
        .iter()
        .map(|s| s.identity.clone())
        .collect::<BTreeSet<_>>();
    let naive_ids = naive_rust
        .iter()
        .map(|s| s.identity.clone())
        .collect::<BTreeSet<_>>();
    let only_lexical = lexical_ids
        .difference(&naive_ids)
        .cloned()
        .collect::<Vec<_>>();
    let only_naive = naive_ids
        .difference(&lexical_ids)
        .cloned()
        .collect::<Vec<_>>();
    println!(
        "  sections               lexical {}   naive {}   lexical-only {}   naive-only {}",
        lexical_ids.len(),
        naive_ids.len(),
        only_lexical.len(),
        only_naive.len()
    );
    assert!(
        !only_naive.is_empty() || !only_lexical.is_empty(),
        "CONTROL REFUSES ITSELF: a brace counter and a delimiter reader agreed on this material, \
         so the fixture does not exercise the distinction"
    );
    for identity in only_naive.iter().chain(only_lexical.iter()) {
        println!("    {identity}");
    }
    // the distinguishing word: the first line where the two readers' depths part.
    for (source, text) in &rust_at {
        let lexical = closings(text, Delimiters::Lexical);
        let naive = closings(text, Delimiters::NaiveBraces);
        if let Some((at, _)) = lexical
            .iter()
            .zip(naive.iter())
            .enumerate()
            .find(|(_, (a, b))| a != b)
        {
            let line = text.lines().nth(at).unwrap_or("");
            println!("  {source}:{}  {}", at + 1, line.trim());
            println!(
                "    lexical says closes={}   brace counter says closes={}",
                lexical[at], naive[at]
            );
            break;
        }
    }

    println!("\nDONE — every figure above was taken by running this driver.");
}

// ───────────────────────────────────────────────────────────────────────────────────────────
// the two laws, side by side
// ───────────────────────────────────────────────────────────────────────────────────────────

struct Section {
    identity: String,
    source: String,
    line: usize,
    text: String,
    words: usize,
    lines: usize,
    features: BTreeSet<String>,
}

impl Section {
    fn new(identity: String, source: String, line: usize, text: String) -> Section {
        let words = lexical_tokens(&text)
            .iter()
            .filter(|token| token.chars().any(char::is_alphanumeric))
            .count();
        let lines = text.lines().count();
        let mut features = text_features(&text);
        features.extend(text_features(&source));
        Section {
            identity,
            source,
            line,
            text,
            words,
            lines,
            features,
        }
    }

    fn line_at(&self, at: usize) -> &str {
        self.text.lines().nth(at).unwrap_or("")
    }
}

/// THE RETIRED THEORY LAW — `repository.rs:443` before 2026-08-09, verbatim:
/// `if !(5..=96).contains(&words) { return Ok(()) }`.
fn retired_theory_sections(source: &str, text: &str, into: &mut Vec<Section>) {
    theory_sections(source, text, into, |words| (5..=96).contains(&words));
}

/// THE LIVE THEORY LAW — a sentence is received when it carries a word.
fn live_theory_sections(source: &str, text: &str, into: &mut Vec<Section>) {
    theory_sections(source, text, into, |words| words > 0);
}

fn theory_sections(
    source: &str,
    text: &str,
    into: &mut Vec<Section>,
    admit: impl Fn(usize) -> bool + Copy,
) {
    let mut paragraph = String::new();
    let mut paragraph_line = 1usize;
    for (line_at, line) in text.lines().enumerate() {
        let line_number = line_at + 1;
        let trimmed = line.trim();
        let boundary = trimmed.is_empty()
            || trimmed.starts_with('#')
            || trimmed.starts_with("```")
            || trimmed.starts_with('|')
            || trimmed.starts_with("http://")
            || trimmed.starts_with("https://")
            || trimmed.starts_with("#let ")
            || trimmed.starts_with("#show ")
            || trimmed.starts_with('$');
        if boundary {
            paragraph_sections(source, paragraph_line, &paragraph, into, admit);
            paragraph.clear();
            paragraph_line = line_number.saturating_add(1);
            continue;
        }
        let prose = trimmed
            .strip_prefix("- ")
            .or_else(|| trimmed.strip_prefix("* "))
            .unwrap_or(trimmed);
        if paragraph.is_empty() {
            paragraph_line = line_number;
        } else {
            paragraph.push(' ');
        }
        paragraph.push_str(prose);
    }
    paragraph_sections(source, paragraph_line, &paragraph, into, admit);
}

fn paragraph_sections(
    source: &str,
    line: usize,
    paragraph: &str,
    into: &mut Vec<Section>,
    admit: impl Fn(usize) -> bool,
) {
    let mut current = Vec::<String>::new();
    let mut sentence_at = 0usize;
    let emit = |tokens: &[String], sentence_at: usize, into: &mut Vec<Section>| {
        let words = tokens
            .iter()
            .filter(|token| token.chars().any(char::is_alphanumeric))
            .count();
        if !admit(words) {
            return;
        }
        let text = render_tokens(tokens.iter().map(String::as_str));
        if text.is_empty() {
            return;
        }
        into.push(Section::new(
            format!("{source}::theory::{line}:{sentence_at}"),
            source.to_owned(),
            line,
            text,
        ));
    };
    for token in lexical_tokens(paragraph) {
        current.push(token.clone());
        if matches!(token.as_str(), "." | "!" | "?") {
            emit(&current, sentence_at, into);
            sentence_at += 1;
            current.clear();
        }
    }
    if !current.is_empty() {
        emit(&current, sentence_at, into);
    }
}

/// THE RETIRED RUST LAW — `repository.rs:467` before 2026-08-09: `const BLOCK_LINES: usize = 24`.
fn retired_rust_sections(source: &str, text: &str, into: &mut Vec<Section>) {
    let mut block = String::new();
    let mut block_start = 1usize;
    let mut block_lines = 0usize;
    for (line_at, line) in text.lines().enumerate() {
        let line_number = line_at + 1;
        let boundary = line.trim().is_empty() || block_lines == 24;
        if boundary && !block.is_empty() {
            push_rust(source, block_start, std::mem::take(&mut block), into);
            block_lines = 0;
        }
        if line.trim().is_empty() {
            continue;
        }
        if block.is_empty() {
            block_start = line_number;
        } else {
            block.push('\n');
        }
        block.push_str(line);
        block_lines += 1;
    }
    if !block.is_empty() {
        push_rust(source, block_start, block, into);
    }
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum Delimiters {
    /// the live law: comments, strings, raw strings and character literals are not delimiters.
    Lexical,
    /// the control: every `{` and `}` byte counts, wherever it sits.
    NaiveBraces,
}

/// THE LIVE RUST LAW — a blank line, or the brace depth returning to zero.
fn live_rust_sections(source: &str, text: &str, how: Delimiters, into: &mut Vec<Section>) {
    let closes = closings(text, how);
    let mut block = String::new();
    let mut block_start = 1usize;
    for (line_at, line) in text.lines().enumerate() {
        let line_number = line_at + 1;
        let boundary = line.trim().is_empty()
            || closes
                .get(line_at.wrapping_sub(1))
                .copied()
                .unwrap_or(false);
        if boundary && !block.is_empty() {
            push_rust(source, block_start, std::mem::take(&mut block), into);
        }
        if line.trim().is_empty() {
            continue;
        }
        if block.is_empty() {
            block_start = line_number;
        } else {
            block.push('\n');
        }
        block.push_str(line);
    }
    if !block.is_empty() {
        push_rust(source, block_start, block, into);
    }
}

fn push_rust(source: &str, line: usize, text: String, into: &mut Vec<Section>) {
    if text.is_empty() {
        return;
    }
    into.push(Section::new(
        format!("{source}::rust-source::{line}"),
        source.to_owned(),
        line,
        text,
    ));
}

/// One entry per line: did a top-level item END on it? Reproduces `rust_item_closings`.
fn closings(text: &str, how: Delimiters) -> Vec<bool> {
    #[derive(Clone, Copy)]
    enum Mode {
        Code,
        LineComment,
        BlockComment(usize),
        Str,
        RawStr(usize),
    }
    let bytes = text.as_bytes();
    let mut out = Vec::new();
    let mut mode = Mode::Code;
    let mut depth = 0usize;
    let mut entered = false;
    let mut at = 0usize;
    while at < bytes.len() {
        let byte = bytes[at];
        if byte == b'\n' {
            if let Mode::LineComment = mode {
                mode = Mode::Code;
            }
            out.push(entered && depth == 0);
            entered = depth > 0;
            at += 1;
            continue;
        }
        if how == Delimiters::NaiveBraces {
            if byte == b'{' {
                depth += 1;
                entered = true;
            } else if byte == b'}' {
                depth = depth.saturating_sub(1);
            }
            at += 1;
            continue;
        }
        match mode {
            Mode::LineComment => at += 1,
            Mode::BlockComment(nesting) => {
                if bytes[at..].starts_with(b"*/") {
                    mode = if nesting <= 1 {
                        Mode::Code
                    } else {
                        Mode::BlockComment(nesting - 1)
                    };
                    at += 2;
                } else if bytes[at..].starts_with(b"/*") {
                    mode = Mode::BlockComment(nesting + 1);
                    at += 2;
                } else {
                    at += 1;
                }
            }
            Mode::Str => {
                if byte == b'\\' && bytes.get(at + 1).is_some_and(|&next| next != b'\n') {
                    at += 2;
                } else {
                    if byte == b'"' {
                        mode = Mode::Code;
                    }
                    at += 1;
                }
            }
            Mode::RawStr(hashes) => {
                if byte == b'"'
                    && bytes.len() >= at + 1 + hashes
                    && bytes[at + 1..at + 1 + hashes].iter().all(|&h| h == b'#')
                {
                    mode = Mode::Code;
                    at += 1 + hashes;
                } else {
                    at += 1;
                }
            }
            Mode::Code => {
                if let Some((width, hashes)) = raw_opening(bytes, at) {
                    mode = Mode::RawStr(hashes);
                    at += width;
                } else if bytes[at..].starts_with(b"//") {
                    mode = Mode::LineComment;
                    at += 2;
                } else if bytes[at..].starts_with(b"/*") {
                    mode = Mode::BlockComment(1);
                    at += 2;
                } else if byte == b'"' {
                    mode = Mode::Str;
                    at += 1;
                } else if byte == b'\'' {
                    at += char_width(bytes, at);
                } else if byte == b'{' {
                    depth += 1;
                    entered = true;
                    at += 1;
                } else if byte == b'}' {
                    depth = depth.saturating_sub(1);
                    at += 1;
                } else {
                    at += 1;
                }
            }
        }
    }
    if !bytes.is_empty() && bytes[bytes.len() - 1] != b'\n' {
        out.push(entered && depth == 0);
    }
    out
}

fn raw_opening(bytes: &[u8], at: usize) -> Option<(usize, usize)> {
    fn identifier(byte: u8) -> bool {
        byte.is_ascii_alphanumeric() || byte == b'_' || byte >= 0x80
    }
    if at > 0 && identifier(bytes[at - 1]) {
        return None;
    }
    let mut cursor = at;
    if matches!(bytes.get(cursor), Some(b'b') | Some(b'c')) {
        cursor += 1;
    }
    if bytes.get(cursor) != Some(&b'r') {
        return None;
    }
    cursor += 1;
    let mut hashes = 0usize;
    while bytes.get(cursor) == Some(&b'#') {
        hashes += 1;
        cursor += 1;
    }
    if bytes.get(cursor) != Some(&b'"') {
        return None;
    }
    Some((cursor + 1 - at, hashes))
}

fn char_width(bytes: &[u8], at: usize) -> usize {
    match bytes.get(at + 1) {
        Some(b'\\') => {
            let mut cursor = at + 2;
            while let Some(&byte) = bytes.get(cursor) {
                if byte == b'\n' {
                    return 1;
                }
                if byte == b'\'' {
                    return cursor + 1 - at;
                }
                cursor += 1;
            }
            1
        }
        Some(b'\n') => 1,
        Some(&lead) => {
            let width = if lead < 0x80 {
                1
            } else if lead >> 5 == 0b110 {
                2
            } else if lead >> 4 == 0b1110 {
                3
            } else {
                4
            };
            if bytes.get(at + 1 + width) == Some(&b'\'') {
                2 + width
            } else {
                1
            }
        }
        None => 1,
    }
}

// ───────────────────────────────────────────────────────────────────────────────────────────

fn incidence<'a>(sections: impl Iterator<Item = &'a Section>) -> BTreeMap<String, BTreeSet<usize>> {
    let mut out = BTreeMap::<String, BTreeSet<usize>>::new();
    for (at, section) in sections.enumerate() {
        for feature in &section.features {
            out.entry(feature.clone()).or_default().insert(at);
        }
    }
    out
}

fn union_population(
    incidence: &BTreeMap<String, BTreeSet<usize>>,
    region: &BTreeSet<String>,
) -> usize {
    let mut union = BTreeSet::new();
    for feature in region {
        if let Some(sections) = incidence.get(feature) {
            union.extend(sections.iter().copied());
        }
    }
    union.len()
}

/// Every section the atlas holds, named. The atlas' own sections are private; the public face that
/// reaches all of them is a leader whose region is every feature the driver saw, with no aperture.
/// The caller checks that this region really did reach all of them against the atlas' own receipt,
/// so a region that under-reaches cannot be mistaken for agreement.
fn atlas_identities(
    atlas: &LaboratorySourceAtlas,
    region: BTreeSet<String>,
) -> (BTreeSet<String>, usize) {
    let leader = LaboratoryResearchLeader {
        identity: "the-whole-atlas".to_owned(),
        question: "every section".to_owned(),
        region,
        horizon: u64::MAX,
        generation: 0,
        caused_by_clauses: BTreeSet::new(),
    };
    let returned = atlas.enact(&leader).expect("the whole atlas returns");
    let reached = returned.complete_population;
    (
        returned
            .sections
            .into_iter()
            .map(|section| section.source_identity)
            .collect(),
        reached,
    )
}

fn relative(root: &Path, path: &Path) -> String {
    path.strip_prefix(root)
        .unwrap_or(path)
        .to_string_lossy()
        .into_owned()
}

fn repository_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(Path::parent)
        .expect("the repository root sits two above soma/life")
        .to_path_buf()
}
