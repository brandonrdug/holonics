//! Recover four foreign conditioners from their own declared statistics, condition the body with
//! each through the one seam, and ask the body which of them it can tell apart from its own reading.
//!
//! ```text
//! cargo run --release --example foreign_codec_intake -- \
//!     standing/output \
//!     reference/pureholonics-seed/src/pureholonics \
//!     reference/holobrochos-a07ff376/src/soma
//! ```
//!
//! The three paths are the deposited mathematical material and two frames of real linguistic
//! material. Every conditioner below is an **opaque law**: the recovery holds a boxed `Fn` and the
//! only admitted contact is calling it on words of the declared query family, which is exhausted
//! rather than sampled. Nothing about a conditioner's classes, emission or adjacency is supplied.
//!
//! ## The one control this driver exists for
//!
//! > **The body must be shown telling two recovered conditioners apart, naming the material that
//! > separates them, BEFORE its inability to tell a third from its own reading is read as
//! > agreement.**
//!
//! `CLAUDE.md` §8: a gauge whose group acts trivially on the declared material is not a gauge. So the
//! character-level and syllabic conditioners are run first and their distinguishing words are
//! printed; only then is the word-runs conditioner's agreement with the body's own reading admitted
//! as evidence. Every declared control is checked and the run exits nonzero if any fails.
//!
//! ## What is not claimed
//!
//! That a recovered conditioner is *correct*. It is recovered from an exhausted family and it
//! conforms on held-out real material longer than that family — both are stated. A conditioner
//! outside the declared adjacency shape is refused with its obstruction rather than approximated,
//! and that refusal is one of the controls.

use std::collections::{BTreeMap, BTreeSet};
use std::path::{Path, PathBuf};

use holonic_engine::codec_recovery::{
    Boundary, Emission, OpaqueSymbolCodec, RecoveryApertures, Symbol, SymbolAlphabet,
    SymbolSeparation, conform,
};
use holonic_engine::conditioned_derivation::{
    ConditionedBody, DerivationQuery, FoundedMorphology, MorphemicIncidence, derive, expose,
};
use holonic_engine::derivation_codec_intake::{
    CodecIntake, IntakeRefusal, MorphologyDistinction, PositionDistinction, distinguish, intake,
    present,
};

// -------------------------------------------------------------------------------------------------
// The declared query family
// -------------------------------------------------------------------------------------------------

/// The declared alphabet: the twenty-six ASCII letters and the three separators the deposited
/// identifiers and the prose both carry. Twenty-nine symbols at radius three is
/// `29 + 841 + 24389 = 25259` family words, inside the aperture this driver declares below, and
/// radius three is the shortest radius that can decide an adjacency touching a dropped class — a
/// two-symbol word carries no character for a dropped symbol's boundary to place.
fn declared_characters() -> Vec<char> {
    let mut declared: Vec<char> = ('a'..='z').collect();
    declared.extend([' ', '.', '_']);
    declared
}

/// The declared alphabet as symbols. The conditioners under test speak text; the recovery speaks
/// symbols, and this is the one translation between them.
fn alphabet() -> SymbolAlphabet {
    SymbolAlphabet::from_chars(&declared_characters()).expect("the alphabet carries no repeat")
}

const RADIUS: usize = 3;

/// **The apertures this driver declares.** They moved out of `codec_recovery` on 2026-08-09
/// (`canon/THE_AUTHORED_LEVEL.md` §5.2): neither is derivable from the material, both are statements
/// about the host, so the caller states them. 65,536 family words holds this alphabet at radius
/// three with 40,277 to spare, and the free-entry aperture bounds a `2^k` enumeration at
/// 4,096 tables. Past either the recovery refuses by name rather than sampling.
const APERTURES: RecoveryApertures = RecoveryApertures {
    family_words: 65_536,
    free_entries: 12,
};

fn is_separator(symbol: char) -> bool {
    matches!(symbol, ' ' | '.' | '_')
}

// -------------------------------------------------------------------------------------------------
// The foreign conditioners. Opaque laws; nothing below is read out of these definitions.
// -------------------------------------------------------------------------------------------------

/// *Letters agglutinate; separators are dropped and break.*
fn word_runs() -> OpaqueSymbolCodec {
    OpaqueSymbolCodec::over_text(&alphabet(), |input: &str| {
        let mut tokens = Vec::new();
        let mut current = String::new();
        for symbol in input.chars() {
            if is_separator(symbol) {
                if !current.is_empty() {
                    tokens.push(std::mem::take(&mut current));
                }
            } else {
                current.push(symbol);
            }
        }
        if !current.is_empty() {
            tokens.push(current);
        }
        tokens
    })
}

/// *Every letter is its own token; separators are dropped.* The same symbol quotient and the same
/// emission as [`word_runs`], differing in one adjacency entry — which is what makes the two
/// comparable as codecs and their separating input exact.
fn characters() -> OpaqueSymbolCodec {
    OpaqueSymbolCodec::over_text(&alphabet(), |input: &str| {
        input
            .chars()
            .filter(|symbol| !is_separator(*symbol))
            .map(|symbol| symbol.to_string())
            .collect()
    })
}

/// *A consonant run opens a token and carries the vowels after it; a vowel followed by a consonant
/// breaks.* A wholly different architecture: three classes, one of them dropped.
fn syllables() -> OpaqueSymbolCodec {
    OpaqueSymbolCodec::over_text(&alphabet(), |input: &str| {
        let vowel = |symbol: char| matches!(symbol, 'a' | 'e' | 'i' | 'o' | 'u');
        let mut tokens = Vec::new();
        let mut current = String::new();
        let mut previous: Option<char> = None;
        for symbol in input.chars() {
            let cut = match previous {
                None => true,
                Some(before) => {
                    is_separator(before)
                        || is_separator(symbol)
                        || (vowel(before) && !vowel(symbol))
                }
            };
            if cut && !current.is_empty() {
                tokens.push(std::mem::take(&mut current));
            }
            if !is_separator(symbol) {
                current.push(symbol);
            }
            previous = Some(symbol);
        }
        if !current.is_empty() {
            tokens.push(current);
        }
        tokens
    })
}

/// *Everything is one token.* Declared statistics that separate no two symbols and therefore supply
/// no relation.
fn one_class() -> OpaqueSymbolCodec {
    OpaqueSymbolCodec::over_text(&alphabet(), |input: &str| {
        if input.is_empty() {
            Vec::new()
        } else {
            vec![input.to_owned()]
        }
    })
}

// -------------------------------------------------------------------------------------------------
// Material
// -------------------------------------------------------------------------------------------------

fn material(root: &Path, extension: &str) -> Vec<PathBuf> {
    let mut found = Vec::new();
    let Ok(entries) = std::fs::read_dir(root) else {
        return found;
    };
    let mut here: Vec<PathBuf> = entries.flatten().map(|entry| entry.path()).collect();
    here.sort();
    for path in here {
        if path.is_dir() {
            found.extend(material(&path, extension));
        } else if path.extension().is_some_and(|carried| carried == extension) {
            found.push(path);
        }
    }
    found
}

fn read(root: &Path, extension: &str) -> Vec<(String, String)> {
    material(root, extension)
        .into_iter()
        .filter_map(|path| {
            std::fs::read_to_string(&path)
                .ok()
                .map(|text| (path.display().to_string(), text))
        })
        .collect()
}

// -------------------------------------------------------------------------------------------------
// Reporting
// -------------------------------------------------------------------------------------------------

fn rule(title: &str) {
    println!("\n{}", "=".repeat(98));
    println!("{title}");
    println!("{}", "=".repeat(98));
}

struct Controls {
    failed: Vec<String>,
}

impl Controls {
    fn new() -> Self {
        Self { failed: Vec::new() }
    }

    fn check(&mut self, name: &str, holds: bool, saying: &str) {
        println!(
            "  [{}] {name}\n        {saying}",
            if holds { "holds" } else { "FAILS" }
        );
        if !holds {
            self.failed.push(name.to_owned());
        }
    }
}

fn shown(text: &str) -> String {
    text.replace(' ', "\u{b7}")
}

/// One symbol, spelled through the declared alphabet. The organ carries ordinals; a reader needs
/// the identity, and this is the only place the two meet in this driver.
fn spell(symbol: Symbol) -> String {
    shown(alphabet().identity(symbol).unwrap_or("?"))
}

/// The symbol a declared character stands for.
fn symbol_for(character: char) -> Symbol {
    alphabet()
        .symbol_of(character.to_string().as_str())
        .expect("the character is declared")
}

/// A word, spelled.
fn spell_word(word: &[Symbol]) -> String {
    word.iter().copied().map(spell).collect()
}

fn print_relations(carried: &CodecIntake) {
    let relations = &carried.relations;
    println!(
        "\n  {} -- recovered from testimony alone",
        carried.conditioner
    );
    println!(
        "    declared family: {} symbols, radius {}, exhausted -- {} words, {} calls",
        relations.alphabet.len(),
        relations.radius,
        relations.work.declared_family_words,
        relations.work.target_calls
    );

    println!("\n    the symbol quotient, and what each class emits");
    for (representative, emission) in &relations.emission {
        let block = relations
            .classes
            .iter()
            .find(|block| block.contains(representative))
            .expect("every representative names a class");
        let members: String = block.iter().map(|symbol| spell(*symbol)).collect();
        println!(
            "      class {:?}  {:<5}  {{{}}}",
            spell(*representative),
            match emission {
                Emission::Emit => "Emit",
                Emission::Drop => "Drop",
            },
            members
        );
    }

    println!(
        "\n    the separation relation -- each pair with the SHORTEST context that separates it"
    );
    println!("    grouped by the class pair it lands in; every separated symbol pair is named");
    let mut species: BTreeMap<(Symbol, Symbol), Vec<&SymbolSeparation>> = BTreeMap::new();
    for separation in &relations.separations {
        let left = relations
            .representative_of(separation.left)
            .unwrap_or(separation.left);
        let right = relations
            .representative_of(separation.right)
            .unwrap_or(separation.right);
        species
            .entry((left.min(right), left.max(right)))
            .or_default()
            .push(separation);
    }
    for ((left, right), members) in &species {
        let first = members[0];
        println!(
            "      class {:?} apart from class {:?}   shortest context {:?}^{:?}",
            spell(*left),
            spell(*right),
            spell_word(&first.prefix),
            spell_word(&first.suffix)
        );
        println!(
            "        exhibited at {:?}|{:?}  ->  {:?} vs {:?}",
            spell(first.left),
            spell(first.right),
            first.left_return,
            first.right_return
        );
        let pairs: Vec<String> = members
            .iter()
            .map(|separation| format!("{}|{}", spell(separation.left), spell(separation.right)))
            .collect();
        for chunk in pairs.chunks(16) {
            println!("        {}", chunk.join(" "));
        }
    }

    println!("\n    the adjacency relation -- which classes agglutinate");
    for entry in &relations.adjacency {
        println!(
            "      {:?} -> {:?}   {}",
            spell(entry.left),
            spell(entry.right),
            match entry.boundary {
                Boundary::Join => "Join",
                Boundary::Cut => "Cut",
            }
        );
    }
    if relations.gauge_freedom.is_empty() {
        println!("\n    no adjacency entry is left free by the declared family");
    } else {
        println!("\n    adjacency entries no input of any length decides -- a freedom, reported:");
        for (left, right) in &relations.gauge_freedom {
            println!("      {:?} -> {:?}", spell(*left), spell(*right));
        }
    }

    println!("\n    retained obstruction -- declared symbols this conditioner emits nothing for:");
    println!(
        "      {}",
        carried
            .retained
            .dropped
            .iter()
            .map(|symbol| format!("{:?}", spell(*symbol)))
            .collect::<Vec<String>>()
            .join(" ")
    );
}

fn print_covers(name: &str, morphology: &FoundedMorphology, identifiers: &BTreeSet<String>) {
    println!("\n  the founded cover of every recruited identifier under `{name}`");
    println!("  a bracketed character is material this conditioner committed no stem for");
    for identifier in identifiers {
        match morphology.cover(identifier) {
            Ok(cover) => println!("    {identifier:<22} {}", cover.render()),
            Err(refusal) => println!("    {identifier:<22} refused: {refusal}"),
        }
    }
}

/// One direction of a distinction, exhibited by its **species** — the distinguishing word and the
/// founded stem that saw it — with one pair of identifier positions carrying each. The species is
/// the artifact; the pair is the material that produced it.
fn exhibit_species(population: &str, entries: &[PositionDistinction]) {
    let mut species: BTreeMap<(Option<&str>, Option<&str>), &PositionDistinction> = BTreeMap::new();
    for entry in entries {
        species
            .entry((
                entry.distinguishing_word.as_deref(),
                entry.witness_stem.as_deref(),
            ))
            .or_insert(entry);
    }
    if species.is_empty() {
        println!("    {population}: nothing");
        return;
    }
    println!("    {population}:");
    for ((word, stem), representative) in &species {
        println!(
            "      word {:<12} stem {:<14} e.g. {} | {}",
            match word {
                Some("") => "\"\" (visible without transport)".to_owned(),
                Some(word) => format!("{:?}", shown(word)),
                None => "(none ever)".to_owned(),
            },
            match stem {
                Some(stem) => format!("{stem:?}"),
                None => "(terminus)".to_owned(),
            },
            representative.left,
            representative.right
        );
    }
}

/// Exhibit a distinction in both directions, with every distinguishing word and every witnessing
/// stem named.
fn print_distinction(distinction: &MorphologyDistinction) {
    println!("\n  `{}` against `{}`", distinction.left, distinction.right);
    if distinction.indistinguishable() {
        println!(
            "    the body's reading of the deposited identifiers separates NOTHING differently"
        );
        println!("    -- no position pair, in either direction");
        return;
    }

    exhibit_species(
        "the right reading separates what the left merges",
        &distinction.right_separates,
    );
    exhibit_species(
        "the left reading separates what the right merges",
        &distinction.left_separates,
    );

    let words: Vec<String> = distinction
        .distinguishing_words()
        .into_iter()
        .map(|word| format!("{:?}", shown(word)))
        .collect();
    println!(
        "    every distinguishing word exhibited: {}",
        words.join(" ")
    );
    let stems: Vec<String> = distinction
        .witness_stems()
        .into_iter()
        .map(|stem| format!("{stem:?}"))
        .collect();
    println!(
        "    every witnessing stem exhibited:     {}",
        stems.join(" ")
    );

    for (name, population) in [
        ("only the left founded", &distinction.only_left_reaching),
        ("only the right founded", &distinction.only_right_reaching),
    ] {
        if population.is_empty() {
            continue;
        }
        println!("    committed stems {name}, that reach this material:");
        for firing in population.iter().take(12) {
            println!("      {:<14} {}", firing.stem, firing.positions.join("  "));
        }
        if population.len() > 12 {
            println!("      ... and the rest are carried in the returned population");
        }
    }
}

fn print_refusal(name: &str, refusal: &IntakeRefusal) {
    println!("\n  {name}");
    println!("    refused, by type: {refusal}");
    match refusal {
        IntakeRefusal::NoRelationRecovered { classes } => {
            for block in classes {
                let members: String = block.iter().map(|symbol| spell(*symbol)).collect();
                println!("      the one class it returned: {{{members}}}");
            }
        }
        IntakeRefusal::NoFoundedWord { wholes } => {
            for whole in wholes.iter().take(4) {
                println!("      presented and founded nothing: {whole}");
            }
        }
        IntakeRefusal::NoCommittedStem { founded } => {
            println!(
                "      founded, and none recurred across two wholes: {}",
                founded
                    .iter()
                    .take(8)
                    .map(|word| format!("{word:?}"))
                    .collect::<Vec<String>>()
                    .join(" ")
            );
        }
        other => println!("      {other:?}"),
    }
}

// -------------------------------------------------------------------------------------------------

fn main() {
    let arguments: Vec<String> = std::env::args().skip(1).collect();
    let deposit_root = PathBuf::from(
        arguments
            .first()
            .cloned()
            .unwrap_or_else(|| "standing/output".to_owned()),
    );
    let corpus_roots: Vec<PathBuf> = if arguments.len() > 1 {
        arguments[1..].iter().map(PathBuf::from).collect()
    } else {
        vec![
            PathBuf::from("reference/pureholonics-seed/src/pureholonics"),
            PathBuf::from("reference/holobrochos-a07ff376/src/soma"),
        ]
    };

    let deposit = read(&deposit_root, "lean");
    let mut corpus: Vec<(String, String)> = Vec::new();
    for root in &corpus_roots {
        corpus.extend(read(root, "md"));
    }
    if deposit.is_empty() || corpus.is_empty() {
        eprintln!(
            "no material: {} lean artifact(s) under {}, {} whole(s) of prose",
            deposit.len(),
            deposit_root.display(),
            corpus.len()
        );
        std::process::exit(2);
    }

    let body = match ConditionedBody::mount(deposit.clone()) {
        Ok(body) => body,
        Err(refusal) => {
            eprintln!("the deposit was refused: {refusal}");
            std::process::exit(2);
        }
    };
    let identifiers = body.recruited_population();
    let native = FoundedMorphology::condition(
        &corpus
            .iter()
            .map(|(whole, text)| expose(whole, text))
            .collect::<Vec<_>>(),
    );

    let declared = alphabet();
    let declared_set: BTreeSet<char> = declared_characters().into_iter().collect();
    let mut controls = Controls::new();

    rule("FOREIGN CODEC INTAKE -- recovered relations entering the conditioning path");
    println!("\nmaterial");
    println!(
        "  mathematical   {:<52} {} artifacts",
        deposit_root.display(),
        deposit.len()
    );
    for root in &corpus_roots {
        println!(
            "  linguistic     {:<52} {} wholes",
            root.display(),
            read(root, "md").len()
        );
    }
    println!("\nthe deposit recruits {} identifiers:", identifiers.len());
    for identifier in &identifiers {
        println!("    {identifier}");
    }

    // ---------------------------------------------------------------------------------------------
    rule("[1]  THE RELATIONS -- derived from each conditioner's own declared statistics");
    // ---------------------------------------------------------------------------------------------

    let runs = match intake(
        "word-runs",
        &word_runs(),
        &declared,
        RADIUS,
        APERTURES,
        &corpus,
    ) {
        Ok(carried) => carried,
        Err(refusal) => {
            eprintln!("the word-runs conditioner was refused: {refusal}");
            std::process::exit(2);
        }
    };
    let chars = match intake(
        "characters",
        &characters(),
        &declared,
        RADIUS,
        APERTURES,
        &corpus,
    ) {
        Ok(carried) => carried,
        Err(refusal) => {
            eprintln!("the character conditioner was refused: {refusal}");
            std::process::exit(2);
        }
    };
    let syllabic = match intake(
        "syllables",
        &syllables(),
        &declared,
        RADIUS,
        APERTURES,
        &corpus,
    ) {
        Ok(carried) => carried,
        Err(refusal) => {
            eprintln!("the syllabic conditioner was refused: {refusal}");
            std::process::exit(2);
        }
    };

    for carried in [&runs, &chars, &syllabic] {
        print_relations(carried);
    }

    controls.check(
        "relations-returned",
        [&runs, &chars, &syllabic]
            .iter()
            .all(|carried| !carried.relations.separations.is_empty()),
        "every conditioner returned a non-empty separation relation on this alphabet",
    );
    controls.check(
        "every-separation-carries-its-context",
        [&runs, &chars, &syllabic].iter().all(|carried| {
            carried
                .relations
                .separations
                .iter()
                .all(|separation| separation.left_return != separation.right_return)
        }),
        "each separated pair carries the context that separates it and both returns at it",
    );
    let syllabic_boundary = |left: char, right: char| {
        syllabic
            .relations
            .adjacency
            .iter()
            .find(|entry| (entry.left, entry.right) == (symbol_for(left), symbol_for(right)))
            .map(|entry| entry.boundary)
    };
    controls.check(
        "the-adjacency-relation-is-ordered",
        syllabic_boundary('b', 'a') == Some(Boundary::Join)
            && syllabic_boundary('a', 'b') == Some(Boundary::Cut)
            && syllabic.relations.adjacency.iter().all(|entry| {
                Some(entry.boundary) == syllabic.codec.boundary_between(entry.left, entry.right)
            }),
        "a consonant carries the vowel after it and a vowel breaks before a consonant -- the \
         transpose is a different relation, and the report agrees with the runner",
    );
    controls.check(
        "the-vowel-class-was-recovered-and-not-declared",
        syllabic.relations.classes.len() == 3
            && syllabic
                .relations
                .classes
                .iter()
                .any(|block| {
                    *block
                        == ['a', 'e', 'i', 'o', 'u']
                            .into_iter()
                            .map(symbol_for)
                            .collect::<BTreeSet<Symbol>>()
                }),
        "the syllabic conditioner's vowel class came out of testimony; no vowel was ever named to it",
    );

    // ---------------------------------------------------------------------------------------------
    rule("[2]  THE REFUSALS -- typed, never an empty return");
    // ---------------------------------------------------------------------------------------------

    let no_relation = intake(
        "one-class",
        &one_class(),
        &declared,
        RADIUS,
        APERTURES,
        &corpus,
    );
    match &no_relation {
        Ok(_) => println!("\n  one-class: RECOVERED, which it must not be"),
        Err(refusal) => print_refusal(
            "one-class -- statistics that separate no two symbols",
            refusal,
        ),
    }
    controls.check(
        "refusal-no-relation",
        matches!(no_relation, Err(IntakeRefusal::NoRelationRecovered { .. })),
        "a conditioner whose statistics separate nothing is refused by type, not returned empty",
    );

    let absent = SymbolAlphabet::from_chars(&['\u{2603}', '\u{2604}', ' '])
        .expect("the absent alphabet carries no repeat");
    let no_word = intake(
        "word-runs",
        &word_runs(),
        &absent,
        RADIUS,
        APERTURES,
        &corpus,
    );
    match &no_word {
        Ok(_) => println!("\n  absent-alphabet: RECOVERED, which it must not be"),
        Err(refusal) => print_refusal(
            "word-runs over an alphabet the real material does not carry",
            refusal,
        ),
    }
    controls.check(
        "refusal-no-founded-word",
        matches!(no_word, Err(IntakeRefusal::NoFoundedWord { .. })),
        "material carrying no declared symbol founds nothing and is refused by type",
    );

    let single = corpus[..1].to_vec();
    let no_commitment = intake(
        "word-runs",
        &word_runs(),
        &declared,
        RADIUS,
        APERTURES,
        &single,
    );
    match &no_commitment {
        Ok(_) => println!("\n  single-whole: RECOVERED, which it must not be"),
        Err(refusal) => print_refusal(
            "word-runs on one whole -- nothing can recur across two distinct sources",
            refusal,
        ),
    }
    controls.check(
        "refusal-no-committed-stem",
        matches!(no_commitment, Err(IntakeRefusal::NoCommittedStem { .. })),
        "a population no second whole witnessed commits nothing and is refused by type",
    );

    // ---------------------------------------------------------------------------------------------
    rule("[3]  THE READING -- each recovered conditioner's cover of the deposited identifiers");
    // ---------------------------------------------------------------------------------------------

    print_covers("native (the body's own `expose`)", &native, &identifiers);
    for carried in [&runs, &chars, &syllabic] {
        print_covers(&carried.conditioner, &carried.morphology, &identifiers);
    }

    // ---------------------------------------------------------------------------------------------
    rule("[4]  THE GAUGE ACTS -- two conditioners the body tells apart, with the material");
    // ---------------------------------------------------------------------------------------------

    let against_chars = distinguish(
        &identifiers,
        ("native", &native),
        ("characters", &chars.morphology),
    )
    .expect("the recruited identifiers are ASCII");
    let against_syllabic = distinguish(
        &identifiers,
        ("native", &native),
        ("syllables", &syllabic.morphology),
    )
    .expect("the recruited identifiers are ASCII");

    print_distinction(&against_chars);
    print_distinction(&against_syllabic);

    controls.check(
        "gauge-acts",
        !against_chars.indistinguishable() && !against_syllabic.indistinguishable(),
        "the distinction instrument returns a non-empty population on this exact material",
    );
    controls.check(
        "every-separation-names-a-witness-or-a-word",
        [&against_chars, &against_syllabic].iter().all(|distinction| {
            distinction
                .right_separates
                .iter()
                .chain(distinction.left_separates.iter())
                .all(|entry| entry.witness_stem.is_some() || entry.distinguishing_word.is_some())
        }),
        "no separated pair is reported without either the stem that saw it or the word that shows it",
    );

    // ---------------------------------------------------------------------------------------------
    rule("[5]  THE AGREEMENT -- admissible only now that the gauge has been shown to act");
    // ---------------------------------------------------------------------------------------------

    let against_runs = distinguish(
        &identifiers,
        ("native", &native),
        ("word-runs", &runs.morphology),
    )
    .expect("the recruited identifiers are ASCII");
    print_distinction(&against_runs);

    let mut words_agree = true;
    let mut departure: Option<String> = None;
    for (whole, text) in &corpus {
        let native_words = expose(whole, text).words;
        let presented = present(whole, text, &declared_set);
        let recovered: Vec<String> = presented
            .runs
            .iter()
            .flat_map(|run| {
                let word = declared.spell(run).expect("a presented run is declared");
                runs.codec
                    .segment(&word)
                    .expect("declared symbols only")
                    .into_iter()
                    .map(|token| declared.render(&token))
                    .collect::<Vec<_>>()
            })
            .collect();
        if recovered != native_words {
            words_agree = false;
            departure = Some(whole.clone());
        }
    }
    println!("\n  word for word, whole by whole, on the real corpus:");
    match &departure {
        None => println!(
            "    the recovered `word-runs` conditioner founds exactly the words `expose` founds"
        ),
        Some(whole) => println!("    departs on {whole}"),
    }
    println!(
        "    committed populations equal: {}",
        runs.morphology.committed_stems() == native.committed_stems()
    );
    println!("    the one difference, and no conduct path reads it:");
    let sampled = runs
        .morphology
        .founded()
        .iter()
        .find(|stem| stem.stem == "carrier")
        .or_else(|| runs.morphology.founded().first());
    if let Some(stem) = sampled {
        println!("      stem {:?} foreign lineage:", stem.stem);
        for entry in &stem.foreign_lineage {
            println!("        {entry}");
        }
        let own = native.stem(&stem.stem);
        println!(
            "      the natively founded stem of the same word carries lineage: {:?}",
            own.map(|stem| stem.foreign_lineage.clone())
                .unwrap_or_default()
        );
    }

    controls.check(
        "words-identical",
        words_agree,
        "the recovered conditioner's words are the body's own words, in order, whole by whole",
    );
    controls.check(
        "indistinguishable",
        against_runs.indistinguishable()
            && against_runs.only_left_reaching.is_empty()
            && against_runs.only_right_reaching.is_empty(),
        "the body's reading of the deposited identifiers cannot tell the two apart",
    );

    println!("\n  WHERE THE EVIDENCE ACTUALLY IS, stated because `CLAUDE.md` §8 requires it:");
    println!(
        "    these two morphologies commit the SAME stems, so `indistinguishable` above could"
    );
    println!(
        "    not have come out otherwise and carries no evidence by itself. The measurement is"
    );
    println!("    `words-identical`, one line up: a boundary table recovered from 25259 black-box");
    println!(
        "    returns cut 945 KB of real prose into the body's own words and could easily have"
    );
    println!("    failed. The next section is what makes the instrument's empty return mean");
    println!(
        "    something -- there the populations really differ and it still decides, both ways."
    );

    // ---------------------------------------------------------------------------------------------
    rule("[5b] THE DISTINCTION ANSWERS TO STRUCTURE -- one removal each way");
    // ---------------------------------------------------------------------------------------------

    let reaching: Vec<String> = MorphemicIncidence::over(&identifiers, &native)
        .expect("the recruited identifiers are ASCII")
        .firing()
        .into_iter()
        .map(|firing| firing.stem)
        .collect();
    let reaches: BTreeSet<&str> = reaching.iter().map(String::as_str).collect();

    let unreached = native
        .committed_stems()
        .into_iter()
        .find(|stem| !reaches.contains(*stem))
        .map(str::to_owned);
    let quiet = unreached.as_ref().and_then(|stem| {
        let without = native.without_stem(stem)?;
        distinguish(
            &identifiers,
            ("native", &native),
            ("native less that stem", &without),
        )
        .ok()
        .map(|distinction| (stem.clone(), distinction))
    });
    match &quiet {
        Some((stem, distinction)) => {
            println!("\n  removed a committed stem that reaches nothing here: {stem:?}");
            println!("    the founded populations now differ by that named member");
            println!(
                "    the reading: {}",
                if distinction.indistinguishable() {
                    "unchanged, in both directions"
                } else {
                    "MOVED, which it must not have"
                }
            );
        }
        None => println!("\n  no committed stem reaches nothing here"),
    }

    let moved = reaching.iter().take(8).find_map(|stem| {
        let without = native.without_stem(stem)?;
        let distinction = distinguish(
            &identifiers,
            ("native", &native),
            ("native less that stem", &without),
        )
        .ok()?;
        (!distinction.indistinguishable()).then_some((stem.clone(), distinction))
    });
    match &moved {
        Some((stem, distinction)) => {
            println!("\n  removed a committed stem that does reach here: {stem:?}");
            println!(
                "    -- the first such stem in canonical order whose removal moves the reading"
            );
            print_distinction(distinction);
        }
        None => println!("\n  no removal among the first reaching stems moved the reading"),
    }

    controls.check(
        "removal-of-an-unreaching-stem-leaves-the-reading",
        quiet
            .as_ref()
            .is_some_and(|(_, distinction)| distinction.indistinguishable()),
        "populations that differ by a member the material never exercises read alike",
    );
    controls.check(
        "removal-of-a-reaching-stem-moves-the-reading",
        moved.as_ref().is_some_and(|(_, distinction)| {
            !distinction.indistinguishable()
                && (!distinction.witness_stems().is_empty()
                    || !distinction.distinguishing_words().is_empty())
        }),
        "removing structure removes later conduct, and the instrument names what shows it",
    );

    // ---------------------------------------------------------------------------------------------
    rule("[6]  THE CONDITIONERS ARE DISTINCT OBJECTS -- exactly, over all inputs");
    // ---------------------------------------------------------------------------------------------

    let separating = runs
        .codec
        .shortest_separating_input(&chars.codec)
        .expect("the two codecs share their classes and emission");
    match &separating {
        None => println!("\n  no input of any length separates `word-runs` from `characters`"),
        Some(input) => {
            println!(
                "\n  the shortest input separating `word-runs` from `characters`: {:?}",
                spell_word(input)
            );
            println!(
                "    word-runs  -> {:?}",
                runs.codec
                    .segment(input)
                    .expect("declared symbols only")
                    .iter()
                    .map(|token| spell_word(token))
                    .collect::<Vec<_>>()
            );
            println!(
                "    characters -> {:?}",
                chars
                    .codec
                    .segment(input)
                    .expect("declared symbols only")
                    .iter()
                    .map(|token| spell_word(token))
                    .collect::<Vec<_>>()
            );
        }
    }
    let self_separating = runs
        .codec
        .shortest_separating_input(&runs.codec)
        .expect("a codec is comparable with itself");
    println!(
        "    and against itself: {}",
        match &self_separating {
            None => "none, which is a proof of identity over ALL inputs".to_owned(),
            Some(input) => format!("{input:?}, which would be a defect"),
        }
    );
    controls.check(
        "codecs-are-distinct",
        separating
            .as_ref()
            .is_some_and(|input| runs.codec.segment(input).ok() != chars.codec.segment(input).ok())
            && self_separating.is_none(),
        "the agreeing conditioner and the distinguished one are two objects, not one twice",
    );

    // The recovered structure runs on real material longer than anything the family reached.
    let mut held_out: Vec<String> = Vec::new();
    for (whole, text) in corpus.iter().take(2) {
        held_out.extend(
            present(whole, text, &declared_set)
                .runs
                .into_iter()
                .filter(|run| run.chars().count() > RADIUS),
        );
    }
    let borrowed: Vec<Vec<Symbol>> = held_out
        .iter()
        .map(|run| declared.spell(run).expect("a presented run is declared"))
        .collect();
    let conformance = conform(&runs.codec, &word_runs(), &borrowed);
    let widest = borrowed
        .iter()
        .map(|run| runs.codec.segment(run).map_or(0, |tokens| tokens.len()))
        .max()
        .unwrap_or(0);
    println!(
        "\n  conformance on held-out real runs longer than the family, widest return {widest} tokens"
    );
    if conformance.is_exact() {
        println!("    exact -- the recovered structure is a machine, not retained testimony");
    } else {
        for disagreement in conformance.disagreements.iter().take(4) {
            println!(
                "    {:?}: conditioner {:?} recovered {:?}",
                spell_word(&disagreement.input),
                disagreement.target,
                disagreement.recovered
            );
        }
    }
    controls.check(
        "conformance-exact",
        conformance.is_exact() && widest >= 12,
        "the recovered structure agrees with the opaque conditioner past the exhausted family",
    );

    // ---------------------------------------------------------------------------------------------
    rule("[7]  THE PRODUCTION -- the seam is the causal path, not a second reading");
    // ---------------------------------------------------------------------------------------------

    let statements = body.standing_statements();
    let query = DerivationQuery::reaching(
        statements
            .iter()
            .next()
            .expect("the deposit reached a statement"),
    );
    println!("\n  query: {}", query.statement);

    let names = |morphology: &FoundedMorphology| -> Vec<String> {
        derive(&body.standing_derivations(), morphology, &query)
            .expect("the recruited identifiers are ASCII")
            .into_iter()
            .map(|passage| passage.name)
            .collect()
    };
    let unconditioned = names(&FoundedMorphology::unconditioned());
    let own = names(&native);
    let carried = names(&runs.morphology);
    let elsewhere = names(&chars.morphology);
    let syllabic_names = names(&syllabic.morphology);

    for (name, population) in [
        ("unconditioned", &unconditioned),
        ("native", &own),
        ("word-runs (recovered)", &carried),
        ("characters (recovered)", &elsewhere),
        ("syllables (recovered)", &syllabic_names),
    ] {
        println!("\n    {name}");
        if population.is_empty() {
            println!("      (empty -- no stem bridges two recruited identifiers)");
        }
        for passage in population.iter().take(6) {
            println!("      {passage}");
        }
        if population.len() > 6 {
            println!("      ... and the rest are carried in the returned population");
        }
    }

    controls.check(
        "production-carried",
        !carried.is_empty() && carried == own,
        "a morphology carried across the seam drives the production the native one drives",
    );
    controls.check(
        "production-differs",
        !elsewhere.is_empty() && elsewhere != own && syllabic_names != own,
        "a different recovered conditioner reaches a different production",
    );
    controls.check(
        "unconditioned-produces-nothing",
        unconditioned.is_empty(),
        "a body exposed to nothing holds no stem that can bridge two identifiers",
    );

    // ---------------------------------------------------------------------------------------------
    rule("DECLARED CONTROLS");
    // ---------------------------------------------------------------------------------------------
    if controls.failed.is_empty() {
        println!("\n  every declared control holds.");
    } else {
        println!("\n  FAILED: {}", controls.failed.join(", "));
        std::process::exit(1);
    }
}
