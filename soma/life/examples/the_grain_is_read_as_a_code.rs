//! **Step 0 of the Eros cycle: three readings, taken before construction.**
//!
//! The standing plan is `blueprint/THE_ROADMAP.md` §"THE EROS CYCLE". This driver
//! takes the first of its three readings and nothing else. It builds no organ,
//! claims no capability, and grades no deed.
//!
//! # What is being read
//!
//! `decomposing_codec` already is the codec pivot the compression tablet
//! defines. Its **grain** is a set of words after which the decomposer closes a
//! part, and by its own header the grain *"is the reusable morphology — what the
//! decomposer does to material it has never seen is completely determined by
//! it."* `revise()` moves the grain by cutting at each collapsed pair's own
//! distinguishing word.
//!
//! So the question this driver reads, and only reads:
//!
//! ```text
//! held-out material B, cut and scored under the PARENT grain
//! held-out material B, cut and scored under the REVISED grain
//! what does SymbolicSurprisal::compare return between the two?
//! ```
//!
//! # Why every outcome is information
//!
//! `surprisal.rs:44-49` states the property that decides how this must be
//! reported: *"Vanishing and equality are decided EXACTLY, with no enclosure…
//! It is why `S(P) = S(Q)` is decidable here while `S(P) < S(Q)` is not."*
//!
//! - The **difference form** is exact and is the primary return. It cannot be
//!   `Open`, and it is the additive invariant the compression tablet demands.
//! - A **direction** is a secondary reading taken at a declared grain, and an
//!   `Open` there is a statement about how close the two forms are on this
//!   material — which locates the grain a later reading needs.
//!
//! # What this driver is NOT
//!
//! Not a compression claim. *"Reduced founding cost is compression"* was
//! regraded 2026-07-19: it measures recurrence, reuse and amortization. Not a
//! learning claim: the deposit-changes-later-conduct chain is `established` and
//! is this plan's **carrier**, never its return. The open grade is a later
//! **nonidentical** neighbourhood, and this driver does not reach for it.
//!
//! The collapsed-pair population is primary throughout; the exact form is its
//! magnitude face, printed beside it and never instead of it.
//!
//! ```text
//! cargo run --release -p life --example the_grain_is_read_as_a_code
//! ```

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::surprisal::{cross_entropy, Grain, Support, SymbolicSurprisal};
use life::decomposing_codec::{
    read, render_word, DecomposingBody, DecompositionGrain, DecompositionPass, Symbol,
};
use num_bigint::BigUint;

/// The declared material. Real records from this repository, never a fixture.
const CONDITIONING: [&str; 3] = [
    "research/records/2026-08-14_COMPRESSION_IS_A_CODEC_PIVOT_THE_INVARIANCE_IS_ADDITIVE_AND_NOTHING_PRICES_BOTH_AXES.md",
    "research/records/2026-08-13_THE_CUT_BECOMES_THE_CODECS_AND_THE_LATER_CURRENT_RIDES_THE_DEPOSIT.md",
    "research/records/2026-08-13_SCALING_IS_REPETITION_OF_AN_INVARIANT_UNIT_AND_THE_GENERATOR_IS_THE_COMPACT_REPRESENTATIVE.md",
];

/// Held out. Named as held out before the run, and it conditions nothing.
const HELD_OUT: &str = "canon/TABLET_THE_COMPRESSION.md";

/// The second held-out body, whose subject shares no vocabulary with the
/// conditioning material. The keystone control: if BOTH bodies move, the
/// revision was a global normalisation rather than changed terrain.
const HELD_OUT_DISJOINT: &str = "canon/TABLET_THE_MANIFOLD.md";

fn words_of(path: &str) -> Vec<Vec<Symbol>> {
    let text = std::fs::read_to_string(path)
        .unwrap_or_else(|error| panic!("the declared material must be present: {path}: {error}"));
    text.lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| line.bytes().map(Symbol).collect())
        .collect()
}

/// The part multiset of a pass. `DecompositionPass::parts` returns the SET; the
/// multiset is what a population is, and it is reachable because `decomposed`
/// and `parts` are both public. Step 1 of the plan is a getter for exactly this.
fn multiset(pass: &DecompositionPass) -> BTreeMap<Vec<Symbol>, BigUint> {
    let mut counted: BTreeMap<Vec<Symbol>, BigUint> = BTreeMap::new();
    for whole in &pass.decomposed {
        for part in &whole.parts {
            *counted.entry(part.clone()).or_insert_with(BigUint::default) += 1u32;
        }
    }
    counted
}

/// The event table, DERIVED from the union of every population in play and
/// never authored. A returned integer would be a receiver coordinate promoted
/// into the artifact, so the members are carried by name and the ids are local
/// to this reading.
fn event_table(populations: &[&BTreeMap<Vec<Symbol>, BigUint>]) -> BTreeMap<Vec<Symbol>, u64> {
    let mut union: BTreeSet<Vec<Symbol>> = BTreeSet::new();
    for population in populations {
        union.extend(population.keys().cloned());
    }
    union
        .into_iter()
        .enumerate()
        .map(|(at, word)| (word, at as u64))
        .collect()
}

fn addressed(
    population: &BTreeMap<Vec<Symbol>, BigUint>,
    table: &BTreeMap<Vec<Symbol>, u64>,
) -> BTreeMap<u64, BigUint> {
    population
        .iter()
        .filter_map(|(word, count)| table.get(word).map(|event| (*event, count.clone())))
        .collect()
}

/// How many of the held-out population's events the standing code has never
/// seen. Reported BESIDE the reading, never behind it — it is the founding half
/// of the two-part account.
fn unsupported_population(
    population: &BTreeMap<Vec<Symbol>, BigUint>,
    code: &BTreeMap<Vec<Symbol>, BigUint>,
) -> Vec<Vec<Symbol>> {
    population
        .keys()
        .filter(|word| !code.contains_key(*word))
        .cloned()
        .collect()
}

struct Reading {
    parts: usize,
    distinct: usize,
    collapsed: usize,
    unsupported: Vec<Vec<Symbol>>,
    form: Option<SymbolicSurprisal>,
}

fn score(
    grain: &DecompositionGrain,
    code_material: &[Vec<Symbol>],
    held_out: &[Vec<Symbol>],
) -> Reading {
    let code_pass = read(grain, code_material).expect("the conditioning material reads");
    let held_pass = read(grain, held_out).expect("the held-out material reads");
    let code = multiset(&code_pass);
    let population = multiset(&held_pass);
    let table = event_table(&[&code, &population]);
    let unsupported = unsupported_population(&population, &code);
    let form = match cross_entropy(&addressed(&population, &table), &addressed(&code, &table)) {
        Ok(Support::Supported(form)) => Some(form),
        Ok(Support::Unsupported) => None,
        Err(error) => panic!("the surprisal carrier refused: {error}"),
    };
    Reading {
        parts: population
            .values()
            .map(|count| count.to_string().parse::<usize>().unwrap_or(0))
            .sum(),
        distinct: population.len(),
        collapsed: held_pass.collapsed().len(),
        unsupported,
        form,
    }
}

fn report(name: &str, reading: &Reading) {
    println!(
        "  {name:<26} parts {:>7}   distinct {:>6}   collapsed pairs {:>5}   unsupported {:>6}",
        reading.parts,
        reading.distinct,
        reading.collapsed,
        reading.unsupported.len()
    );
    match &reading.form {
        Some(form) => println!("      form   {}", form.named()),
        None => println!(
            "      form   UNSUPPORTED for the whole reading -- the aggregate collapsed on the \
             first novel event"
        ),
    }
}

fn main() {
    println!("{}", "=".repeat(100));
    println!("STEP 0 -- THE GRAIN IS READ AS A CODE");
    println!("{}", "=".repeat(100));
    println!();
    println!("  This driver READS. It builds nothing, claims nothing, and grades no deed.");
    println!();

    let conditioning: Vec<Vec<Symbol>> = CONDITIONING.iter().flat_map(|p| words_of(p)).collect();
    let held_out = words_of(HELD_OUT);
    let disjoint = words_of(HELD_OUT_DISJOINT);

    println!(
        "  conditioning material   {} lines over {} records",
        conditioning.len(),
        CONDITIONING.len()
    );
    println!(
        "  held out                {} lines   {HELD_OUT}",
        held_out.len()
    );
    println!(
        "  held out, disjoint      {} lines   {HELD_OUT_DISJOINT}",
        disjoint.len()
    );
    println!();

    // The origin grain: close a part after a space. Declared, and the only
    // authored thing in the run.
    let origin = DecompositionGrain::declare([vec![Symbol(b' ')]]).expect("a non-empty grain");

    println!("{}", "-".repeat(100));
    println!("UNDER THE PARENT GRAIN");
    println!("{}", "-".repeat(100));
    println!("  grain   {} cut word(s)", origin.cuts().len());
    let before = score(&origin, &conditioning, &held_out);
    let before_disjoint = score(&origin, &conditioning, &disjoint);
    report(HELD_OUT, &before);
    report(HELD_OUT_DISJOINT, &before_disjoint);

    // The deposit: condition on A, then revise at the collapsed pairs' own words.
    let mut body = DecomposingBody::mount(origin.clone()).expect("the body mounts");
    body.receive(conditioning.clone())
        .expect("the batch is received");
    let revision = body.revise().expect("the pass opened a reflection");
    let revised = revision.grain.clone();

    println!();
    println!("{}", "-".repeat(100));
    println!("THE DEPOSIT");
    println!("{}", "-".repeat(100));
    println!(
        "  founded {} codec version(s); grain {} -> {} cut words",
        revision.founded.len(),
        origin.cuts().len(),
        revised.cuts().len()
    );
    for founded in revision.founded.iter().take(12) {
        println!(
            "      cut at {:<24} founded by the pair separated by {}",
            render_word(&founded.word),
            render_word(&founded.word)
        );
    }
    if revision.founded.len() > 12 {
        println!("      ... and {} more", revision.founded.len() - 12);
    }

    println!();
    println!("{}", "-".repeat(100));
    println!("UNDER THE REVISED GRAIN");
    println!("{}", "-".repeat(100));
    let after = score(&revised, &conditioning, &held_out);
    let after_disjoint = score(&revised, &conditioning, &disjoint);
    report(HELD_OUT, &after);
    report(HELD_OUT_DISJOINT, &after_disjoint);

    println!();
    println!("{}", "=".repeat(100));
    println!("THE READING");
    println!("{}", "=".repeat(100));

    for (name, before, after) in [
        (HELD_OUT, &before, &after),
        (HELD_OUT_DISJOINT, &before_disjoint, &after_disjoint),
    ] {
        println!();
        println!("  {name}");
        match (&before.form, &after.form) {
            (Some(before_form), Some(after_form)) => {
                let difference = after_form.minus(before_form);
                println!("      the difference form is exact and is the primary return:");
                println!("          {}", difference.named());
                println!(
                    "      moved at all (exact, never Open)          {}",
                    if difference.is_zero() { "NO" } else { "YES" }
                );
                match after_form.compare(before_form) {
                    Ok(ordering) => {
                        println!("      direction at the default grain           {ordering:?}")
                    }
                    Err(error) => println!("      direction refused: {error}"),
                }
                match after_form.compare_grain(before_form, Grain::at(1, 4)) {
                    Ok(ordering) => {
                        println!("      direction at a declared coarser grain    {ordering:?}")
                    }
                    Err(error) => println!("      direction refused: {error}"),
                }
            }
            _ => {
                println!("      at least one side returned UNSUPPORTED for the whole reading.");
                println!(
                    "      That is the aggregate collapsing on the first novel event while the"
                );
                println!(
                    "      supported majority was already accumulated -- which is exactly what"
                );
                println!(
                    "      Step 2 of the plan repairs, and this run locates it on real material."
                );
            }
        }
        println!(
            "      unsupported population   {} -> {}",
            before.unsupported.len(),
            after.unsupported.len()
        );
        println!(
            "      collapsed pairs          {} -> {}",
            before.collapsed, after.collapsed
        );
    }

    println!();
    println!("{}", "-".repeat(100));
    println!("WHAT THIS RUN DOES NOT ESTABLISH");
    println!("{}", "-".repeat(100));
    println!(
        "  Nothing. It is a reading taken before construction, and the plan's steps 1 through 4"
    );
    println!(
        "  are unchanged by it. In particular it does NOT establish that the deposit improved"
    );
    println!("  anything: 'reduced founding cost is compression' was regraded 2026-07-19, and the");
    println!(
        "  later material here is IDENTICAL across the two grains, which is learning grade two."
    );
    println!("  Grade three needs a nonidentical neighbourhood and this driver does not reach it.");
    println!("{}", "=".repeat(100));
}
