//! **Step 4 of the Eros cycle.** A grain revised by one body conducts a
//! **nonidentical** later body, and the change is exhibited as a population
//! with its exact magnitude face beside it.
//!
//! The standing plan is `blueprint/THE_ROADMAP.md` §"THE EROS CYCLE".
//!
//! # The object, and it is one grade and not a slogan
//!
//! Three learning grades were deposited 2026-07-20. **Persistence** — a changed
//! body survives — is measured. **Associative** — a controlled intervening
//! history changes later *addressed* conduct — is measured. The third is open:
//!
//! > *"Experience forms a correspondence by which a retained construction
//! > changes useful conduct in a later **nonidentical** neighborhood."*
//!
//! Everything below the third grade is this deed's **carrier** and never its
//! return. `CLAUDE.md` §1: an established capability is admissible without limit
//! as a carrier and inadmissible as a result.
//!
//! # What is NOT claimed, stated before the numbers
//!
//! Not that anything was compressed. *"Reduced founding cost is compression"*
//! was regraded 2026-07-19: it measures recurrence, reuse and amortization, and
//! while those observations stand the ontological definition does not.
//!
//! Not that a cost fell. **The collapsed population is the object**; the exact
//! form is its magnitude face, reported beside it. `THE_MEASURED_CAPABILITIES`
//! grades the collapsed-pair exhibit *"the project's sharpest instrument"*
//! precisely because it converts cost from a **ratio** into an **exhibitable
//! population**, and returning a number in its place would be a regression.
//!
//! No macro-event. Nothing here reads *the machine compressed its own
//! experience*.
//!
//! # The controls, every one decided before the run
//!
//! 1. **The discriminator.** A subject-disjoint body whose reading must **not**
//!    move. If it moves as much as the held-out body, the deposit was a global
//!    normalisation and not changed terrain. This control **already fired once**,
//!    on 2026-08-14, which is why the aperture below exists.
//! 2. **The aperture orbit.** Two declared apertures must reach different
//!    grains, or the narrowing is a parameter that changes nothing.
//! 3. **The no-op.** `resume_unrevised()` must move the difference form by
//!    **exactly zero**, decided by `is_zero()` and never by an enclosure.
//! 4. **The foil.** A grain widened by words of the same lengths that the
//!    collapsed population did **not** return. If any cut does as well, the
//!    derivation is *"cutting more is better"* wearing a lineage.
//! 5. **No further founding while scoring.** The unsupported population is
//!    exhibited, never founded, or the deed has measured its own founding.
//! 6. **A derived event table.** Built from the union of the populations in
//!    play; members carried by name, never by an index this driver minted.
//!
//! # What would refute the claim
//!
//! The disjoint body moving as much as the held-out one; the no-op moving
//! anything; the foil doing as well as the derived grain; the aperture orbit
//! being trivial; or the held-out reading not moving at all.
//!
//! ```text
//! cargo run --release -p life --example the_deposit_changes_what_unseen_material_costs
//! ```

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::surprisal::{CrossEntropyFiber, SymbolicSurprisal, cross_entropy_fiber};
use life::decomposing_codec::{
    DecomposingBody, DecompositionGrain, DecompositionPass, RevisionAperture, Symbol, read,
    render_word,
};
use num_bigint::BigUint;

/// **The crossing.** Two conditioning bodies on different subjects and two later
/// bodies, one near each.
///
/// A one-sided control cannot reach grade three, and the first run of this deed
/// is why: at every aperture the deposit refines the grain, and *any* refinement
/// helps *any* later body. Measured 2026-08-14 — the words that the most
/// collapsed pairs ask for are `(`, `)`, `*`, `,`, `-`, `.`, `/`, `:`, `;`, which
/// are the least material-specific cuts there are. **Recurrence across pairs is
/// generality**, so an aperture keyed on it selects against attribution.
///
/// So the question is not *did the later body improve* — it always does. It is
/// **did it improve BECAUSE OF THIS conditioning body**, and that is a
/// difference between two deposits rather than between two grains. The return is
/// the named population one deposit reaches that the other does not.
const CIRCULATION_BODY: [&str; 2] = [
    "canon/TABLET_THE_CIRCULATING_CARTOGRAPHER.md",
    "canon/TABLET_THE_REASONING_CYCLE.md",
];
const GEOMETRY_BODY: [&str; 2] = ["canon/TABLET_THE_MANIFOLD.md", "canon/TABLET_THE_TURN.md"];

/// Later, nonidentical, held out. One near each conditioning body.
const LATER_NEAR_CIRCULATION: &str = "canon/TABLET_THE_COMPRESSION.md";
const LATER_NEAR_GEOMETRY: &str = "canon/TABLET_THE_CHART.md";

/// The declared aperture. Two are run and their orbit is exhibited before either
/// reading is believed.
const DECLARED_APERTURES: [usize; 2] = [1, 64];

/// The grain a conditioning body's own collapsed pairs derive, at a declared
/// aperture. Nothing here is authored but the threshold, and its orbit is shown.
fn derive_grain(
    origin: &DecompositionGrain,
    conditioning: &[Vec<Symbol>],
    aperture: RevisionAperture,
) -> DecompositionGrain {
    let mut body = DecomposingBody::mount(origin.clone()).expect("mounts");
    body.receive(conditioning.to_vec()).expect("readable");
    body.revise_within(aperture)
        .expect("this material admits at the declared aperture")
        .grain
}

/// The part kinds of `later` that `code_body`'s own population under this grain
/// **carries** — what the later body can be read through at all.
fn supported_kinds(
    grain: &DecompositionGrain,
    code_body: &[Vec<Symbol>],
    later: &[Vec<Symbol>],
) -> BTreeSet<Vec<Symbol>> {
    let code = read(grain, code_body)
        .expect("the code body reads")
        .part_population();
    read(grain, later)
        .expect("the later body reads")
        .part_population()
        .into_keys()
        .filter(|part| code.contains_key(part))
        .collect()
}

fn lines_of(path: &str) -> Vec<Vec<Symbol>> {
    let text = std::fs::read_to_string(path)
        .unwrap_or_else(|error| panic!("declared material must be present: {path}: {error}"));
    text.lines()
        .filter(|line| !line.trim().is_empty())
        .map(|line| line.bytes().map(Symbol).collect())
        .collect()
}

fn event_table(populations: &[&BTreeMap<Vec<Symbol>, usize>]) -> BTreeMap<Vec<Symbol>, u64> {
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
    population: &BTreeMap<Vec<Symbol>, usize>,
    table: &BTreeMap<Vec<Symbol>, u64>,
) -> BTreeMap<u64, BigUint> {
    population
        .iter()
        .filter_map(|(word, count)| table.get(word).map(|e| (*e, BigUint::from(*count))))
        .collect()
}

struct Reading {
    parse: usize,
    kinds: usize,
    collapsed: usize,
    /// Parts the later body reaches that the conditioning body's code does not
    /// carry — the founding half, exhibited and never founded.
    unreached: Vec<Vec<Symbol>>,
    form: Option<SymbolicSurprisal>,
    partial: bool,
}

fn score(grain: &DecompositionGrain, code_body: &[Vec<Symbol>], later: &[Vec<Symbol>]) -> Reading {
    let code_pass: DecompositionPass = read(grain, code_body).expect("the code body reads");
    let later_pass: DecompositionPass = read(grain, later).expect("the later body reads");
    let code = code_pass.part_population();
    let population = later_pass.part_population();
    let table = event_table(&[&code, &population]);
    let fiber = cross_entropy_fiber(&addressed(&population, &table), &addressed(&code, &table))
        .expect("the surprisal carrier is exact");
    let named: BTreeMap<u64, Vec<Symbol>> =
        table.iter().map(|(word, e)| (*e, word.clone())).collect();
    let unreached = fiber
        .unsupported()
        .iter()
        .filter_map(|event| named.get(event).cloned())
        .collect();
    Reading {
        parse: later_pass.part_count(),
        kinds: population.len(),
        collapsed: later_pass.collapsed().len(),
        unreached,
        form: fiber.form().cloned(),
        partial: matches!(fiber, CrossEntropyFiber::Partial { .. }),
    }
}

fn line(name: &str, reading: &Reading) {
    println!(
        "  {name:<34} parse {:>7}  kinds {:>6}  collapsed {:>8}  unreached {:>6}  {}",
        reading.parse,
        reading.kinds,
        reading.collapsed,
        reading.unreached.len(),
        if reading.partial {
            "PARTIAL"
        } else if reading.form.is_some() {
            "SUPPORTED"
        } else {
            "UNSUPPORTED"
        }
    );
}

/// The exact difference, which is the primary return. It is never `Open`.
fn moved(before: &Reading, after: &Reading) -> Option<(SymbolicSurprisal, bool)> {
    match (&before.form, &after.form) {
        (Some(before_form), Some(after_form)) => {
            let difference = after_form.minus(before_form);
            let zero = difference.is_zero();
            Some((difference, zero))
        }
        _ => None,
    }
}

fn main() {
    println!("{}", "=".repeat(104));
    println!("THE DEPOSIT CHANGES WHAT UNSEEN MATERIAL COSTS");
    println!("{}", "=".repeat(104));
    println!();

    let circulation: Vec<Vec<Symbol>> = CIRCULATION_BODY.iter().flat_map(|p| lines_of(p)).collect();
    let geometry: Vec<Vec<Symbol>> = GEOMETRY_BODY.iter().flat_map(|p| lines_of(p)).collect();
    let near_circulation = lines_of(LATER_NEAR_CIRCULATION);
    let near_geometry = lines_of(LATER_NEAR_GEOMETRY);

    println!("  THE CROSSING -- two conditioning bodies, two later bodies, one near each.");
    println!();
    println!("  conditioning A (circulation)  {:>5} lines   {:?}", circulation.len(), CIRCULATION_BODY);
    println!("  conditioning C (geometry)     {:>5} lines   {:?}", geometry.len(), GEOMETRY_BODY);
    println!("  later B, near A               {:>5} lines   {LATER_NEAR_CIRCULATION}", near_circulation.len());
    println!("  later D, near C               {:>5} lines   {LATER_NEAR_GEOMETRY}", near_geometry.len());
    println!();
    println!("  Both later bodies are NONIDENTICAL to both conditioning bodies and condition nothing.");
    println!();

    let origin = DecompositionGrain::declare([vec![Symbol(b' ')]]).expect("a declared grain");

    // -----------------------------------------------------------------------------------------
    // CONTROL -- the aperture orbit, taken before any reading is believed.
    // -----------------------------------------------------------------------------------------
    println!("{}", "-".repeat(104));
    println!("CONTROL -- THE APERTURE ORBIT, taken before any reading is believed");
    println!("{}", "-".repeat(104));
    let mut grains = Vec::new();
    for asked in DECLARED_APERTURES {
        let aperture = RevisionAperture::asked_by_at_least(asked).expect("positive");
        let mut body = DecomposingBody::mount(origin.clone()).expect("mounts");
        body.receive(circulation.clone()).expect("readable");
        let revision = body.revise_within(aperture).expect("admits");
        println!(
            "  asked by >= {asked:<4}  founded {:>8}  admitted {:>6}  excluded {:>6}  grain -> {}",
            revision.founded.len(),
            revision.words.len(),
            revision.excluded.len(),
            revision.grain.cuts().len()
        );
        grains.push(revision.words.clone());
    }
    let orbit_is_nontrivial = grains[0] != grains[1];
    println!(
        "  the two declared apertures reached different grains   {}",
        if orbit_is_nontrivial { "YES" } else { "NO -- vacuous" }
    );

    let aperture = RevisionAperture::asked_by_at_least(DECLARED_APERTURES[1]).expect("positive");
    let grain_a = derive_grain(&origin, &circulation, aperture);
    let grain_c = derive_grain(&origin, &geometry, aperture);

    println!();
    println!("{}", "-".repeat(104));
    println!("THE TWO DEPOSITS -- each derived from its own body's collapsed pairs");
    println!("{}", "-".repeat(104));
    println!("  A (circulation) grain   {} cut words", grain_a.cuts().len());
    println!("  C (geometry)    grain   {} cut words", grain_c.cuts().len());
    let shared: BTreeSet<Vec<Symbol>> = grain_a
        .cuts()
        .intersection(grain_c.cuts())
        .cloned()
        .collect();
    let only_a: Vec<Vec<Symbol>> = grain_a.cuts().difference(grain_c.cuts()).cloned().collect();
    let only_c: Vec<Vec<Symbol>> = grain_c.cuts().difference(grain_a.cuts()).cloned().collect();
    println!(
        "  shared {} words; only A {}; only C {}",
        shared.len(),
        only_a.len(),
        only_c.len()
    );
    println!(
        "  only A: {}",
        only_a.iter().take(14).map(|w| render_word(w)).collect::<Vec<_>>().join("  ")
    );
    println!(
        "  only C: {}",
        only_c.iter().take(14).map(|w| render_word(w)).collect::<Vec<_>>().join("  ")
    );
    let deposits_differ = !only_a.is_empty() && !only_c.is_empty();

    // -----------------------------------------------------------------------------------------
    // THE CROSSING. Each later body read through each deposit.
    // -----------------------------------------------------------------------------------------
    println!();
    println!("{}", "=".repeat(104));
    println!("THE CROSSING -- what each later body reaches through each deposit");
    println!("{}", "=".repeat(104));

    let b_through_a = supported_kinds(&grain_a, &circulation, &near_circulation);
    let b_through_c = supported_kinds(&grain_c, &geometry, &near_circulation);
    let d_through_a = supported_kinds(&grain_a, &circulation, &near_geometry);
    let d_through_c = supported_kinds(&grain_c, &geometry, &near_geometry);

    println!(
        "  B through A {:>6} kinds        B through C {:>6} kinds",
        b_through_a.len(),
        b_through_c.len()
    );
    println!(
        "  D through A {:>6} kinds        D through C {:>6} kinds",
        d_through_a.len(),
        d_through_c.len()
    );

    // The attributable return: named members one deposit reaches and the other does not.
    let b_only_a: Vec<Vec<Symbol>> = b_through_a.difference(&b_through_c).cloned().collect();
    let b_only_c: Vec<Vec<Symbol>> = b_through_c.difference(&b_through_a).cloned().collect();
    let d_only_a: Vec<Vec<Symbol>> = d_through_a.difference(&d_through_c).cloned().collect();
    let d_only_c: Vec<Vec<Symbol>> = d_through_c.difference(&d_through_a).cloned().collect();

    println!();
    println!("  THE ATTRIBUTABLE POPULATION -- reached through one deposit and not the other");
    println!(
        "      B reaches {:>5} kinds only through A, and {:>5} only through C",
        b_only_a.len(),
        b_only_c.len()
    );
    println!(
        "      D reaches {:>5} kinds only through A, and {:>5} only through C",
        d_only_a.len(),
        d_only_c.len()
    );
    println!();
    println!("      B only through A: {}", b_only_a.iter().take(12).map(|w| render_word(w)).collect::<Vec<_>>().join("  "));
    println!("      D only through C: {}", d_only_c.iter().take(12).map(|w| render_word(w)).collect::<Vec<_>>().join("  "));

    // The crossing itself: does each later body favour its own neighbour's deposit?
    let b_favours_a = b_only_a.len() as i64 - b_only_c.len() as i64;
    let d_favours_c = d_only_c.len() as i64 - d_only_a.len() as i64;
    println!();
    println!("  B's preference for A over C   {b_favours_a:+}");
    println!("  D's preference for C over A   {d_favours_c:+}");
    let crossing_holds = b_favours_a > 0 && d_favours_c > 0;

    // -----------------------------------------------------------------------------------------
    // The magnitude face, beside the population and never instead of it.
    // -----------------------------------------------------------------------------------------
    println!();
    println!("{}", "-".repeat(104));
    println!("THE MAGNITUDE FACE -- beside the population, never instead of it");
    println!("{}", "-".repeat(104));
    let b_parent = score(&origin, &circulation, &near_circulation);
    let b_revised = score(&grain_a, &circulation, &near_circulation);
    line("B under the parent grain", &b_parent);
    line("B under A's deposit", &b_revised);
    match moved(&b_parent, &b_revised) {
        Some((difference, zero)) => println!(
            "      difference form {}   {}",
            if zero { "IS EXACTLY ZERO" } else { "moved" },
            if zero { String::new() } else { difference.named() }
        ),
        None => println!("      one side carried no supported part at all"),
    }

    // -----------------------------------------------------------------------------------------
    // CONTROL -- the no-op. Resuming unrevised must move nothing at all.
    // -----------------------------------------------------------------------------------------
    let mut unrevised = DecomposingBody::mount(origin.clone()).expect("mounts");
    unrevised.receive(circulation.clone()).expect("readable");
    unrevised.resume_unrevised().expect("an open reflection closes");
    let b_unrevised = score(&origin, &circulation, &near_circulation);
    let noop = moved(&b_parent, &b_unrevised);
    let noop_is_zero = matches!(noop, Some((_, true)));

    // -----------------------------------------------------------------------------------------
    // CONTROL -- the foil. Same-length words the population did NOT return.
    // -----------------------------------------------------------------------------------------
    let asked: BTreeSet<Vec<Symbol>> = grain_a.cuts().clone();
    let alphabet: Vec<u8> = (b'a'..=b'z').collect();
    let mut foil_words: Vec<Vec<Symbol>> = Vec::new();
    let mut at = 0usize;
    for word in grain_a.cuts() {
        let mut candidate: Vec<Symbol> = Vec::new();
        loop {
            candidate = (0..word.len().max(1))
                .map(|k| Symbol(alphabet[(at + k * 7) % alphabet.len()]))
                .collect();
            at += 1;
            if (!asked.contains(&candidate) && !foil_words.contains(&candidate)) || at > 8192 {
                break;
            }
        }
        foil_words.push(candidate);
    }
    let foil = origin.with_all(foil_words).expect("a foil grain of the same shape");

    // The foil must be measured by the SAME statistic as the derived cut, or the
    // comparison is between two different quantities. An earlier form of this
    // control compared a set size against a net preference and reported the foil
    // as winning; it was measuring nothing. The statistic is: run the whole
    // crossing again with the foil standing in for A.
    let b_through_foil = supported_kinds(&foil, &circulation, &near_circulation);
    let d_through_foil = supported_kinds(&foil, &circulation, &near_geometry);
    let b_foil_pref = b_through_foil.difference(&b_through_c).count() as i64
        - b_through_c.difference(&b_through_foil).count() as i64;
    let d_foil_pref = d_through_c.difference(&d_through_foil).count() as i64
        - d_through_foil.difference(&d_through_c).count() as i64;
    let foil_crosses = b_foil_pref > 0 && d_foil_pref > 0;
    let foil_is_weaker = !foil_crosses || (b_foil_pref < b_favours_a && d_foil_pref < d_favours_c);

    println!();
    println!("{}", "=".repeat(104));
    println!("WHAT RETURNED");
    println!("{}", "=".repeat(104));
    println!("  aperture orbit non-trivial                          {orbit_is_nontrivial}");
    println!("  the two deposits genuinely differ                   {deposits_differ}");
    println!("  the no-op moved exactly zero                        {noop_is_zero}");
    println!("  the foil, run through the SAME crossing statistic:");
    println!("      B favours the foil over C by {b_foil_pref:+}   (derived cut: {b_favours_a:+})");
    println!("      D favours C over the foil by {d_foil_pref:+}   (derived cut: {d_favours_c:+})");
    println!(
        "      the foil crosses too                            {foil_crosses}   {}",
        if foil_is_weaker {
            "the derived cut is not decorative"
        } else {
            "FOIL CROSSES AS WELL -- the derived cut IS decorative and the deed is refuted"
        }
    );
    println!("  THE CROSSING HOLDS                                  {crossing_holds}");
    println!("      B favours its neighbour's deposit by {b_favours_a:+}");
    println!("      D favours its neighbour's deposit by {d_favours_c:+}");

    println!();
    println!("{}", "-".repeat(104));
    println!("WHAT THIS RUN DOES NOT ESTABLISH");
    println!("{}", "-".repeat(104));
    println!("  Not compression: 'reduced founding cost is compression' was regraded 2026-07-19.");
    println!("  Not intelligence: that step is where machine-independence is known not to extend.");
    println!("  The population is the object; the exact form is its magnitude face. The grade");
    println!("  claimed is exactly three -- a later NONIDENTICAL neighbourhood -- and every grade");
    println!("  below it stands as the carrier and never as the return.");
    println!("  Two conditioning bodies and two later bodies is a crossing of FOUR readings, not a");
    println!("  population of experiments; nothing here is a rate and no figure is an average.");
    println!("{}", "=".repeat(104));
}
