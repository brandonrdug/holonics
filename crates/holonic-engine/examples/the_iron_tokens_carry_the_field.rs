//! The iron tokens a corpus founds, and what they cost to find.
//!
//! ## The question
//!
//! Brandon:
//!
//! > *"if in the English we use about mathematics, there are certain words that are used
//! > invariantly to refer to a discrete kind of object… If the words are not necessarily hard-coded
//! > as invariants, but the machine experiences them as invariants associated with particular
//! > meanings, then perhaps its language comprehension would implicitly curve around those **iron
//! > recurrences (density)**. It would give implicit meaning to words that warp around the usage of
//! > invariant tokens… The density and invariants it founds are not ours to necessarily author,
//! > they are happenstance of our own writing."*
//!
//! The precedent is `canon/THE_DIALECT.md`: 8,935 messages measured, `holon` 1141, `current` 696,
//! `FOUND`/`RIDE`/`OPEN` as capitalised primitives **zero**. Nobody authored that reading.
//!
//! ## Why two readings and not one
//!
//! **Frequency is `Π`** — the lived construction — and `Π` does not gate. **Probability is `Q`**, a
//! quotient a *declared receiver* takes, and because it is a quotient its loss is exhibitable.
//! `reference/holobrochos-a07ff376/src/soma/FORMULA.md:2459`: *"A probability distribution over
//! which event will be received is an observer's declared quotient over what that observer does not
//! carry."*
//!
//! And **an amplitude is complex while a probability is its squared modulus**, so a probability
//! keeps the magnitude and deletes the **phase** — the same deletion a float performs on the tail
//! and a bare sign performs on the turn, at a fourth carrier. Two routes to one result add as
//! amplitudes, not counts: **a frequency census cannot tell two routes that reinforce from two that
//! cancel.** So density alone cannot say whether 4,712 occurrences are one object seen 4,712 times
//! or a dozen objects sharing a spelling.
//!
//! **Iron = dense AND unseparated. Those are the magnitude and the phase of one reading.**
//!
//! ## Where the two readings come from
//!
//! - **density** — `corpus_census`, handing the embodied standing to `surprisal::read_population`,
//!   which returns `S(p) = -log2 p` as a ℚ-linear form over prime axes and never as a number.
//! - **separation** — `token_invariance`, presenting each surface's occurrences as *positions* to
//!   `receiver_exact_compression::compress`, whose collapsed population carries the **shortest word**
//!   that separates each pair and the receiver that saw it.
//!
//! ## The declared controls
//!
//! 1. Density and separation come apart on the real corpus: a dense separable surface and a sparse
//!    unseparated one are both exhibited. If they never came apart the conjunction would be doing no
//!    work and this driver would say so.
//! 2. The separating word is **exhibited** for every separable surface, not summarised. Checked over
//!    the whole sweep at both horizons.
//! 3. Nothing is dropped silently: every measured surface carries both readings, and every declared
//!    bound names its residual.
//! 4. The receiver family is declared and its orbit is **non-trivial** — each axis separates a pair
//!    of the corpus's own surfaces that the other two do not, and each axis's ablation strictly
//!    coarsens some surface's reading. The standard is `rebase_invariants.rs`'s pivot-rule gauge:
//!    *"their agreement is one computation compared with itself twice."*
//! 5. Two expectations declared in advance and shown, plus a third declared from
//!    `canon/THE_DIALECT.md` that the corpus **refutes** — reported as the finding it is.
//! 6. The window census and the organ's Nerode refinement are two independent implementations of one
//!    partition and must agree on every surface (`CLAUDE.md` §8).
//! 7. The surprisal carrier's refusal arm is driven on real material: a stratum read through another
//!    stratum's standing returns `Unsupported` rather than a smoothing constant, and `Support::found`
//!    resolves it by **changing the support** — measurably, on a third surface's form.
//!
//! ## Provenance of the expectations
//!
//! Assistant-declared, not Brandon's. `arxiv`-iron and `the`-fuzzy were formed from a throwaway
//! Python probe of this same corpus taken before the Rust reading, and are therefore predictions
//! about whether *this implementation* reproduces that probe rather than blind guesses. The
//! `holon`-iron expectation is independent: it comes from `canon/THE_DIALECT.md`'s measurement of a
//! different corpus, and it is refuted here.

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

use holonic_engine::corpus_census::{
    CorpusCensus, DECLARED_STRATA, DensityRow, Stratum, SurfaceId, density_band,
};
use holonic_engine::exact_value::ExactOrdering;
use holonic_engine::surprisal::{
    Grain, Support, SymbolicSurprisal, cross_entropy, read_population,
};
use holonic_engine::token_invariance::{
    AblationReading, ReceiverAxis, SeparationReading, Verdict, ablation_profile, axis_witnesses,
    cross_check, iron_at, sweep, warping_incidence, window, witnessed_iron_at,
};
use num_bigint::BigUint;

/// The two declared horizons. A receiver coordinate: every reading carries the one it was taken at.
const HORIZONS: [usize; 2] = [1, 2];
/// The declared radius of the warping incidence.
const WARP_RADIUS: usize = 4;
/// The declared exhibition floor. A **presentation** bound on printing, never on measuring: every
/// surface below it is still measured, still in the return, and its count is named.
const EXHIBITION_FLOOR: u64 = 4;
/// **The capacity this caller declares**, in separated class pairs per surface.
///
/// `canon/THE_AUTHORED_LEVEL.md`: a level is either read off the material or declared by the caller.
/// This is the caller declaring, and it is a statement about *this host*, not about the corpus:
/// materializing a pair population is the one quadratic operation in the reading, and 8,192 pairs
/// per surface is what this driver is willing to hold at once. Every surface past it returns
/// `ExhibitionObstructed` naming the width its material required, and this driver **prints that
/// population and its widths** rather than letting it disappear.
const DECLARED_CAPACITY: u64 = 8_192;
/// The window aperture this module carried as an authored constant until 2026-08-09, kept here only
/// so the excision's orbit can be measured against it. It decides nothing.
const EXCISED_WINDOW_APERTURE: usize = 64;
/// The separation cap this module carried as an authored constant until 2026-08-09, same purpose.
const EXCISED_SEPARATION_EXHIBIT: usize = 512;

fn main() {
    let root = std::env::args()
        .nth(1)
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            PathBuf::from(env!("CARGO_MANIFEST_DIR"))
                .join("..")
                .join("..")
        });

    let census = match CorpusCensus::read(&root) {
        Ok(census) => census,
        Err(error) => {
            println!("the declared corpus could not be read: {error}");
            std::process::exit(1);
        }
    };

    let mut holds: Vec<(String, bool, String)> = Vec::new();

    // ---------------------------------------------------------------- the declared corpus
    println!("THE IRON TOKENS CARRY THE FIELD");
    println!("===============================");
    println!();
    println!("The declared corpus. Four strata, whole files, nothing sampled.");
    println!();
    println!(
        "  {:<9} {:<34} {:>7} {:>12} {:>10}",
        "stratum", "root", "wholes", "word tokens", "distinct"
    );
    for declaration in DECLARED_STRATA {
        let wholes: Vec<_> = census
            .wholes()
            .iter()
            .filter(|whole| whole.stratum == declaration.stratum)
            .collect();
        let population = census.stratum_population(declaration.stratum);
        let tokens: BigUint = population.values().sum();
        println!(
            "  {:<9} {:<34} {:>7} {:>12} {:>10}",
            declaration.stratum.name(),
            format!("{}/*.{}", declaration.relative_root, declaration.extension),
            wholes.len(),
            tokens,
            population.len()
        );
    }
    let word_surfaces = census.word_surfaces();
    println!();
    println!(
        "  total stream        {} tokens ({} word, {} markup)",
        census.total_occurrences(),
        census.word_occurrences(),
        census.total_occurrences() - census.word_occurrences()
    );
    println!("  measured population {} distinct word surfaces", word_surfaces.len());

    // The one bound on the measured population, named rather than silent.
    let markup = census.markup_bound(8);
    println!();
    println!(
        "  DECLARED BOUND -- the measured population is the WORD surfaces. Markup stays in the \n\
         \x20 stream (a receiver standing next to a `#` must see it) and carries its own density \n\
         \x20 band, but is not itself measured. What that excludes, named:"
    );
    println!(
        "    {} markup occurrences over {} distinct markup surfaces; most recurrent:",
        markup.markup_occurrences, markup.distinct_markup_surfaces
    );
    println!(
        "    {}",
        markup
            .exhibited
            .iter()
            .map(|(surface, count)| format!("{surface:?} x{count}"))
            .collect::<Vec<_>>()
            .join("  ")
    );

    // ------------------------------------------------- CONTROL 4a: the family's orbit
    println!();
    println!("THE DECLARED RECEIVER FAMILY, AND ITS ORBIT");
    println!("-------------------------------------------");
    println!(
        "Three receivers, each reading one coordinate of a surface's census signature. `density` \n\
         is `floor(log2 N)` computed as a bit length -- exact integers, no logarithm evaluated. It \n\
         is the axis the question asks for: comprehension curving around iron recurrences requires \n\
         density to be something a RECEIVER can see, not only something a reader tabulates."
    );
    println!();
    let witnesses = axis_witnesses(&census);
    let mut orbit_nontrivial = true;
    for axis in ReceiverAxis::DECLARED {
        match witnesses.get(&axis) {
            Some(witness) => {
                let left = census.signature(witness.left);
                let right = census.signature(witness.right);
                let others: Vec<&str> = ReceiverAxis::DECLARED
                    .into_iter()
                    .filter(|other| {
                        *other != axis
                            && match other {
                                ReceiverAxis::Kind => left.0 != right.0,
                                ReceiverAxis::Weight => left.1 != right.1,
                                ReceiverAxis::Density => left.2 != right.2,
                            }
                    })
                    .map(|other| other.name())
                    .collect();
                if !others.is_empty() {
                    orbit_nontrivial = false;
                }
                println!(
                    "  {:<8} separates {:>22} from {:<22} ({} vs {}); the other two agree: {}",
                    axis.name(),
                    format!("{:?}", census.surface(witness.left)),
                    format!("{:?}", census.surface(witness.right)),
                    axis.render(witness.left_reading),
                    axis.render(witness.right_reading),
                    if others.is_empty() { "yes" } else { "NO" }
                );
            }
            None => {
                orbit_nontrivial = false;
                println!("  {:<8} FOUND NO WITNESS -- this axis is not acting", axis.name());
            }
        }
    }
    holds.push((
        "control 4a -- each declared receiver separates a pair of the corpus's own surfaces that \
         the other two do not"
            .to_owned(),
        orbit_nontrivial,
        format!("{} of 3 axes exhibited a witness", witnesses.len()),
    ));

    // ---------------------------------------------------------------- the density reading
    println!();
    println!("1 -- THE DENSITY READING (`Pi`, counted, gating nothing)");
    println!("--------------------------------------------------------");
    let density = match census.density_reading() {
        Ok(reading) => reading,
        Err(error) => {
            println!("the density reading failed: {error}");
            std::process::exit(1);
        }
    };
    println!(
        "Every one of the {} measured surfaces carries occurrences, distinct wholes, the strata it \n\
         reaches, and the EXACT symbolic surprisal of its embodied probability p = N/SumN -- a \n\
         Q-linear form over prime axes, stored and never evaluated.",
        density.len()
    );
    println!();
    let mut by_occurrence: Vec<(&SurfaceId, &DensityRow)> = density.iter().collect();
    by_occurrence.sort_by(|left, right| {
        right
            .1
            .occurrences
            .cmp(&left.1.occurrences)
            .then(left.0.cmp(right.0))
    });
    println!(
        "  {:<14} {:>8} {:>7} {:<22} {}",
        "surface", "occ", "wholes", "strata", "S(p) = -log2 p, exact"
    );
    for (surface, row) in by_occurrence.iter().take(14) {
        println!(
            "  {:<14} {:>8} {:>7} {:<22} {}",
            format!("{:?}", census.surface(**surface)),
            row.occurrences,
            row.distinct_wholes,
            row.strata
                .iter()
                .map(|stratum| stratum.name())
                .collect::<Vec<_>>()
                .join(","),
            render_support(&row.surprisal)
        );
    }

    // ---------------------------------------------------------------- the separation reading
    println!();
    println!("2 -- THE SEPARATION READING (`receiver_exact_compression`, Moore refinement)");
    println!("---------------------------------------------------------------------------");
    println!(
        "An occurrence is a POSITION. Conduct steps left or right, bounded by a declared horizon. \n\
         All occurrences of one surface start in ONE one-shot block -- the reading gets no head \n\
         start -- and the conduct partition is the Nerode congruence of the declared family. The \n\
         collapsed population carries the SHORTEST word that separates each pair."
    );
    println!();
    println!(
        "  NO APERTURE BOUNDS THIS READING. The separation population factorizes: conduct words are\n\
         \x20 pure runs, so a window is an ORDERED word (-1, +1, -2, +2, ...) whose lexicographic\n\
         \x20 order IS the organ's refinement order, and the first index at which two windows differ\n\
         \x20 carries the shortest separating word, its offset, and the receiver that sees it. The\n\
         \x20 whole population of `C(d,2)` pairs is therefore held by `d` sorted classes and `d-1`\n\
         \x20 shared-prefix lengths -- `O(d * horizon)` -- and every pair is recoverable exactly.\n\
         \x20 Until 2026-08-09 this module presented the first {EXCISED_WINDOW_APERTURE} distinct \
         windows per surface and\n\
         \x20 retained {EXCISED_SEPARATION_EXHIBIT} separations. Section 6 measures what that was \
         withholding."
    );

    let mut sweeps: BTreeMap<usize, BTreeMap<SurfaceId, SeparationReading>> = BTreeMap::new();
    let mut irons: BTreeMap<usize, BTreeSet<SurfaceId>> = BTreeMap::new();
    let mut witnessed: BTreeMap<usize, BTreeSet<SurfaceId>> = BTreeMap::new();
    for horizon in HORIZONS {
        let reading = sweep(&census, horizon);
        irons.insert(horizon, iron_at(&reading));
        witnessed.insert(horizon, witnessed_iron_at(&reading));
        sweeps.insert(horizon, reading);
    }

    println!();
    println!(
        "  {:<8} {:>10} {:>10} {:>12} {:>12} {:>12} {:>14} {:>18}",
        "horizon",
        "measured",
        "iron",
        "vacuous",
        "witnessed",
        "separated",
        "max windows",
        "separated pairs"
    );
    for horizon in HORIZONS {
        let reading = &sweeps[&horizon];
        let iron = &irons[&horizon];
        let seen = &witnessed[&horizon];
        let widest = reading
            .values()
            .map(|row| row.distinct_windows)
            .max()
            .unwrap_or(0);
        let pairs: BigUint = reading
            .values()
            .map(|row| row.complex.separated_class_pairs())
            .sum();
        println!(
            "  {:<8} {:>10} {:>10} {:>12} {:>12} {:>12} {:>14} {:>18}",
            horizon,
            reading.len(),
            iron.len(),
            iron.len() - seen.len(),
            seen.len(),
            reading.len() - iron.len(),
            widest,
            pairs
        );
    }
    println!();
    println!(
        "  `CLAUDE.md` §8, THE TAUTOLOGY RULE, AND IT BITES HERE. A surface occurring ONCE is\n\
         \x20 unseparated by arithmetic: there is no occurrence pair for conduct to separate, so its\n\
         \x20 iron verdict could not have come out otherwise and carries no evidence. The reading\n\
         \x20 carries the exact count of non-separations each verdict survived -- `C(N,2)` -- and it\n\
         \x20 is zero exactly on the vacuous ones. **Nothing is dropped**: the vacuous population is\n\
         \x20 in the return with both readings and its size is printed above. What follows uses the\n\
         \x20 WITNESSED iron -- verdicts at least one pair could have refuted."
    );
    {
        let reading = &sweeps[&HORIZONS[1]];
        let mut survived: Vec<(&SurfaceId, BigUint)> = witnessed[&HORIZONS[1]]
            .iter()
            .map(|surface| (surface, reading[surface].survived_pairs()))
            .collect();
        survived.sort_by(|left, right| right.1.cmp(&left.1).then(left.0.cmp(right.0)));
        println!();
        println!("  The iron verdicts that survived the most refutations, at horizon {}:", HORIZONS[1]);
        for (surface, pairs) in survived.iter().take(6) {
            println!(
                "    {:<24} {} occurrences across {} wholes -> {} pairwise non-separations",
                format!("{:?}", census.surface(**surface)),
                census.occurrences(**surface),
                census.distinct_wholes(**surface),
                pairs
            );
        }
    }
    holds.push((
        "the iron verdict is non-vacuous: some surface's iron reading survived a large exact number \
         of occurrence pairs that could each have refuted it"
            .to_owned(),
        witnessed[&HORIZONS[1]]
            .iter()
            .any(|surface| sweeps[&HORIZONS[1]][surface].survived_pairs() > BigUint::from(1000u32)),
        format!(
            "{} witnessed iron surfaces at horizon {}, {} vacuous",
            witnessed[&HORIZONS[1]].len(),
            HORIZONS[1],
            irons[&HORIZONS[1]].len() - witnessed[&HORIZONS[1]].len()
        ),
    ));

    // ------------------------------------------------- CONTROL 6: two implementations agree
    //
    // The factorization computed by `token_invariance` and the Moore refinement computed by
    // `receiver_exact_compression` are two implementations of one partition, and this compares them
    // PAIR FOR PAIR -- word, witness, terminus -- not just block counts. The organ's cost is
    // quadratic, so the comparison runs under this caller's declared capacity and the surfaces past
    // it are named with the width they required rather than dropped.
    println!();
    println!("  CONTROL 6 -- the second implementation, run pair for pair against the first.");
    let mut checked = 0usize;
    let mut compared_pairs = BigUint::from(0u32);
    let mut check_failures: Vec<String> = Vec::new();
    let mut obstructed: Vec<(usize, SurfaceId, BigUint)> = Vec::new();
    for horizon in HORIZONS {
        for surface in sweeps[&horizon].keys() {
            match cross_check(&census, *surface, horizon, DECLARED_CAPACITY) {
                Ok(check) => {
                    checked += 1;
                    compared_pairs += BigUint::from(check.organ_pairs);
                    if !check.agrees() {
                        check_failures.push(format!(
                            "h{horizon} {:?}: {} classes vs {} conduct blocks, {} vs {} pairs, \
                             {} word/witness disagreements",
                            census.surface(*surface),
                            check.classes,
                            check.conduct_blocks,
                            check.factorized_pairs,
                            check.organ_pairs,
                            check.disagreements.len()
                        ));
                    }
                }
                Err(obstruction) => {
                    obstructed.push((horizon, *surface, obstruction.required.clone()));
                }
            }
        }
    }
    obstructed.sort_by(|left, right| right.2.cmp(&left.2));
    println!(
        "    {checked} readings cross-checked, {compared_pairs} pairs compared, {} disagreements",
        check_failures.len()
    );
    println!(
        "    {} readings OBSTRUCTED at the declared capacity of {DECLARED_CAPACITY} class pairs. \
         An obstruction is\n    not a truncation: no separations were returned for these, and each \
         names the width its\n    material required. The widest:",
        obstructed.len()
    );
    for (horizon, surface, required) in obstructed.iter().take(6) {
        println!(
            "      h{horizon} {:<16} required width {required} ({} distinct windows)",
            format!("{:?}", census.surface(*surface)),
            sweeps[horizon][surface].distinct_windows
        );
    }
    holds.push((
        "control 6 -- the factorized separation complex and the organ's Moore refinement are two \
         independent implementations of one partition and agree PAIR FOR PAIR on every surface \
         inside the declared capacity, at both horizons"
            .to_owned(),
        check_failures.is_empty() && compared_pairs > BigUint::from(0u32),
        if check_failures.is_empty() {
            format!(
                "{checked} readings, {compared_pairs} pairs compared, 0 disagreements; \
                 {} readings obstructed and named",
                obstructed.len()
            )
        } else {
            format!("{} disagreements, first: {}", check_failures.len(), check_failures[0])
        },
    ));

    // ------------------------------------------------- CONTROL 4b: ablation contribution
    println!();
    println!("  Each axis's contribution, measured by `AblatedSystem` rather than assumed.");
    println!("  H.0016's transformations clause: removing a receiver may only COARSEN.");
    println!();
    let ablation_probes: Vec<SurfaceId> = by_occurrence
        .iter()
        .take(40)
        .map(|(surface, _)| **surface)
        .collect();
    let mut contributed: BTreeMap<ReceiverAxis, Option<(SurfaceId, AblationReading)>> =
        ReceiverAxis::DECLARED.into_iter().map(|axis| (axis, None)).collect();
    let mut refined_anywhere = false;
    for probe in &ablation_probes {
        for reading in ablation_profile(&census, *probe, 2) {
            if reading.blocks_without > reading.blocks_with {
                refined_anywhere = true;
            }
            let slot = contributed.get_mut(&reading.axis).expect("declared axis");
            if slot.is_none() && reading.contributed() {
                *slot = Some((*probe, reading));
            }
        }
    }
    let mut every_axis_contributes = true;
    for axis in ReceiverAxis::DECLARED {
        match contributed[&axis] {
            Some((surface, reading)) => println!(
                "    {:<8} ablated on {:>14}: {} conduct blocks -> {}",
                axis.name(),
                format!("{:?}", census.surface(surface)),
                reading.blocks_with,
                reading.blocks_without
            ),
            None => {
                every_axis_contributes = false;
                println!(
                    "    {:<8} NEVER changed a reading over {} probes -- it is not acting",
                    axis.name(),
                    ablation_probes.len()
                );
            }
        }
    }
    holds.push((
        "control 4b -- every declared receiver's ablation strictly coarsens some surface's reading, \
         and no ablation ever refines one"
            .to_owned(),
        every_axis_contributes && !refined_anywhere,
        format!(
            "3 axes over {} probes; refinements observed: {}",
            ablation_probes.len(),
            refined_anywhere
        ),
    ));

    // ------------------------------------------------- CONTROL 2: every separable word exhibited
    //
    // `shortest_separation` is a COMPLETE answer to a narrower question, not a prefix of the
    // population: it is the pair that separates soonest, materialized from the complex on demand.
    // It runs on every separable surface at both horizons regardless of width, because it costs one
    // pair rather than `C(d,2)`.
    let mut unexhibited = Vec::new();
    let mut empty_word = Vec::new();
    for horizon in HORIZONS {
        for (surface, row) in &sweeps[&horizon] {
            if matches!(row.verdict, Verdict::Separated { .. }) {
                match row.shortest_separation(&census) {
                    None => unexhibited.push((horizon, *surface)),
                    Some(separation) if separation.word.is_empty() => {
                        empty_word.push((horizon, *surface));
                    }
                    Some(_) => {}
                }
            }
        }
    }
    holds.push((
        "control 2 -- every separable surface exhibits at least one separating word, and no word is \
         empty (an empty word is the one-shot reading, which held every occurrence together)"
            .to_owned(),
        unexhibited.is_empty() && empty_word.is_empty(),
        format!(
            "{} separable surfaces with no exhibited word, {} with an empty word",
            unexhibited.len(),
            empty_word.len()
        ),
    ));

    // ------------------------------------------------- CONTROL 3: nothing dropped
    let mut both_readings = true;
    for horizon in HORIZONS {
        let reading = &sweeps[&horizon];
        if reading.len() != density.len() {
            both_readings = false;
        }
        for surface in density.keys() {
            if !reading.contains_key(surface) {
                both_readings = false;
            }
        }
    }
    // Every verdict is taken over the WHOLE occurrence population: the sum of each surface's window
    // classes' occurrences must be the census's own count for that surface, or something was
    // sampled. This is failable — a subsampling reading fails it on the first busy surface.
    let mut short_read: Vec<(usize, SurfaceId)> = Vec::new();
    for horizon in HORIZONS {
        for (surface, row) in &sweeps[&horizon] {
            if row.complex.occurrences() != BigUint::from(census.occurrences(*surface)) {
                short_read.push((horizon, *surface));
            }
        }
    }
    holds.push((
        "control 3 -- every measured surface appears in BOTH readings at BOTH horizons, and every \
         separation reading covers that surface's WHOLE occurrence population"
            .to_owned(),
        both_readings && short_read.is_empty(),
        format!(
            "{} density rows, {} separation rows per horizon, {} surfaces read short of their \
             census count",
            density.len(),
            sweeps[&HORIZONS[0]].len(),
            short_read.len()
        ),
    ));

    // ------------------------------------------------- the monotone contraction
    let near = &irons[&HORIZONS[0]];
    let far = &irons[&HORIZONS[1]];
    holds.push((
        "the iron population contracts monotonically in the horizon: a longer word can only \
         separate more"
            .to_owned(),
        far.is_subset(near),
        format!(
            "iron@{} = {}, iron@{} = {}, contained: {}",
            HORIZONS[0],
            near.len(),
            HORIZONS[1],
            far.len(),
            far.is_subset(near)
        ),
    ));

    // ---------------------------------------------------------------- 3: the conjunction
    println!();
    println!("3 -- THE CONJUNCTION, AS A POPULATION");
    println!("-------------------------------------");
    println!(
        "The joint reading over EVERY measured surface: density band (floor(log2 occurrences)) \n\
         against separation verdict at horizon {}. Not a ranking -- a cross-tabulation, so every \n\
         surface is in it and no cut decides anything.",
        HORIZONS[1]
    );
    println!();
    let far_sweep = &sweeps[&HORIZONS[1]];
    let far_witnessed = &witnessed[&HORIZONS[1]];
    let mut table: BTreeMap<u64, (usize, usize, BTreeMap<usize, usize>)> = BTreeMap::new();
    for (surface, row) in far_sweep {
        let band = density_band(census.occurrences(*surface));
        let slot = table.entry(band).or_default();
        match row.verdict {
            Verdict::Iron => slot.0 += 1,
            Verdict::Separated { first_depth } => {
                slot.1 += 1;
                *slot.2.entry(first_depth).or_default() += 1;
            }
        }
    }
    println!(
        "  {:<12} {:>10} {:>8} {:>10} {:>22}",
        "occ band", "surfaces", "iron", "separated", "first separated at"
    );
    for (band, (iron, separated, depths)) in &table {
        let low = if *band == 0 { 1u64 } else { 1u64 << band };
        let high = (1u64 << (band + 1)) - 1;
        println!(
            "  {:<12} {:>10} {:>8} {:>10} {:>22}",
            format!("{low}..{high}"),
            iron + separated,
            iron,
            separated,
            depths
                .iter()
                .map(|(depth, count)| format!("d{depth}:{count}"))
                .collect::<Vec<_>>()
                .join(" ")
        );
    }

    println!();
    println!(
        "  THE IRON POPULATION at horizon {}, occurrences >= {EXHIBITION_FLOOR}. The floor is an \n\
         EXHIBITION bound on printing, not a measurement bound: {} iron surfaces sit below it -- \n\
         {} of them vacuously, on a single occurrence -- and every one is in the return with both \n\
         readings. `survived` is the exact count of occurrence pairs the verdict withstood.",
        HORIZONS[1],
        far.iter()
            .filter(|surface| census.occurrences(**surface) < EXHIBITION_FLOOR)
            .count(),
        far.len() - far_witnessed.len()
    );
    println!();
    let mut dense_iron: Vec<SurfaceId> = far
        .iter()
        .copied()
        .filter(|surface| census.occurrences(*surface) >= EXHIBITION_FLOOR)
        .collect();
    dense_iron.sort_by_key(|surface| (std::cmp::Reverse(census.occurrences(*surface)), *surface));
    println!(
        "  {:<24} {:>6} {:>6} {:>8} {:<16} {}",
        "iron surface", "occ", "wholes", "survived", "strata", "S(p) = -log2 p, exact"
    );
    for surface in dense_iron.iter().take(34) {
        let row = &density[surface];
        println!(
            "  {:<24} {:>6} {:>6} {:>8} {:<16} {}",
            format!("{:?}", census.surface(*surface)),
            row.occurrences,
            row.distinct_wholes,
            far_sweep[surface].survived_pairs(),
            row.strata.iter().map(|s| s.name()).collect::<Vec<_>>().join(","),
            render_support(&row.surprisal)
        );
    }
    if dense_iron.len() > 34 {
        println!(
            "  ... and {} more above the exhibition floor, all in the return.",
            dense_iron.len() - 34
        );
    }

    // ------------------------------------------------- CONTROL 1 + 5: the readings come apart
    println!();
    println!("  THE FUZZY POPULATION -- the densest surfaces, with their shortest separating words.");
    println!();
    let mut every_dense_separates = true;
    for (surface, _) in by_occurrence.iter().take(10) {
        let row = &far_sweep[surface];
        println!(
            "  {:?}  occ {}  windows {}  separated class pairs {}  separated occurrence pairs {}",
            census.surface(**surface),
            row.occurrences,
            row.distinct_windows,
            row.complex.separated_class_pairs(),
            row.separated_occurrence_pairs()
        );
        match row.shortest_separation(&census) {
            Some(separation) => println!("      {}", separation.exhibit(&census)),
            None => {
                every_dense_separates = false;
                println!("      NO SEPARATION EXHIBITED");
            }
        }
    }

    println!();
    println!(
        "  A dense surface's separating words -- the fuzziness exhibited, not scored. The WHOLE\n\
         \x20 population is materialized under this caller's declared capacity and then quotiented\n\
         \x20 by the word it exhibits, so what is printed is a complete census of the distinct\n\
         \x20 separations rather than a prefix of the pair list."
    );
    let holon = census.lookup("holon");
    if let Some(holon) = holon {
        let row = &far_sweep[&holon];
        println!();
        match row.exhibit(&census, DECLARED_CAPACITY) {
            Ok(separations) => {
                let mut distinct: BTreeMap<String, usize> = BTreeMap::new();
                for separation in &separations {
                    *distinct.entry(separation.exhibit(&census)).or_default() += 1;
                }
                println!(
                    "  {:?} at horizon {}: occ {}, {} distinct windows, {} separations returned \
                     WHOLE, {} distinct separating readings",
                    census.surface(holon),
                    HORIZONS[1],
                    row.occurrences,
                    row.distinct_windows,
                    separations.len(),
                    distinct.len()
                );
                let mut by_multiplicity: Vec<(&String, &usize)> = distinct.iter().collect();
                by_multiplicity.sort_by(|left, right| right.1.cmp(left.1).then(left.0.cmp(right.0)));
                for (exhibit, count) in by_multiplicity.iter().take(8) {
                    println!("      x{count:<5} {exhibit}");
                }
            }
            Err(obstruction) => println!(
                "  {:?} at horizon {}: OBSTRUCTED -- {obstruction}",
                census.surface(holon),
                HORIZONS[1]
            ),
        }
    }

    // And on a surface whose whole population this caller's capacity refuses: a NAMED complete
    // sub-population rather than a prefix. `exhibit_class` answers "everything that separates from
    // this one class", which is a smaller question answered whole -- the distinction that makes an
    // obstruction lawful where a truncation is not.
    let mut narrow_answered = false;
    if let Some(densest) = by_occurrence.first().map(|(surface, _)| **surface) {
        let row = &far_sweep[&densest];
        println!();
        match row.exhibit(&census, DECLARED_CAPACITY) {
            Err(obstruction) => {
                println!(
                    "  {:?}: the whole population is REFUSED -- {obstruction}\n\
                     \x20   so ask a narrower question instead of taking a prefix of the answer to \
                     the wide one:",
                    census.surface(densest)
                );
                let narrow = row.complex.exhibit_class(
                    &census,
                    0,
                    row.distinct_windows.saturating_sub(1) as u64,
                );
                match narrow {
                    Ok(separations) => {
                        narrow_answered = separations.len() == row.distinct_windows - 1;
                        let mut distinct: BTreeSet<String> = BTreeSet::new();
                        for separation in &separations {
                            distinct.insert(separation.exhibit(&census));
                        }
                        println!(
                            "     window class 0 against all {} others: {} separations returned \
                             WHOLE, {} distinct readings among them; the shallowest:\n       {}",
                            row.distinct_windows - 1,
                            separations.len(),
                            distinct.len(),
                            separations
                                .iter()
                                .min_by_key(|separation| separation.word.len())
                                .map(|separation| separation.exhibit(&census))
                                .unwrap_or_else(|| "<none>".to_owned())
                        );
                    }
                    Err(narrow_obstruction) => {
                        println!("     even the narrow question is refused: {narrow_obstruction}")
                    }
                }
            }
            Ok(separations) => {
                narrow_answered = true;
                println!(
                    "  {:?}: the whole population fits the declared capacity -- {} separations",
                    census.surface(densest),
                    separations.len()
                );
            }
        }
    }
    holds.push((
        "an obstructed width still answers a NAMED narrower question whole -- one window class \
         against every other -- rather than handing back a prefix of the wide answer"
            .to_owned(),
        narrow_answered,
        format!("declared capacity {DECLARED_CAPACITY} class pairs"),
    ));

    // Control 1: a dense separable surface and a sparse unseparated one, both exhibited.
    let dense_separable = by_occurrence
        .iter()
        .find(|(surface, _)| matches!(far_sweep[surface].verdict, Verdict::Separated { .. }))
        .map(|(surface, _)| **surface);
    let sparse_unseparated = far
        .iter()
        .copied()
        .filter(|surface| census.occurrences(*surface) >= EXHIBITION_FLOOR)
        .min_by_key(|surface| (census.occurrences(*surface), *surface));
    println!();
    match (dense_separable, sparse_unseparated) {
        (Some(dense), Some(sparse)) => {
            let dense_row = &far_sweep[&dense];
            let sparse_row = &far_sweep[&sparse];
            println!(
                "  CONTROL 1 -- the two readings come apart:\n\
                 \x20   DENSE AND SEPARABLE  {:?}: {} occurrences, {} conduct blocks, first \
                 separated at depth {}\n\
                 \x20   SPARSE AND UNSEPARATED {:?}: {} occurrences, 1 conduct block, no \
                 separating word exists within the horizon",
                census.surface(dense),
                dense_row.occurrences,
                dense_row.distinct_windows,
                dense_row.first_depth().unwrap_or(0),
                census.surface(sparse),
                sparse_row.occurrences,
            );
            holds.push((
                "control 1 -- density and separation come apart on the real corpus".to_owned(),
                dense_row.distinct_windows > 1
                    && sparse_row.distinct_windows == 1
                    && dense_row.occurrences > sparse_row.occurrences,
                format!(
                    "{:?} occ {} blocks {} vs {:?} occ {} blocks {}",
                    census.surface(dense),
                    dense_row.occurrences,
                    dense_row.distinct_windows,
                    census.surface(sparse),
                    sparse_row.occurrences,
                    sparse_row.distinct_windows
                ),
            ));
        }
        _ => holds.push((
            "control 1 -- density and separation come apart on the real corpus".to_owned(),
            false,
            "the corpus did not exhibit both shapes; the conjunction is doing no work".to_owned(),
        )),
    }
    holds.push((
        "every one of the ten densest surfaces separates and exhibits a word".to_owned(),
        every_dense_separates,
        format!("checked at horizon {}", HORIZONS[1]),
    ));

    // ------------------------------------------------- CONTROL 5: declared expectations
    println!();
    println!("  CONTROL 5 -- expectations declared in advance, and what the corpus returned.");
    println!();
    let mut expectations_held = true;
    for (name, expected_iron, basis, gating) in [
        (
            "arxiv",
            true,
            "occurs only inside a citation URL, so it should have one window",
            true,
        ),
        (
            "the",
            false,
            "the commonest English function word; it names no discrete object",
            true,
        ),
        (
            "holon",
            true,
            "canon/THE_DIALECT.md measures it the project's densest term of art, 1141 uses",
            false,
        ),
    ] {
        let Some(surface) = census.lookup(name) else {
            println!("  {name:<8} ABSENT from the declared corpus");
            if gating {
                expectations_held = false;
            }
            continue;
        };
        let row = &far_sweep[&surface];
        let actual = row.verdict.is_iron();
        let verdict = if actual == expected_iron { "HELD" } else { "REFUTED" };
        println!(
            "  {name:<8} expected {:<5} -> measured {:<5} [{verdict}]{}\n           occ {}, {} \
             conduct blocks at horizon {}\n           basis: {basis}",
            if expected_iron { "iron" } else { "fuzzy" },
            if actual { "iron" } else { "fuzzy" },
            if gating { "" } else { "  (declared, non-gating)" },
            row.occurrences,
            row.distinct_windows,
            HORIZONS[1],
        );
        if gating && actual != expected_iron {
            expectations_held = false;
        }
    }
    holds.push((
        "control 5 -- a surface expected iron is shown to be, and one expected fuzzy is shown to be"
            .to_owned(),
        expectations_held,
        "`arxiv` and `the`, declared before the reading".to_owned(),
    ));

    // ---------------------------------------------------------------- 4: the warping
    println!();
    println!("4 -- THE WARPING, AS AN INCIDENCE");
    println!("---------------------------------");
    println!(
        "A non-iron surface's position IS what it recruits and what recruits it, relative to the \n\
         iron ones. Declared radius {WARP_RADIUS}; both arms are directions, kept apart."
    );
    println!(
        "  DECLARED AXIS -- the WITNESSED iron at horizon {}, {} surfaces. The {} vacuously iron \n\
         \x20 surfaces (one occurrence each) are excluded from the axis by name and by count, for \n\
         \x20 the reason above: an axis that could not have been refuted is not a landmark.",
        HORIZONS[1],
        far_witnessed.len(),
        far.len() - far_witnessed.len()
    );
    let warping = warping_incidence(&census, far_witnessed, WARP_RADIUS);
    println!();
    println!(
        "  iron axes {}, nonzero incidence entries {}, rows that are themselves iron {}",
        warping.iron.len(),
        warping.nonzero(),
        warping.iron_rows
    );
    let touching: BTreeSet<SurfaceId> = warping.entries.keys().map(|(row, _)| *row).collect();
    println!(
        "  reach of the iron field: {} of {} measured surfaces stand within radius {WARP_RADIUS} of \n\
         \x20 a witnessed iron surface; {} stand outside it entirely and carry an EMPTY row, which \n\
         \x20 is a returned reading and not a gap.",
        touching.len(),
        word_surfaces.len(),
        word_surfaces.len() - touching.len()
    );
    println!();
    println!("  The widest warping supports, chosen by the data rather than by a probe list:");
    let mut widest: Vec<(SurfaceId, usize)> = touching
        .iter()
        .filter(|surface| !far_witnessed.contains(surface))
        .map(|surface| (*surface, warping.support_width(*surface)))
        .collect();
    widest.sort_by(|left, right| right.1.cmp(&left.1).then(left.0.cmp(&right.0)));
    for (surface, width) in widest.iter().take(8) {
        let row = warping.row(*surface);
        println!(
            "    {:<16} occ {:>6}  touches {:>3} iron axes; heaviest: {}",
            format!("{:?}", census.surface(*surface)),
            census.occurrences(*surface),
            width,
            row.iter()
                .take(3)
                .map(|(iron, recruitment)| format!(
                    "{:?}({}/{})",
                    census.surface(*iron),
                    recruitment.recruits,
                    recruitment.recruited_by
                ))
                .collect::<Vec<_>>()
                .join(" ")
        );
    }
    println!();
    let warp_probes: Vec<SurfaceId> = ["the", "and", "exact", "receiver", "holon", "abs", "doi"]
        .into_iter()
        .filter_map(|name| census.lookup(name))
        .collect();
    for probe in &warp_probes {
        let row = warping.row(*probe);
        println!(
            "  {:?} (occ {}, warping support width {})",
            census.surface(*probe),
            census.occurrences(*probe),
            warping.support_width(*probe)
        );
        if row.is_empty() {
            println!("      touches no iron axis within radius {WARP_RADIUS}");
            continue;
        }
        for (iron, recruitment) in row.iter().take(6) {
            println!(
                "      {:<20} recruits {:>6}   recruited by {:>6}",
                format!("{:?}", census.surface(*iron)),
                recruitment.recruits,
                recruitment.recruited_by
            );
        }
    }
    let widths: Vec<usize> = warp_probes
        .iter()
        .map(|probe| warping.support_width(*probe))
        .collect();
    holds.push((
        "the warping is a complex and not a table: the probed surfaces carry genuinely different \
         supports in the iron field"
            .to_owned(),
        widths.iter().collect::<BTreeSet<_>>().len() > 1 && warping.nonzero() > 0,
        format!("support widths {widths:?} over {} nonzero entries", warping.nonzero()),
    ));

    // ---------------------------------------------------------------- the surprisal carrier
    println!();
    println!("5 -- THE QUOTIENT'S OWN REFUSAL, DRIVEN ON REAL MATERIAL");
    println!("--------------------------------------------------------");
    println!(
        "A frequency becomes a probability only under a DECLARED receiver. Read the seed stratum's \n\
         population through the canon stratum's standing and the carrier must refuse the events \n\
         canon has no relation for -- not smooth them. `Support::found` then resolves one by \n\
         CHANGING THE SUPPORT, which moves every other event's surprisal because the denominator \n\
         moved."
    );
    let seed = census.stratum_population(Stratum::Seed);
    let mut canon = census.stratum_population(Stratum::Canon);
    let before = read_population(&seed, &canon).expect("both populations are exact");
    let unsupported: Vec<u64> = before
        .iter()
        .filter(|(_, support)| **support == Support::Unsupported)
        .map(|(event, _)| *event)
        .collect();
    println!();
    println!(
        "  seed events {}, canon standing {} events; UNSUPPORTED under canon: {}",
        seed.len(),
        canon.len(),
        unsupported.len()
    );
    println!(
        "  exhibited by name: {}",
        unsupported
            .iter()
            .take(10)
            .map(|event| format!("{:?}", census.surface(SurfaceId(*event as u32))))
            .collect::<Vec<_>>()
            .join(" ")
    );
    let cross_before = cross_entropy(&seed, &canon).expect("exact");
    println!(
        "  H(seed, canon) before FOUND: {}",
        match &cross_before {
            Support::Unsupported => "Unsupported -- the typed refusal, not a smoothing constant"
                .to_owned(),
            Support::Supported(form) => render_form(form),
        }
    );

    // A witness whose surprisal must MOVE when the support changes.
    let witness = canon
        .iter()
        .max_by(|left, right| left.1.cmp(right.1).then(right.0.cmp(left.0)))
        .map(|(event, _)| *event)
        .expect("the canon standing is not empty");
    let witness_before = Support::read(&canon, witness).expect("supported");
    for event in &unsupported {
        Support::found(&mut canon, *event);
    }
    let after = read_population(&seed, &canon).expect("exact");
    let still_unsupported = after
        .values()
        .filter(|support| **support == Support::Unsupported)
        .count();
    let cross_after = cross_entropy(&seed, &canon).expect("exact");
    let witness_after = Support::read(&canon, witness).expect("supported");
    let moved = match (&witness_before, &witness_after) {
        (Support::Supported(before), Support::Supported(after)) => {
            after.compare(before).expect("exact enclosures")
        }
        _ => ExactOrdering::Open,
    };
    println!(
        "  after FOUNDing all {} unsupported events: still unsupported {}",
        unsupported.len(),
        still_unsupported
    );
    println!(
        "  H(seed, canon) after FOUND:  {}",
        match &cross_after {
            Support::Unsupported => "Unsupported".to_owned(),
            Support::Supported(form) => render_form(form),
        }
    );
    println!(
        "  the witness {:?} was supported throughout; its surprisal moved: {:?} (a FOUND changes \
         the support, it does not smooth it)",
        census.surface(SurfaceId(witness as u32)),
        moved
    );
    holds.push((
        "control 7 -- the surprisal carrier refuses an unsupported event on real material, and the \
         FOUND resolves it by changing the support rather than by smoothing"
            .to_owned(),
        cross_before == Support::Unsupported
            && !unsupported.is_empty()
            && still_unsupported == 0
            && matches!(cross_after, Support::Supported(_))
            && moved == ExactOrdering::Greater,
        format!(
            "{} refusals -> 0 after FOUND; the witness's surprisal moved {moved:?}",
            unsupported.len()
        ),
    ));

    // The four-state ordering, on corpus material.
    println!();
    println!(
        "  The ordering is four-state and the grain is what moves it -- `Open` is a statement \n\
         about the receiver's grain, never about the forms."
    );
    let mut by_count: BTreeMap<u64, Vec<SurfaceId>> = BTreeMap::new();
    for surface in &word_surfaces {
        by_count
            .entry(census.occurrences(*surface))
            .or_default()
            .push(*surface);
    }

    // A pair the DECLARED grain separates and a coarse one cannot. Searched over the corpus's own
    // material rather than authored: the widest gap that still returns `Open` coarsely is the pair
    // of adjacent occurrence counts, because S(n/T) - S((n+1)/T) = log2(n+1) - log2(n), and every
    // prime of the total cancels.
    let mut ordering_nonvacuous = false;
    let mut near_pair = None;
    for (count, group) in by_count.iter().rev() {
        if let Some(next) = by_count.get(&(count + 1)) {
            near_pair = Some((group[0], next[0], *count, count + 1));
            break;
        }
    }
    if let Some((left, right, left_count, right_count)) = near_pair
        && let (Support::Supported(left_form), Support::Supported(right_form)) =
            (&density[&left].surprisal, &density[&right].surprisal)
    {
        let fine = left_form.compare_grain(right_form, Grain::DECLARED).expect("exact");
        let coarse = left_form.compare_grain(right_form, Grain::at(1, 4)).expect("exact");
        println!(
            "    S({:?}) at {left_count} occ vs S({:?}) at {right_count} occ: {:?} at {}, {:?} at {}",
            census.surface(left),
            census.surface(right),
            fine,
            Grain::DECLARED,
            coarse,
            Grain::at(1, 4)
        );
        ordering_nonvacuous = fine != ExactOrdering::Open && coarse == ExactOrdering::Open;
    }
    // And a far-apart pair, so the coarse grain is shown to decide sometimes rather than always
    // refusing -- otherwise `Open` would be a property of the grain and not of the pair.
    if let (Some(left), Some(right)) = (census.lookup("holon"), census.lookup("receiver"))
        && let (Support::Supported(left_form), Support::Supported(right_form)) =
            (&density[&left].surprisal, &density[&right].surprisal)
    {
        println!(
            "    S({:?}) vs S({:?}), 35x apart: {:?} at {} -- the coarse grain decides when the \
             forms are far enough, so `Open` is about the PAIR and the grain together",
            census.surface(left),
            census.surface(right),
            left_form.compare_grain(right_form, Grain::at(1, 4)).expect("exact"),
            Grain::at(1, 4)
        );
    }
    // Equality is decided on coefficients, before any enclosure is taken.
    let mut equal_pair = None;
    for (count, group) in by_count.iter().rev() {
        if group.len() >= 2 && *count > 1 {
            equal_pair = Some((group[0], group[1], *count));
            break;
        }
    }
    let mut equality_exact = false;
    if let Some((left, right, count)) = equal_pair
        && let (Support::Supported(left_form), Support::Supported(right_form)) =
            (&density[&left].surprisal, &density[&right].surprisal)
    {
        let verdict = left_form.compare_grain(right_form, Grain::at(1, 4)).expect("exact");
        println!(
            "    S({:?}) vs S({:?}), both at {count} occurrences: {:?} at the COARSEST grain -- \
             equality is decided on coefficients before any enclosure",
            census.surface(left),
            census.surface(right),
            verdict
        );
        equality_exact = verdict == ExactOrdering::Equal;
    }
    holds.push((
        "the four-state ordering is non-vacuous on corpus material: one pair decides at the \
         declared grain and returns `Open` at a coarse one, and an equal pair returns `Equal` at \
         the coarsest grain with no enclosure taken"
            .to_owned(),
        ordering_nonvacuous && equality_exact,
        format!("Open-at-coarse: {ordering_nonvacuous}, exact Equal: {equality_exact}"),
    ));

    // ---------------------------------------------------------- 6: the excision's own orbit
    println!();
    println!("6 -- WHAT THE TWO EXCISED LEVELS WERE WITHHOLDING");
    println!("-------------------------------------------------");
    println!(
        "`canon/THE_CONTAMINANT_PROTOCOL.md` §4: lift the level, re-run the declared material,\n\
         exhibit the difference. `WINDOW_APERTURE = 64` presented the first 64 distinct windows per\n\
         surface IN CORPUS ORDER and reported the conduct-block count of that subsample;\n\
         `SEPARATION_EXHIBIT = 512` then kept the first 512 separations of what was left. Both were\n\
         silent: the return was a prefix and a count, and no caller could tell it from the whole."
    );
    println!();
    println!(
        "  {:<8} {:>12} {:>14} {:>16} {:>18} {:>18}",
        "horizon", "capped", "windows lost", "old cap on pairs", "old pairs kept", "whole pairs"
    );
    let mut orbit_moved = false;
    for horizon in HORIZONS {
        let reading = &sweeps[&horizon];
        let capped = reading
            .values()
            .filter(|row| row.distinct_windows > EXCISED_WINDOW_APERTURE)
            .count();
        let windows_lost: usize = reading
            .values()
            .map(|row| row.distinct_windows.saturating_sub(EXCISED_WINDOW_APERTURE))
            .sum();
        let old_found: BigUint = reading
            .values()
            .map(|row| pairs_of(row.distinct_windows.min(EXCISED_WINDOW_APERTURE)))
            .sum();
        let old_kept: BigUint = reading
            .values()
            .map(|row| {
                pairs_of(row.distinct_windows.min(EXCISED_WINDOW_APERTURE))
                    .min(BigUint::from(EXCISED_SEPARATION_EXHIBIT))
            })
            .sum();
        let whole: BigUint = reading
            .values()
            .map(|row| row.complex.separated_class_pairs())
            .sum();
        if capped > 0 && whole > old_kept {
            orbit_moved = true;
        }
        println!(
            "  {horizon:<8} {capped:>12} {windows_lost:>14} {old_found:>16} {old_kept:>18} \
             {whole:>18}"
        );
    }
    holds.push((
        "the excised levels were DECIDING the reading, not bounding an unreached ceiling: on the \
         declared corpus the window aperture cut the presented population and the separation cap \
         cut the return"
            .to_owned(),
        orbit_moved,
        "measured at both horizons in the table above".to_owned(),
    ));

    // The distinguishing material: a separation between two window classes the old aperture never
    // presented. Under `WINDOW_APERTURE = 64` this pair did not exist for any caller.
    println!();
    println!(
        "  THE DISTINGUISHING MATERIAL. A separation between two window classes that both sat past\n\
         \x20 the old aperture's first-64-in-corpus-order selection. Under the excised constant no\n\
         \x20 caller could reach either side of it, at any capacity, because the population was cut\n\
         \x20 before the organ ever saw it."
    );
    let mut exhibited_withheld = false;
    for name in ["holon", "receiver", "exact", "the"] {
        let Some(surface) = census.lookup(name) else {
            continue;
        };
        let row = &far_sweep[&surface];
        if row.distinct_windows <= EXCISED_WINDOW_APERTURE {
            continue;
        }
        let presented = old_aperture_selection(&census, surface, HORIZONS[1], row);
        let withheld: Vec<usize> = (0..row.distinct_windows)
            .filter(|class| !presented.contains(class))
            .collect();
        if withheld.len() < 2 {
            continue;
        }
        let (left, right) = (withheld[0], withheld[withheld.len() - 1]);
        let Some(separation) = row.complex.separation_between(&census, left, right) else {
            continue;
        };
        println!();
        println!(
            "  {:?} at horizon {}: {} window classes, {} of them withheld by the old aperture.\n\
             \x20   class {} vs class {} -- neither was ever presented:\n      {}\n\
             \x20   and it stands for {} separated occurrence pairs ({} x {}).",
            census.surface(surface),
            HORIZONS[1],
            row.distinct_windows,
            withheld.len(),
            left,
            right,
            separation.exhibit(&census),
            separation.occurrence_pairs(),
            separation.left_occurrences,
            separation.right_occurrences,
        );
        exhibited_withheld = true;
        break;
    }
    holds.push((
        "the excision exhibits its own distinguishing material: a separating word between two \
         window classes the old aperture withheld from every caller"
            .to_owned(),
        exhibited_withheld,
        "searched over the declared probes in corpus order".to_owned(),
    ));

    // ---------------------------------------------------------------- verdicts
    println!();
    println!("DECLARED CONTROLS");
    println!("-----------------");
    let mut failed = 0;
    for (claim, held, evidence) in &holds {
        if *held {
            println!("  [holds] {claim}\n            {evidence}");
        } else {
            failed += 1;
            println!("  [FAILS] {claim}\n            {evidence}");
        }
    }
    println!();
    if failed == 0 {
        println!("HELD -- {} declared controls, 0 failed", holds.len());
    } else {
        println!(
            "FAILED -- {failed} of {} declared controls did not hold",
            holds.len()
        );
        std::process::exit(1);
    }
}

/// `C(n,2)`, exact.
fn pairs_of(population: usize) -> BigUint {
    if population < 2 {
        return BigUint::from(0u32);
    }
    BigUint::from(population) * BigUint::from(population - 1) / BigUint::from(2u32)
}

/// Which window classes the excised `WINDOW_APERTURE = 64` would have presented: the first 64
/// distinct windows **in corpus order**, which is the order `CorpusCensus::sites` returns.
///
/// Reconstructed rather than remembered, so the orbit is measured against what the old code did and
/// not against a description of it. Note what the selection depended on: file traversal order.
fn old_aperture_selection(
    census: &CorpusCensus,
    surface: SurfaceId,
    horizon: usize,
    row: &SeparationReading,
) -> BTreeSet<usize> {
    let index: BTreeMap<&Vec<Option<(u64, u64, u64)>>, usize> = row
        .complex
        .classes
        .iter()
        .enumerate()
        .map(|(position, class)| (&class.window, position))
        .collect();
    let mut selected = BTreeSet::new();
    for (whole, position) in census.sites(surface) {
        if selected.len() >= EXCISED_WINDOW_APERTURE {
            break;
        }
        let reading = window(census, *whole, *position, horizon);
        if let Some(class) = index.get(&reading) {
            selected.insert(*class);
        }
    }
    selected
}

fn render_support(support: &Support) -> String {
    match support {
        Support::Unsupported => "Unsupported (FOUNDs)".to_owned(),
        Support::Supported(form) => render_form(form),
    }
}

/// A form's leading terms and its size. `named()` in full is unbounded for a cross-entropy form.
fn render_form(form: &SymbolicSurprisal) -> String {
    let terms = form.terms();
    if terms.len() <= 4 {
        return form.named();
    }
    let head: Vec<String> = terms
        .iter()
        .take(3)
        .map(|(prime, coefficient)| format!("{coefficient}*log2({prime})"))
        .collect();
    format!("{} + ... [{} prime axes]", head.join(" + "), terms.len())
}
