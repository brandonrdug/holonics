//! The verdict that sits beside iron: a surface used variously that conduct still cannot pull apart.
//!
//! ## The question, and why the iron reading answers a different one
//!
//! `the_iron_tokens_carry_the_field` measures **iron**: `distinct_windows == 1`, a surface the
//! corpus never once used in a context the declared family can tell apart. On the real corpus that
//! reading is dominated by **formulaic** surfaces — a citation fragment, a timestamp, a domain
//! name — which is the reading working correctly.
//!
//! It is not the object Brandon named. His words, as `corpus_census.rs` and
//! `the_iron_tokens_carry_the_field.rs` already carry them:
//!
//! > *"if in the English we use about mathematics, there are certain words that are used
//! > invariantly to refer to a discrete kind of object… If the words are not necessarily hard-coded
//! > as invariants, but the machine experiences them as invariants associated with particular
//! > meanings, then perhaps its language comprehension would implicitly curve around those **iron
//! > recurrences (density)**. It would give implicit meaning to words that warp around the usage of
//! > invariant tokens… The density and invariants it founds are not ours to necessarily author,
//! > they are happenstance of our own writing."*
//!
//! **`tensor` is not iron precisely because it is used variously**, and by `canon/MEANING_DEFINED.md`
//! that is what makes it meaningful rather than what disqualifies it:
//!
//! > *"the meaning of the token depends on the context it is used in, and **what we mean by
//! > *meaning* is that the transport phase distributions are similar and recurring in frequency
//! > distributions**"*
//!
//! So the object is the **opposite pole**: many distinct windows that nonetheless land in one
//! conduct block.
//!
//! ## The theorem that decides where the verdict can be stated
//!
//! At the **full** declared family that statement is unsatisfiable, and this is a theorem of
//! `token_invariance` rather than a property of any corpus. Two occurrences separate exactly when
//! their windows differ, so the conduct-block count of a surface's occurrence population **is** its
//! distinct-window count — which is what `cross_check` asserts when it requires
//! `classes == conduct_blocks`. `windows > 1 && blocks == 1` therefore holds for no surface, at no
//! horizon, on no material, and a deeper horizon only separates more.
//!
//! **The collapse cannot come from refining. It can only come from coarsening the receiver family.**
//! So the verdict names the family at which it happens:
//!
//! > A surface is **conduct-invariant** when the full declared family separates its occurrences —
//! > `distinct_windows > 1`, so it is genuinely used variously — while some **nonempty** declared
//! > sub-family holds them all in **one conduct block**.
//!
//! The collapsing families are downward closed with a single maximal element, so the verdict does
//! not search: `F` collapses iff `F ⊆ constant_axes(s)` and the terminus pattern does not vary.
//! `constant_axes` is the maximal collapsing family and its complement is what the material moved.
//!
//! ## The declared controls
//!
//! 1. **The two verdicts partition the measured population**, they are taken from **one** sweep on
//!    **one** material, and they agree exactly on iron. Checked, not asserted in prose.
//! 2. **The verdict cannot be vacuous**, and unlike iron it does not need a separate clause to say
//!    so: `windows > 1` forces at least one separated occurrence pair, and the exact count of pairs
//!    the full family separates and the collapsing family holds is carried by every reading.
//! 3. **The collapsing family is a nonempty PROPER subset.** All three axes constant with a constant
//!    terminus pattern is one window, which is iron. So every admitted surface exhibits both the
//!    axes its material held and the axes its material moved.
//! 4. **The orbit is non-trivial.** Every collapsing family that appears is reported with its
//!    population, and every family that appears **zero** times is reported as zero. A verdict whose
//!    families all coincide has not been shown to be a family.
//! 5. **The independent implementation grades it.** `receiver_exact_compression` is run at every one
//!    of the eight declared sub-families, including the empty one, and its conduct-block count must
//!    equal the projection's and must agree with what the verdict claimed.
//! 6. **The separation the collapsing family deletes is exhibited**, with the receiver that saw it,
//!    and that receiver must lie **outside** the collapsing family — and must never be a terminus,
//!    because a terminus is not a receiver's to delete.
//! 7. **The aperture law is held, not widened.** The verdict is computed off the sorted window
//!    classes in `O(d · horizon)` and never materializes a pair, so a surface whose exhibition the
//!    declared capacity refuses still receives a verdict whole. Both halves are shown on the same
//!    surface.
//! 8. **The prediction is declared in advance and reported either way.** `tensor`, `vector`,
//!    `lemma`, `group`, `field` are looked up by name. A refuted prediction reported honestly is
//!    worth more than a tuned one.
//!
//! ## Reading the output
//!
//! Nothing here ranks. Populations are returned whole or as a **stated** sub-population with its
//! residual named — never a prefix. Where a presentation is ordered it is ordered for reading and
//! decides nothing, which is the same rule `WarpingIncidence::row` states.

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

use num_bigint::BigUint;

use holonic_engine::corpus_census::{CorpusCensus, DECLARED_STRATA, Kind, SurfaceId};
use holonic_engine::token_invariance::{
    ConductAtlas, ConductVerdict, ReceiverAxis, ReceiverFamily, SeparationReading,
    collapsing_family_population, conduct_invariance_at, cross_check_family, invariance_partition,
    iron_at, sweep, witnessed_iron_at,
};

/// The declared horizons. Both are taken, but only the **last** sweep is retained: the earlier ones
/// contribute their verdict sets and are dropped, so peak standing is one sweep rather than two.
const HORIZONS: [usize; 2] = [1, 2];

/// The capacity this caller declares for anything quadratic. Past it the organ refuses with the
/// width the material required, and the refusal is reported rather than worked around.
const DECLARED_CAPACITY: u64 = 8_192;

/// The capacity this caller declares for the **sub-family** cross-check specifically. It is smaller
/// than [`DECLARED_CAPACITY`] for a stated reason: at [`ReceiverFamily::EMPTY`] the organ's one-shot
/// partition is a single block containing every item, so its pair search is quadratic in the whole
/// presented population rather than in the separated part. Past this it refuses and the refusal is
/// counted.
const FAMILY_CHECK_CAPACITY: u64 = 64;

/// **The horizon this caller founds the conduct axis at.** The fourth declared axis reads what the
/// corpus does with a surface rather than how it is spelled; `ConductAtlas` holds no default, so the
/// founding horizon is declared here and the reading horizons separately in [`HORIZONS`].
const FOUNDING_HORIZON: usize = 1;

/// The default floor above which the conduct-invariant population is written out **complete**.
/// A presentation capacity the caller declares — the second command-line argument overrides it —
/// and never a filter on the reading: the whole population is counted, the occurrence distribution
/// below the floor is printed complete, and the residual is named.
const DEFAULT_EXHIBIT_FLOOR: u64 = 6;

/// The prediction, declared before the sweep runs. `canon/MEANING_DEFINED.md` and Brandon's own
/// statement name `tensor` and `vector`; the other three are the same shape in the same material.
const PREDICTED: [&str; 10] = [
    "tensor", "vector", "lemma", "group", "field", "Tensor", "Vector", "Lemma", "Group", "Field",
];

/// The project's own dialect, from `canon/THE_DIALECT.md`, as a second frame on the same question.
const DIALECT: [&str; 6] = ["holon", "receiver", "current", "passage", "residual", "exact"];

fn main() {
    let root = std::env::args().nth(1).map(PathBuf::from).unwrap_or_else(|| {
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("..").join("..")
    });
    let exhibit_floor: u64 = std::env::args()
        .nth(2)
        .and_then(|value| value.parse().ok())
        .unwrap_or(DEFAULT_EXHIBIT_FLOOR);

    let census = match CorpusCensus::read(&root) {
        Ok(census) => census,
        Err(error) => {
            println!("the declared corpus could not be read: {error}");
            std::process::exit(1);
        }
    };

    let atlas = ConductAtlas::found(&census, FOUNDING_HORIZON);

    let mut holds: Vec<(String, bool, String)> = Vec::new();

    println!("THE TOKEN HOLDS AN AXIS WHILE ITS WINDOWS VARY");
    println!("==============================================");
    println!();
    println!("The verdict that sits beside iron. Iron is `distinct_windows == 1`; this is many");
    println!("windows held in ONE conduct block by a coarser declared family.");
    println!();

    // ------------------------------------------------------------------ the declared corpus
    println!("THE DECLARED CORPUS");
    println!("-------------------");
    println!();
    println!(
        "  {:<9} {:<34} {:>7} {:>12} {:>10}",
        "stratum", "root", "wholes", "word tokens", "distinct"
    );
    for declaration in DECLARED_STRATA {
        let wholes = census
            .wholes()
            .iter()
            .filter(|whole| whole.stratum == declaration.stratum)
            .count();
        let population = census.stratum_population(declaration.stratum);
        let tokens: BigUint = population.values().sum();
        println!(
            "  {:<9} {:<34} {:>7} {:>12} {:>10}",
            declaration.stratum.name(),
            format!("{}/*.{}", declaration.relative_root, declaration.extension),
            wholes,
            tokens,
            population.len()
        );
    }
    let measured = census.word_surfaces().len();
    println!();
    println!(
        "  total stream        {} tokens ({} word, {} markup)",
        census.total_occurrences(),
        census.word_occurrences(),
        census.total_occurrences() - census.word_occurrences()
    );
    println!("  measured population {measured} distinct word surfaces");

    // ---------------------------------------------------- why the verdict is stated at a family
    println!();
    println!("WHY THE VERDICT IS STATED AT A FAMILY AND NOT AT A HORIZON");
    println!("---------------------------------------------------------");
    println!();
    println!(
        "  Two occurrences separate exactly when their windows differ, so the conduct-block count\n  \
         of a surface's occurrence population IS its distinct-window count. `cross_check` asserts\n  \
         it. So `windows > 1 && blocks == 1` is unsatisfiable at the FULL family -- for every\n  \
         surface, at every horizon, on every material -- and a deeper horizon only separates more.\n  \
         The collapse can only come from COARSENING the receiver family, so the verdict names the\n  \
         family it happens at. Measured below rather than argued."
    );

    // ------------------------------------------------------------------------ the sweep
    let mut earlier: BTreeMap<usize, (BTreeSet<SurfaceId>, BTreeSet<SurfaceId>)> = BTreeMap::new();
    let mut retained: Option<(usize, BTreeMap<SurfaceId, SeparationReading>)> = None;
    for (index, horizon) in HORIZONS.into_iter().enumerate() {
        let reading = sweep(&census, &atlas, horizon);
        let partition = invariance_partition(&reading);
        earlier.insert(
            horizon,
            (
                iron_at(&reading),
                partition.conduct_invariant.iter().copied().collect(),
            ),
        );
        if index + 1 == HORIZONS.len() {
            retained = Some((horizon, reading));
        }
    }
    let (horizon, reading) = retained.expect("at least one declared horizon");
    let partition = invariance_partition(&reading);
    let invariance = conduct_invariance_at(&reading);
    let iron = iron_at(&reading);
    let witnessed = witnessed_iron_at(&reading);

    println!();
    println!("THE THREE-WAY PARTITION OF THE MEASURED POPULATION, AT HORIZON {horizon}");
    println!("--------------------------------------------------------------");
    println!();
    println!(
        "  {:<26} {:>9}   {}",
        "verdict", "surfaces", "what it says"
    );
    println!(
        "  {:<26} {:>9}   {}",
        "IRON, witnessed",
        partition.witnessed_iron.len(),
        "one window, and a pair could have refuted it"
    );
    println!(
        "  {:<26} {:>9}   {}",
        "IRON, vacuous",
        partition.vacuously_iron.len(),
        "one window on fewer than two occurrences"
    );
    println!(
        "  {:<26} {:>9}   {}",
        "CONDUCT-INVARIANT",
        partition.conduct_invariant.len(),
        "many windows, ONE block at a coarser family"
    );
    println!(
        "  {:<26} {:>9}   {}",
        "varying",
        partition.varying.len(),
        "many windows, no family holds them"
    );
    println!("  {:<26} {:>9}", "total", partition.total());

    let varying_by_terminus = invariance
        .values()
        .filter(|row| matches!(row.verdict, ConductVerdict::Varying { terminus_varies: true, .. }))
        .count();
    println!();
    println!(
        "  Of the {} varying surfaces, {} vary by TERMINUS -- their occurrences disagree about\n  \
         whether an offset exists at all, which no ablation can repair, so they are separated even\n  \
         by the empty family. The other {} vary because every declared axis moved.",
        partition.varying.len(),
        varying_by_terminus,
        partition.varying.len() - varying_by_terminus
    );

    holds.push((
        "control 1 -- the two verdicts partition the measured population from ONE sweep, and \
         agree exactly on iron"
            .to_owned(),
        partition.is_a_partition(measured)
            && iron
                == partition
                    .vacuously_iron
                    .union(&partition.witnessed_iron)
                    .copied()
                    .collect::<BTreeSet<_>>()
            && iron.is_disjoint(&partition.conduct_invariant),
        format!(
            "{} blocks summing to {} over {} measured surfaces; iron = {} = {} vacuous + {} \
             witnessed; conduct-invariant disjoint from iron",
            4,
            partition.total(),
            measured,
            iron.len(),
            partition.vacuously_iron.len(),
            witnessed.len()
        ),
    ));

    // The literal statement at the full family, measured rather than argued.
    let literal = reading
        .values()
        .filter(|row| row.distinct_windows > 1 && row.family_blocks(ReceiverFamily::FULL) == 1)
        .count();
    holds.push((
        "the literal statement `windows > 1 && blocks == 1` is EMPTY at the full family -- \
         measured over every surface, not assumed"
            .to_owned(),
        literal == 0,
        format!("{literal} surfaces at horizon {horizon}"),
    ));

    // --------------------------------------------------------- the orbit of collapsing families
    println!();
    println!("THE ORBIT: WHICH DECLARED FAMILIES ACTUALLY COLLAPSE SOMETHING");
    println!("--------------------------------------------------------------");
    println!();
    let population = collapsing_family_population(&reading);
    println!("  {:<22} {:>9}   {}", "collapsing family", "surfaces", "axes the material MOVED");
    let mut nonempty_families = 0usize;
    for family in ReceiverFamily::FULL.subsets() {
        if family.is_empty() || family == ReceiverFamily::FULL {
            continue;
        }
        let members = population.get(&family).map(BTreeSet::len).unwrap_or(0);
        if members > 0 {
            nonempty_families += 1;
        }
        println!(
            "  {:<22} {:>9}   {}",
            family.to_string(),
            members,
            family.complement()
        );
    }
    println!();
    println!(
        "  A family reported at zero is reported, not omitted. `{{}}` and `{}` are excluded by the\n  \
         verdict itself: the empty family certifies nothing, and the full family collapsing means\n  \
         one window, which is iron.",
        ReceiverFamily::FULL
    );

    // Per-axis: how often each axis is the thing held, and how often it is the thing moved.
    println!();
    println!("  {:<10} {:>16} {:>16}", "axis", "held (collapsing)", "moved");
    for axis in ReceiverAxis::DECLARED {
        let held = invariance
            .values()
            .filter(|row| row.verdict.is_conduct_invariant() && row.constant_axes.contains(axis))
            .count();
        let moved = invariance
            .values()
            .filter(|row| row.verdict.is_conduct_invariant() && row.varying_axes().contains(axis))
            .count();
        println!("  {:<10} {:>16} {:>16}", axis.name(), held, moved);
    }

    holds.push((
        "control 4 -- the orbit is non-trivial: more than one declared family collapses a \
         non-empty population, and every axis is both held and moved somewhere"
            .to_owned(),
        nonempty_families >= 2
            && ReceiverAxis::DECLARED.into_iter().all(|axis| {
                invariance
                    .values()
                    .any(|row| row.verdict.is_conduct_invariant() && row.constant_axes.contains(axis))
                    && invariance.values().any(|row| {
                        row.verdict.is_conduct_invariant() && row.varying_axes().contains(axis)
                    })
            }),
        format!(
            "{nonempty_families} of {} proper nonempty families carry a population",
            ReceiverFamily::FULL.subsets().len() - 2
        ),
    ));

    // ------------------------------------------------------------- the population, exhibited
    println!();
    println!("THE CONDUCT-INVARIANT POPULATION, EXHIBITED");
    println!("-------------------------------------------");
    println!();

    // The complete occurrence distribution first, so nothing below the exhibition floor is hidden.
    let mut distribution: BTreeMap<u64, usize> = BTreeMap::new();
    for surface in &partition.conduct_invariant {
        *distribution.entry(census.occurrences(*surface)).or_default() += 1;
    }
    println!("  The COMPLETE occurrence distribution of the population (nothing is cut here):");
    println!();
    let mut line = String::new();
    for (occurrences, count) in &distribution {
        line.push_str(&format!("{occurrences}x{count}  "));
        if line.len() > 96 {
            println!("    {}", line.trim_end());
            line.clear();
        }
    }
    if !line.is_empty() {
        println!("    {}", line.trim_end());
    }
    let above: Vec<SurfaceId> = partition
        .conduct_invariant
        .iter()
        .copied()
        .filter(|surface| census.occurrences(*surface) >= exhibit_floor)
        .collect();
    println!();
    println!(
        "  Written out COMPLETE at occurrences >= {exhibit_floor}: {} surfaces. The remaining {} \n  \
         stand below {exhibit_floor} occurrences and are counted in the distribution above rather\n  \
         than truncated here -- a stated sub-population, never a prefix.",
        above.len(),
        partition.conduct_invariant.len() - above.len(),
    );
    println!();
    println!(
        "  {:<20} {:>5} {:>8} {:>13}  {:<20} {}",
        "surface", "occ", "windows", "withstood", "collapsing", "moved"
    );
    // Presented in descending occurrence for reading. This decides nothing: the population above is
    // the return, and every member of it is printed.
    let mut ordered: Vec<SurfaceId> = partition.conduct_invariant.iter().copied().collect();
    ordered.sort_by_key(|surface| {
        (
            std::cmp::Reverse(census.occurrences(*surface)),
            census.surface(*surface).to_owned(),
        )
    });
    for surface in ordered.iter().filter(|s| census.occurrences(**s) >= exhibit_floor) {
        let row = &invariance[surface];
        println!(
            "  {:<20} {:>5} {:>8} {:>13}  {:<20} {}",
            format!("{:?}", census.surface(*surface)),
            row.occurrences,
            row.windows,
            row.separations_withstood,
            row.constant_axes.to_string(),
            row.varying_axes()
        );
    }

    // ------------------------------------------------- the separation the collapsing family deletes
    println!();
    println!("WHAT THE COLLAPSING FAMILY DELETES, EXHIBITED");
    println!("---------------------------------------------");
    println!();
    println!(
        "  For a conduct-invariant surface the FULL family does separate its occurrences. The\n  \
         shortest separating word is exhibited with the receiver that saw it, and that receiver\n  \
         must lie OUTSIDE the collapsing family -- and must never be a terminus.\n"
    );
    let mut outside_ok = true;
    let mut terminus_ok = true;
    let mut exhibited = 0usize;
    for surface in &ordered {
        let row = &reading[surface];
        let Some(separation) = row.shortest_separation(&census) else {
            outside_ok = false;
            continue;
        };
        let collapsing = invariance[surface].constant_axes;
        if separation.by_terminus {
            terminus_ok = false;
        }
        match separation.axis {
            Some(axis) if !collapsing.contains(axis) => {}
            _ => outside_ok = false,
        }
        if exhibited < 8 {
            println!(
                "    {:<18} collapsing {:<20} {}",
                format!("{:?}", census.surface(*surface)),
                collapsing.to_string(),
                separation.exhibit(&census)
            );
            exhibited += 1;
        }
    }
    holds.push((
        "control 6 -- every conduct-invariant surface's shortest full-family separation is \
         witnessed by an axis OUTSIDE its collapsing family, and never by a terminus"
            .to_owned(),
        outside_ok && terminus_ok && !partition.conduct_invariant.is_empty(),
        format!(
            "{} surfaces checked; outside={outside_ok} no-terminus={terminus_ok}",
            partition.conduct_invariant.len()
        ),
    ));

    // ------------------------------------------------------------------- the prediction
    println!();
    println!("THE DECLARED PREDICTION, REPORTED EITHER WAY");
    println!("--------------------------------------------");
    println!();
    println!(
        "  A verdict alone would say only yes or no. The block count at each of the three coarsest\n  \
         declared families says WHERE the surface sits: `blocks` is how many conduct blocks that\n  \
         family leaves, and `1` is the collapse. `min` is the fewest blocks any nonempty declared\n  \
         family achieves, which is how near the pole the material actually comes.\n"
    );
    println!(
        "  {:<14} {:>6} {:>8} {:>7} {:>8} {:>9} {:>9} {:>6}  {}",
        "surface", "occ", "windows", "{kind}", "{weight}", "{density}", "{conduct}", "min",
        "verdict"
    );
    let mut predicted_hits = 0usize;
    let mut predicted_present = 0usize;
    for name in PREDICTED.into_iter().chain(DIALECT) {
        let Some(surface) = census.lookup(name) else {
            println!("  {:<14} {:>6}", format!("{name:?}"), "absent");
            continue;
        };
        let Some(row) = reading.get(&surface) else {
            println!("  {:<14} {:>6}", format!("{name:?}"), "markup");
            continue;
        };
        predicted_present += 1;
        let inv = row.conduct_invariance();
        let verdict = match inv.verdict {
            ConductVerdict::Iron => "IRON".to_owned(),
            ConductVerdict::ConductInvariant { collapsing, .. } => {
                if PREDICTED.contains(&name) {
                    predicted_hits += 1;
                }
                format!("CONDUCT-INVARIANT at {collapsing}")
            }
            ConductVerdict::Varying { terminus_varies, .. } => {
                if terminus_varies {
                    "varying (by TERMINUS -- no family can)".to_owned()
                } else {
                    "varying (every axis moved)".to_owned()
                }
            }
        };
        let at = |axis: ReceiverAxis| row.family_blocks(ReceiverFamily::of([axis]));
        let least = ReceiverFamily::FULL
            .subsets()
            .into_iter()
            .filter(|family| !family.is_empty())
            .map(|family| row.family_blocks(family))
            .min()
            .unwrap_or(row.distinct_windows);
        println!(
            "  {:<14} {:>6} {:>8} {:>7} {:>8} {:>9} {:>9} {:>6}  {}",
            format!("{name:?}"),
            row.occurrences,
            row.distinct_windows,
            at(ReceiverAxis::Kind),
            at(ReceiverAxis::Weight),
            at(ReceiverAxis::Density),
            at(ReceiverAxis::Conduct),
            least,
            verdict
        );
    }
    println!();
    println!(
        "  {predicted_hits} of the {} predicted mathematical surfaces present in this corpus \
         returned CONDUCT-INVARIANT.",
        PREDICTED.into_iter().filter(|name| census.lookup(name).is_some()).count()
    );
    holds.push((
        "control 8 -- the declared prediction was looked up by name and reported whichever way it \
         came out"
            .to_owned(),
        predicted_present > 0,
        format!(
            "{predicted_present} of {} declared surfaces present; {predicted_hits} of the \
             mathematical ones conduct-invariant",
            PREDICTED.len() + DIALECT.len()
        ),
    ));

    // ------------------------------------------------------------------- the aperture law
    println!();
    println!("THE APERTURE LAW, HELD RATHER THAN WIDENED");
    println!("------------------------------------------");
    println!();
    let mut obstructed_and_read = 0usize;
    let mut obstructed_exhibited: Vec<(SurfaceId, BigUint)> = Vec::new();
    // The width is read off the complex in O(1) and the typed refusal is then DRIVEN on exactly the
    // surfaces that exceed the capacity. Materializing every surface's population merely to discover
    // it fits would be the aperture law inverted.
    let capacity = BigUint::from(DECLARED_CAPACITY);
    for (surface, row) in &reading {
        if row.complex.separated_class_pairs() > capacity {
            let obstruction = row
                .exhibit(&census, DECLARED_CAPACITY)
                .expect_err("a width past the declared capacity must refuse");
            obstructed_and_read += 1;
            if obstructed_exhibited.len() < 4 {
                obstructed_exhibited.push((*surface, obstruction.required.clone()));
            }
        }
    }
    // The other arm, driven too: a population inside the capacity comes back WHOLE, and its size is
    // exactly the width the complex predicted. An obstruction organ that never returns is not one.
    let mut whole_returns = 0usize;
    let mut whole_matched = true;
    for surface in ordered.iter().take(32) {
        let row = &reading[surface];
        match row.exhibit(&census, DECLARED_CAPACITY) {
            Ok(separations) => {
                whole_returns += 1;
                if BigUint::from(separations.len()) != row.complex.separated_class_pairs() {
                    whole_matched = false;
                }
            }
            Err(_) => {}
        }
    }
    for (surface, required) in &obstructed_exhibited {
        let row = &reading[surface];
        let inv = row.conduct_invariance();
        println!(
            "  {:<16} exhibition OBSTRUCTED, required width {required} over {} distinct windows",
            format!("{:?}", census.surface(*surface)),
            row.distinct_windows
        );
        println!(
            "  {:<16} verdict RETURNED anyway: {}",
            "",
            match inv.verdict {
                ConductVerdict::Iron => "IRON".to_owned(),
                ConductVerdict::ConductInvariant { collapsing, .. } =>
                    format!("CONDUCT-INVARIANT at {collapsing}"),
                ConductVerdict::Varying { terminus_varies, .. } =>
                    format!("varying (terminus_varies={terminus_varies})"),
            }
        );
    }
    println!();
    println!(
        "  {obstructed_and_read} surfaces cannot have their separation population materialized at \n  \
         the declared capacity of {DECLARED_CAPACITY} class pairs. Every one of them still carries a\n  \
         conduct verdict, because the verdict reads the sorted window classes in O(d * horizon) and\n  \
         never touches a pair. The aperture is neither removed nor widened."
    );
    holds.push((
        "control 7 -- every surface whose exhibition the declared capacity refuses still carries a \
         conduct verdict, by a route that materializes no pair"
            .to_owned(),
        obstructed_and_read > 0
            && reading
                .keys()
                .all(|surface| invariance.contains_key(surface))
            && whole_returns > 0
            && whole_matched,
        format!(
            "{obstructed_and_read} obstructed at capacity {DECLARED_CAPACITY}; {} verdicts returned \
             over {} surfaces; {whole_returns} populations returned WHOLE at exactly the predicted \
             width",
            invariance.len(),
            reading.len()
        ),
    ));

    // ------------------------------------------------- the independent implementation grades it
    println!();
    println!("THE INDEPENDENT IMPLEMENTATION, AT EVERY DECLARED SUB-FAMILY");
    println!("------------------------------------------------------------");
    println!();
    let mut checked = 0usize;
    let mut disagreed: Vec<String> = Vec::new();
    let mut organ_collapsed = 0usize;
    let mut organ_obstructed = 0usize;
    for surface in reading.keys() {
        for family in ReceiverFamily::FULL.subsets() {
            match cross_check_family(&census, &atlas, *surface, horizon, family, FAMILY_CHECK_CAPACITY) {
                Ok(check) => {
                    checked += 1;
                    if check.organ_blocks == 1 {
                        organ_collapsed += 1;
                    }
                    if !check.agrees() && disagreed.len() < 8 {
                        disagreed.push(format!(
                            "{:?} at {family}: projected {} vs organ {} (claimed collapse {})",
                            census.surface(*surface),
                            check.projected_blocks,
                            check.organ_blocks,
                            check.collapses_claimed
                        ));
                    }
                }
                Err(_) => organ_obstructed += 1,
            }
        }
    }
    println!(
        "  `receiver_exact_compression::compress` run at all 8 declared sub-families on every\n  \
         surface inside the declared capacity of {FAMILY_CHECK_CAPACITY} class pairs: {checked}\n  \
         checks, {} disagreements, {organ_collapsed} of them a genuine collapse to one block.\n  \
         {organ_obstructed} refused at that capacity and are counted rather than skipped silently.",
        disagreed.len()
    );
    for line in &disagreed {
        println!("    DISAGREEMENT {line}");
    }
    holds.push((
        "control 5 -- the projection and `receiver_exact_compression` agree at every declared \
         sub-family, including the empty one, and the organ actually collapses something"
            .to_owned(),
        disagreed.is_empty() && organ_collapsed > 0 && checked > 0,
        format!("{checked} checks, {organ_collapsed} collapses, {organ_obstructed} obstructed"),
    ));

    // --------------------------------------------------------------- across the two horizons
    println!();
    println!("ACROSS THE TWO DECLARED HORIZONS");
    println!("--------------------------------");
    println!();
    println!(
        "  {:<10} {:>10} {:>20} {:>12}",
        "horizon", "iron", "conduct-invariant", "union"
    );
    for h in HORIZONS {
        let (iron_h, invariant_h) = &earlier[&h];
        println!(
            "  {:<10} {:>10} {:>20} {:>12}",
            h,
            iron_h.len(),
            invariant_h.len(),
            iron_h.union(invariant_h).count()
        );
    }
    // A longer word can only separate more, so `constant_axes` can only shrink and the terminus can
    // only start varying. Iron and conduct-invariant are therefore individually NOT monotone -- iron
    // can fall into conduct-invariant -- but their UNION is.
    let near: BTreeSet<SurfaceId> = {
        let (iron_h, invariant_h) = &earlier[&HORIZONS[0]];
        iron_h.union(invariant_h).copied().collect()
    };
    let far: BTreeSet<SurfaceId> = {
        let (iron_h, invariant_h) = &earlier[&HORIZONS[1]];
        iron_h.union(invariant_h).copied().collect()
    };
    let moved: usize = {
        let (iron_near, _) = &earlier[&HORIZONS[0]];
        let (_, invariant_far) = &earlier[&HORIZONS[1]];
        iron_near.intersection(invariant_far).count()
    };
    println!();
    println!(
        "  A longer word only separates more, so `constant_axes` can only shrink and the terminus\n  \
         can only start varying. Neither block is monotone alone -- {moved} surfaces iron at horizon\n  \
         {} became conduct-invariant at horizon {} -- but their UNION must be. Checked:",
        HORIZONS[0], HORIZONS[1]
    );
    holds.push((
        "the union of iron and conduct-invariant is monotone decreasing in the horizon, and the \
         two blocks individually are not"
            .to_owned(),
        far.is_subset(&near),
        format!(
            "|union@{}| = {}, |union@{}| = {}, subset = {}; {moved} surfaces crossed from iron to \
             conduct-invariant",
            HORIZONS[0],
            near.len(),
            HORIZONS[1],
            far.len(),
            far.is_subset(&near)
        ),
    ));

    // ------------------------------------------------------------- a named contrast with iron
    println!();
    println!("THE CONTRAST WITH IRON, ON THE SAME MATERIAL");
    println!("--------------------------------------------");
    println!();
    let mut iron_ordered: Vec<(&SurfaceId, BigUint)> = witnessed
        .iter()
        .map(|surface| (surface, reading[surface].survived_pairs()))
        .collect();
    iron_ordered.sort_by(|left, right| right.1.cmp(&left.1).then(left.0.cmp(right.0)));
    println!("  The witnessed IRON verdicts that withstood the most refutations (presentation only):");
    for (surface, survived) in iron_ordered.iter().take(6) {
        println!(
            "    {:<18} {} occurrences, 1 window, {survived} non-separations withstood",
            format!("{:?}", census.surface(**surface)),
            census.occurrences(**surface)
        );
    }
    println!();
    println!(
        "  Iron asks the corpus never to have distinguished a surface. Conduct-invariance asks the\n  \
         corpus to have distinguished it on axes a coarser receiver does not read. They are the\n  \
         same instrument at two families, and they are disjoint by construction."
    );

    // Whether a block is "formulaic" is a claim about the material, so it is measured rather than
    // asserted. The orthographic kind of the surfaces in each block is the coarsest thing that can
    // carry it, and it is one of the declared axes, so nothing new is introduced to say it.
    println!();
    println!("  The orthographic composition of each block, so `formulaic` is a measurement:");
    println!();
    let kinds = [
        Kind::Lower,
        Kind::Capitalised,
        Kind::AllCaps,
        Kind::Mixed,
        Kind::Numeral,
    ];
    println!(
        "  {:<22} {:>7} {:>9} {:>9} {:>7} {:>9}",
        "block", "lower", "Capital", "ALLCAPS", "Mixed", "numeral"
    );
    let compose = |name: &str, block: &BTreeSet<SurfaceId>| {
        let counts: Vec<usize> = kinds
            .iter()
            .map(|kind| block.iter().filter(|s| census.kind(**s) == *kind).count())
            .collect();
        println!(
            "  {:<22} {:>7} {:>9} {:>9} {:>7} {:>9}",
            name, counts[0], counts[1], counts[2], counts[3], counts[4]
        );
    };
    compose("witnessed IRON", &partition.witnessed_iron);
    compose("CONDUCT-INVARIANT", &partition.conduct_invariant);
    compose("varying", &partition.varying);
    println!();
    println!(
        "  The `varying` block is the corpus's ordinary running prose, so its composition is the\n  \
         baseline the other two are read against."
    );

    // ------------------------------------------------------------------------ the holds
    println!();
    println!("HOLDS");
    println!("-----");
    println!();
    let mut failed = 0usize;
    for (name, held, evidence) in &holds {
        if !held {
            failed += 1;
        }
        println!("  [{}] {name}", if *held { "HOLD" } else { "FAIL" });
        println!("        {evidence}");
    }
    println!();
    if failed == 0 {
        println!("  {} declared holds, all held.", holds.len());
    } else {
        println!("  {} declared holds, {failed} FAILED.", holds.len());
        std::process::exit(1);
    }
}
