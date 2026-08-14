//! A receiver axis whose reading of a neighbour is what the corpus **does** with it.
//!
//! ## The gap this closes, as the record already named it
//!
//! `token_invariance` declared three receivers — `Kind`, `Weight`, `Density` — and all three are
//! **orthographic**: character class, length band, `2^n` corpus count. `2a36a5e` states the
//! consequence directly: `tensor` fails to collapse *"because it stands next to markup in one
//! sentence and a word in the next, which is typography, not meaning."* At horizon 2 on this corpus
//! `tensor`, `vector`, `lemma`, `group`, `field`, `holon`, `receiver` and `exact` were **all**
//! `Varying`, and the 1,269 surfaces that did collapse were URL components and timestamps.
//!
//! `canon/MEANING_DEFINED.md:81` carries the same object as its one unbuilt row: competing
//! decompositions live as pathways, *"nothing yet keeps two incompatible decompositions live."*
//!
//! ## What the fourth axis reads
//!
//! `ReceiverAxis::Conduct` reads, of the surface standing at a position, its
//! [`ConductSignature`](holonic_engine::token_invariance::ConductSignature) — the orthographic axes
//! that surface's **own whole occurrence population** holds constant everywhere else in the corpus,
//! and whether that population ever runs out of whole. That is the block of the down-set lattice the
//! surface lands in under `receiver_exact_compression`'s Nerode partition, which is what the material
//! does rather than how it is written. Two surfaces with nothing orthographic in common can share the
//! reading; two spelled alike can differ.
//!
//! ## Why this axis is DECLARED and not founded by `found_to_exhaustion`
//!
//! Driven below, not asserted. `founded_receiver`'s two species — `ContinuationAperture` and
//! `ConductReach` — both read the **system's own successor relation**, and a population of surfaces
//! has none. Run on one, the organ reaches `FoundingPressure::Congestion` and then refuses
//! `FoundingRefusal::FoundedNothing`. So the conduct axis is a **third species**, and its pressure is
//! that congestion: the orthographic panel routes the whole vocabulary through one distinction, and
//! the engineering answer is another pathway rather than a finer version of the same one.
//! `surface_residue` then measures it under that module's own residue and capacity law.
//!
//! ## The declared controls
//!
//! 1. **The orbit is non-trivial, in BOTH arms.** Adding a receiver may only refine (H.0016), so the
//!    interesting arm is the other one: does the conduct axis **alone** hold together a population
//!    the three orthographic axes split? Both arms are measured, at the surface level and at the
//!    occurrence level, with pairs exhibited. If neither moves, this driver says so and stops
//!    claiming — `CLAUDE.md` §8's vacuous-gauge rule.
//! 2. **The null bind, three ways.** A reading that founds a collapse must lose it when the material
//!    is taken away.
//!    - `unfounded` — a constant conduct axis. The **ceiling**: an axis that reads nothing collapses
//!      everything, so the founded number must sit far below this or the axis is behaving as a
//!      constant.
//!    - `permuted` — the founded tokens permuted across surfaces by a declared permutation. The
//!      multiset of readings is **exactly** preserved, so the axis is equally coarse and carries no
//!      relation to the material. The sharpest of the three.
//!    - `shuffled` — the atlas founded on a **deterministically shuffled corpus** and then read on
//!      the real one. `Π` is preserved bit for bit by the shuffle — every count, hence every
//!      orthographic reading, is identical — so the only thing that moved is what stands next to
//!      what. If a collapse survives this, the axis is reading position and not conduct.
//! 3. **The artifact.** The eight surfaces the orthographic axes could not collapse, each with its
//!    verdict, the family that collapses it, and the shortest separating word where one exists.
//! 4. **Exhaustive, not sampled.** The declared family is four axes, so the sub-family lattice is
//!    sixteen; every one is run against every measured surface, and the independent implementation
//!    grades every check the declared capacity admits, with the refusals counted rather than skipped.

use std::collections::{BTreeMap, BTreeSet};
use std::path::PathBuf;

use num_bigint::BigUint;

use holonic_engine::corpus_census::{CorpusCensus, DECLARED_STRATA, LexicalSpecies, SurfaceId};
use holonic_engine::founded_receiver::{FoundingRefusal, found_to_exhaustion};
use holonic_engine::receiver_exact_compression::{
    InputId, ItemId, Observation, ObservedSystem, ReceiverId,
};
use holonic_engine::token_invariance::{
    ConductAtlas, ConductSignature, ConductVerdict, ReceiverAxis, ReceiverFamily,
    SeparationReading, cross_check_family, invariance_partition, reading, separation_reading,
    surface_residue, sweep,
};

/// **The horizon the conduct axis is founded at.** A caller's declaration; `ConductAtlas` holds no
/// default, and the founding horizon is deliberately not the reading horizon — they are two
/// separate declarations about two separate readings.
const FOUNDING_HORIZON: usize = 1;

/// **The horizon the reading runs at.** Kept at 2 so every figure here is directly comparable with
/// `the_token_holds_an_axis_while_its_windows_vary`, which reported the refutation this driver
/// answers.
const READING_HORIZON: usize = 2;

/// The second reading horizon, taken for the eight-surface artifact only. A shorter word separates
/// less, so a collapse that exists anywhere exists here.
const NEAR_HORIZON: usize = 1;

/// The capacity this caller declares for the sub-family cross-check, in separated class pairs per
/// surface. Past it `cross_check_family` refuses with the width the material required, and the
/// refusals are counted below rather than worked around.
const FAMILY_CHECK_CAPACITY: u64 = 64;

/// The seed of the declared shuffle. Any value produces a permutation; this one is fixed so the
/// null is reproducible bit for bit.
const SHUFFLE_SEED: u64 = 0x486F_6C6F_6E69_6373;

/// The eight surfaces the orthographic panel could not collapse. Declared before the run.
const EIGHT: [&str; 8] = [
    "tensor", "vector", "lemma", "group", "field", "holon", "receiver", "exact",
];

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

    println!("THE AXIS READS WHAT THE NEIGHBOUR DOES");
    println!("======================================");
    println!();
    println!(
        "  Three declared receivers read the neighbour's SPELLING -- case class, length band,\n  \
         corpus count. The fourth reads what the corpus DID with that neighbour everywhere else."
    );

    // ------------------------------------------------------------------ the declared corpus
    println!();
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
    let vocabulary = census.all_surfaces().count();
    println!();
    println!(
        "  total stream        {} tokens ({} word, {} markup)",
        census.total_occurrences(),
        census.word_occurrences(),
        census.total_occurrences() - census.word_occurrences()
    );
    println!("  measured population {measured} distinct word surfaces");
    println!(
        "  the atlas founds    {vocabulary} surfaces -- markup INCLUDED, because a receiver \
         standing beside a `#` must read something"
    );

    // ------------------------------------------- why a fourth axis, and why it is not founded
    println!();
    println!("THE PRESSURE, AND WHY `found_to_exhaustion` CANNOT FOUND THIS AXIS");
    println!("------------------------------------------------------------------");
    println!();
    let declared_population: Vec<SurfaceId> = EIGHT
        .into_iter()
        .chain([
            "current", "passage", "residual", "holonic", "passages", "surface",
        ])
        .filter_map(|name| census.lookup(name))
        .collect();
    let flat = ConductAtlas::unfounded(&census, FOUNDING_HORIZON);
    let surface_system = SurfacePanel {
        census: &census,
        atlas: &flat,
        items: declared_population.clone(),
    };
    let panel = found_to_exhaustion(&surface_system, &[]);
    let congestion = panel
        .refused
        .iter()
        .any(|refusal| matches!(refusal, FoundingRefusal::FoundedNothing { .. }));
    let occupancy = panel
        .one_shot_before
        .blocks
        .iter()
        .map(|block| block.len())
        .max()
        .unwrap_or(0);
    println!(
        "  Declared population: {} surfaces, exhaustive over the declaration -- the eight named\n  \
         surfaces plus six dialect surfaces. Panel: the three orthographic axes. Inputs: none, \n  \
         because a population of surfaces carries no successor relation.\n",
        declared_population.len()
    );
    println!(
        "    one-shot blocks {}   congested block occupancy {occupancy}   foundings {}   refusals {}",
        panel.one_shot_before.len(),
        panel.rounds,
        panel.refused.len()
    );
    for refusal in &panel.refused {
        println!("    REFUSED  {refusal:?}");
    }
    println!();
    println!(
        "  The organ reaches `FoundingPressure::Congestion` -- a block holding more than one item is\n  \
         an overloaded site -- and then refuses, because both of its species read the successor\n  \
         relation this system does not have. The conduct axis is a THIRD species. It is declared,\n  \
         and everything below measures it under `founded_receiver`'s own residue and capacity law."
    );
    holds.push((
        "the founding organ reaches congestion on the surface population and REFUSES by name, so \
         the fourth axis is a third species rather than a fourth finger"
            .to_owned(),
        congestion && panel.rounds == 0 && occupancy > 1,
        format!(
            "{} items, {} one-shot blocks, occupancy {occupancy}, {} foundings, refusals {:?}",
            declared_population.len(),
            panel.one_shot_before.len(),
            panel.rounds,
            panel.refused
        ),
    ));

    // ------------------------------------------------------------------ the axis, founded
    let atlas = ConductAtlas::found(&census, FOUNDING_HORIZON);
    println!();
    println!("THE AXIS, FOUNDED AT HORIZON {FOUNDING_HORIZON}");
    println!("-----------------------------");
    println!();
    println!(
        "  The COMPLETE token population. Nothing is cut: every reading the axis returns anywhere\n  \
         in the corpus appears here with the number of surfaces carrying it.\n"
    );
    println!(
        "  {:<8} {:<34} {:>10}   {}",
        "token", "what it says", "surfaces", "share"
    );
    let population = atlas.population();
    for (token, count) in &population {
        println!(
            "  {:<8} {:<34} {:>10}   {}",
            token,
            ConductSignature::decode(*token).to_string(),
            count,
            format!("{:.2}%", 100.0 * *count as f64 / vocabulary as f64)
        );
    }
    let distinct_tokens = population.len();
    println!();
    println!(
        "  {distinct_tokens} distinct readings over {vocabulary} surfaces. An atlas returning ONE \
         reading has founded\n  nothing; one returning a distinct reading per surface has founded an \
         identity map. Both\n  degenerate ends are reported rather than assumed away."
    );

    // ------------------------------------------------------------------ control 1: the orbit
    println!();
    println!("CONTROL 1 -- THE ORBIT, AT THE SURFACE LEVEL");
    println!("--------------------------------------------");
    println!();
    let residue = surface_residue(
        &census,
        &atlas,
        ReceiverAxis::Conduct,
        ReceiverFamily::ORTHOGRAPHIC,
    );
    let null_residue = surface_residue(
        &census,
        &flat,
        ReceiverAxis::Conduct,
        ReceiverFamily::ORTHOGRAPHIC,
    );
    println!(
        "  `founded_receiver`: Res(r) = ( INTERSECT_{{s != r}} =_s ) \\ =_r, the pairs every other\n  \
         receiver identifies and this one separates. An axis with empty residue is REDUNDANT.\n"
    );
    println!(
        "  arm 1 -- REFINEMENT   pairs the orthographic panel identifies:      {}",
        residue.identified_by_against
    );
    println!(
        "                        of those, pairs `conduct` separates (Res):    {}",
        residue.residue
    );
    println!(
        "  arm 2 -- COARSENING   pairs `conduct` alone identifies:             {}",
        residue.identified_by_axis
    );
    println!(
        "                        of those, pairs the orthographic panel splits:{}",
        residue.carried_alone
    );
    println!(
        "                        capacity, by that module's law |Res| + 1:     {}",
        residue.capacity()
    );
    if let Some((left, right)) = residue.residue_witness {
        println!();
        println!(
            "    residue witness   {:?} / {:?} -- same {:?} orthographically, conduct {} vs {}",
            census.surface(left),
            census.surface(right),
            census.signature(left),
            ConductSignature::decode(atlas.token(left)),
            ConductSignature::decode(atlas.token(right)),
        );
    }
    if let Some((left, right)) = residue.carried_witness {
        println!(
            "    carried witness   {:?} / {:?} -- orthographically {:?} vs {:?}, conduct BOTH {}",
            census.surface(left),
            census.surface(right),
            census.signature(left),
            census.signature(right),
            ConductSignature::decode(atlas.token(left)),
        );
    }
    println!();
    println!(
        "  The null, for comparison: the UNFOUNDED axis has residue {} and capacity {} -- redundant,\n  \
         and by the capacity law it is not deleted but becomes the most congested route.",
        null_residue.residue,
        null_residue.capacity()
    );
    let surface_orbit =
        residue.residue > BigUint::from(0u32) && residue.carried_alone > BigUint::from(0u32);
    holds.push((
        "control 1a -- the axis's orbit is non-trivial at the surface level in BOTH arms: it \
         separates pairs the orthographic panel identifies AND identifies pairs it separates"
            .to_owned(),
        surface_orbit && null_residue.is_redundant(),
        format!(
            "Res = {}, carried alone = {}; the unfounded null is redundant ({})",
            residue.residue, residue.carried_alone, null_residue.residue
        ),
    ));

    // --------------------------------------------------- the nulls, at the occurrence level
    println!();
    println!("CONTROL 2 -- THE NULL BIND");
    println!("--------------------------");
    println!();
    println!(
        "  The object being measured is the population of surfaces the fourth axis moves:\n\n    \
         MOVED(atlas) = surfaces whose maximal collapsing family CONTAINS `conduct` and whose\n                   \
         orthographic part is EMPTY -- a collapse no declared orthographic family could make.\n"
    );

    let permuted = atlas.permuted(&declared_permutation(vocabulary));
    let (shuffled_census, shuffled_atlas) = shuffled_null(&census);
    let transported = ConductAtlas::declaring(
        FOUNDING_HORIZON,
        (0..vocabulary)
            .map(|id| {
                shuffled_census
                    .lookup(census.surface(SurfaceId(id as u32)))
                    .map(|surface| shuffled_atlas.token(surface))
                    .unwrap_or(0)
            })
            .collect(),
    );

    // The shuffle preserved `Pi` exactly, so every orthographic reading is bit-identical and the
    // only thing that moved is what stands next to what. Asserted on the material, not claimed.
    let census_preserved = census.word_surfaces().into_iter().all(|surface| {
        shuffled_census
            .lookup(census.surface(surface))
            .map(|other| {
                shuffled_census.signature(other) == census.signature(surface)
                    && shuffled_census.occurrences(other) == census.occurrences(surface)
            })
            .unwrap_or(false)
    });

    println!(
        "  {:<12} {:<44} {:>10} {:>12}",
        "atlas", "what it reads", "readings", "MOVED"
    );
    let mut moved: BTreeMap<&str, BTreeSet<SurfaceId>> = BTreeMap::new();
    for (name, which, says) in [
        (
            "unfounded",
            &flat,
            "one reading for everything -- the ceiling",
        ),
        (
            "permuted",
            &permuted,
            "the same multiset, permuted across surfaces",
        ),
        (
            "shuffled",
            &transported,
            "founded on a shuffled corpus, read on the real one",
        ),
        ("FOUNDED", &atlas, "what the corpus did with the neighbour"),
    ] {
        let reading = sweep(&census, which, READING_HORIZON);
        let population = moved_population(&reading);
        println!(
            "  {:<12} {:<44} {:>10} {:>12}",
            name,
            says,
            which.population().len(),
            population.len()
        );
        moved.insert(name, population);
    }

    let founded_moved = moved["FOUNDED"].clone();
    let ceiling = moved["unfounded"].len();
    let permuted_moved = &moved["permuted"];
    let shuffled_moved = &moved["shuffled"];
    println!();
    println!(
        "  The founded population is {} of the {ceiling}-surface ceiling a CONSTANT axis reaches.\n  \
         Overlap with the permuted null: {}.  With the shuffled null: {}.",
        founded_moved.len(),
        founded_moved.intersection(permuted_moved).count(),
        founded_moved.intersection(shuffled_moved).count(),
    );
    println!();
    println!(
        "  A null that reproduced the founded population would show the collapse is a consequence\n  \
         of the axis's COARSENESS rather than of what it read. The permuted null is the sharp one:\n  \
         it has the identical multiset of readings and no relation whatever to the material."
    );
    let null_binds = founded_moved.len() < ceiling
        && !founded_moved.is_empty()
        && founded_moved.intersection(permuted_moved).count() < founded_moved.len()
        && founded_moved.intersection(shuffled_moved).count() < founded_moved.len();
    holds.push((
        "control 2 -- the null binds: the founded population sits below the constant-axis ceiling \
         and neither the permuted nor the shuffled null reproduces it"
            .to_owned(),
        null_binds,
        format!(
            "founded {} / ceiling {ceiling}; permuted {} ({} shared); shuffled {} ({} shared)",
            founded_moved.len(),
            permuted_moved.len(),
            founded_moved.intersection(permuted_moved).count(),
            shuffled_moved.len(),
            founded_moved.intersection(shuffled_moved).count(),
        ),
    ));
    holds.push((
        "the shuffle preserved the lived construction exactly -- every count and every orthographic \
         reading is bit-identical -- so the only coordinate that moved is what stands next to what"
            .to_owned(),
        census_preserved,
        format!(
            "{} word surfaces checked against the shuffled census",
            measured
        ),
    ));

    // ------------------------------------------------------ the retained reading, and the orbit
    let reading = sweep(&census, &atlas, READING_HORIZON);
    let partition = invariance_partition(&reading);

    println!();
    println!("CONTROL 1 -- THE ORBIT, AT THE OCCURRENCE LEVEL");
    println!("-----------------------------------------------");
    println!();
    let mut refined = 0usize;
    let mut coarsened = 0usize;
    let mut refined_witness: Option<SurfaceId> = None;
    let mut coarsened_witness: Option<SurfaceId> = None;
    for (surface, row) in &reading {
        let full = row.family_blocks(ReceiverFamily::FULL);
        let orthographic = row.family_blocks(ReceiverFamily::ORTHOGRAPHIC);
        let conduct_only = row.family_blocks(ReceiverFamily::of([ReceiverAxis::Conduct]));
        if full > orthographic {
            refined += 1;
            if refined_witness.is_none() {
                refined_witness = Some(*surface);
            }
        }
        if conduct_only == 1 && orthographic > 1 {
            coarsened += 1;
            if coarsened_witness.is_none() {
                coarsened_witness = Some(*surface);
            }
        }
    }
    println!(
        "  arm 1 -- REFINEMENT   surfaces the four-axis family separates and the orthographic\n  \
         {:<22}panel does not:                                  {refined}",
        ""
    );
    println!(
        "  arm 2 -- COARSENING   surfaces `{{conduct}}` alone holds in ONE block while the\n  \
         {:<22}orthographic panel splits them:                  {coarsened}",
        ""
    );
    for (label, witness) in [
        ("refinement", refined_witness),
        ("coarsening", coarsened_witness),
    ] {
        let Some(surface) = witness else {
            println!("    {label:<12} NO WITNESS -- this arm of the orbit is empty");
            continue;
        };
        let row = &reading[&surface];
        println!(
            "    {label:<12} {:<20} occ {:>6}  blocks: full {} / orthographic {} / conduct {}",
            format!("{:?}", census.surface(surface)),
            row.occurrences,
            row.family_blocks(ReceiverFamily::FULL),
            row.family_blocks(ReceiverFamily::ORTHOGRAPHIC),
            row.family_blocks(ReceiverFamily::of([ReceiverAxis::Conduct])),
        );
    }
    println!();
    println!(
        "  Arm 2 is the one an added receiver can NEVER produce. H.0016's transformations clause:\n  \
         enlarging the family may only refine. A coarser reading of the same material is only\n  \
         reachable by an axis that reads something else, which is the whole content of this build."
    );
    holds.push((
        "control 1b -- the orbit is non-trivial at the occurrence level in both arms, so the axis \
         is not a fourth orthographic axis wearing a new name"
            .to_owned(),
        refined > 0 && coarsened > 0,
        format!("{refined} surfaces refined, {coarsened} coarsened, over {measured} measured"),
    ));

    // ------------------------------------------------------------- the population, by family
    println!();
    println!("THE THREE-WAY PARTITION, AND WHERE THE COLLAPSES NOW SIT");
    println!("--------------------------------------------------------");
    println!();
    println!("  {:<26} {:>9}", "verdict at horizon 2", "surfaces");
    println!(
        "  {:<26} {:>9}",
        "IRON, witnessed",
        partition.witnessed_iron.len()
    );
    println!(
        "  {:<26} {:>9}",
        "IRON, vacuous",
        partition.vacuously_iron.len()
    );
    println!(
        "  {:<26} {:>9}",
        "CONDUCT-INVARIANT",
        partition.conduct_invariant.len()
    );
    println!("  {:<26} {:>9}", "varying", partition.varying.len());
    println!("  {:<26} {:>9}", "total", partition.total());
    println!();
    println!(
        "  The COMPLETE collapsing-family population. A family at zero is printed, not omitted.\n"
    );
    println!(
        "  {:<28} {:>9}   {}",
        "collapsing family", "surfaces", "axes the material MOVED"
    );
    let mut by_family: BTreeMap<ReceiverFamily, usize> = BTreeMap::new();
    for surface in &partition.conduct_invariant {
        if let ConductVerdict::ConductInvariant { collapsing, .. } =
            reading[surface].conduct_invariance().verdict
        {
            *by_family.entry(collapsing).or_default() += 1;
        }
    }
    let mut families_carrying = 0usize;
    for family in ReceiverFamily::FULL.subsets() {
        if family.is_empty() || family == ReceiverFamily::FULL {
            continue;
        }
        let members = by_family.get(&family).copied().unwrap_or(0);
        if members > 0 {
            families_carrying += 1;
        }
        println!(
            "  {:<28} {:>9}   {}",
            family.to_string(),
            members,
            family.complement()
        );
    }
    let conduct_only_family = ReceiverFamily::of([ReceiverAxis::Conduct]);
    println!();
    println!(
        "  {} of the {} proper nonempty declared families carry a population. `{}` -- the conduct\n  \
         axis ALONE, with every orthographic axis moving -- carries {}.",
        families_carrying,
        ReceiverFamily::FULL.subsets().len() - 2,
        conduct_only_family,
        by_family.get(&conduct_only_family).copied().unwrap_or(0),
    );

    // ------------------------------------------------------------------ control 3: the eight
    println!();
    println!("CONTROL 3 -- THE ARTIFACT: THE EIGHT SURFACES");
    println!("---------------------------------------------");
    println!();
    println!(
        "  `blocks` is how many conduct blocks each family leaves over the surface's whole\n  \
         occurrence population; `1` is the collapse. Declared in advance and reported either way.\n"
    );
    let near = sweep(&census, &atlas, NEAR_HORIZON);
    let mut collapsed_at_conduct = 0usize;
    let mut reported = 0usize;
    for horizon_reading in [(NEAR_HORIZON, &near), (READING_HORIZON, &reading)] {
        let (horizon, rows) = horizon_reading;
        println!("  horizon {horizon}");
        println!(
            "  {:<12} {:>6} {:>8} {:>7} {:>8} {:>9} {:>9} {:>5}  {}",
            "surface",
            "occ",
            "windows",
            "{kind}",
            "{weight}",
            "{density}",
            "{conduct}",
            "min",
            "verdict"
        );
        for name in EIGHT {
            let Some(surface) = census.lookup(name) else {
                println!("  {:<12} {:>6}", format!("{name:?}"), "absent");
                continue;
            };
            let Some(row) = rows.get(&surface) else {
                println!("  {:<12} {:>6}", format!("{name:?}"), "markup");
                continue;
            };
            let invariance = row.conduct_invariance();
            let verdict = match invariance.verdict {
                ConductVerdict::Iron => "IRON".to_owned(),
                ConductVerdict::ConductInvariant { collapsing, .. } => {
                    if horizon == READING_HORIZON && collapsing.contains(ReceiverAxis::Conduct) {
                        collapsed_at_conduct += 1;
                    }
                    format!("CONDUCT-INVARIANT at {collapsing}")
                }
                ConductVerdict::Varying {
                    terminus_varies, ..
                } => {
                    if terminus_varies {
                        "varying (by TERMINUS -- no family can)".to_owned()
                    } else {
                        "varying (every declared axis moved)".to_owned()
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
                "  {:<12} {:>6} {:>8} {:>7} {:>8} {:>9} {:>9} {:>5}  {}",
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
            if horizon == READING_HORIZON {
                reported += 1;
            }
        }
        println!();
    }
    println!(
        "  The separating word each of the eight still carries at horizon {READING_HORIZON}, at the\n  \
         FULL panel and then at the conduct axis ALONE. The two are different questions: the full\n  \
         panel names whichever axis comes first, which on a four-axis reading is almost never the\n  \
         one under test, so the second line is what `conduct` itself still sees.\n"
    );
    let conduct_alone = ReceiverFamily::of([ReceiverAxis::Conduct]);
    for name in EIGHT {
        let Some(surface) = census
            .lookup(name)
            .and_then(|id| reading.get(&id).map(|r| (id, r)))
        else {
            continue;
        };
        let (id, row) = surface;
        let invariance = row.conduct_invariance();
        println!(
            "    {:<12} collapsing family: {}",
            format!("{:?}", census.surface(id)),
            invariance
                .verdict
                .collapsing()
                .map(|family| family.to_string())
                .unwrap_or_else(|| "NONE -- no declared family holds it".to_owned()),
        );
        match row.shortest_separation(&census) {
            Some(separation) => println!("      full panel   {}", separation.exhibit(&census)),
            None => println!("      full panel   one window -- no separating word exists"),
        }
        match row.shallowest_within(conduct_alone) {
            Some(separation) => println!("      {conduct_alone:<12} {}", separation.exhibit()),
            None => println!("      {conduct_alone:<12} COLLAPSES -- one block, no word separates"),
        }
    }
    holds.push((
        "control 3 -- the eight declared surfaces were looked up by name and each returned a \
         verdict, a collapsing family where one exists, and its shortest separating word"
            .to_owned(),
        reported == EIGHT.len(),
        format!(
            "{reported} of {} present and reported; {collapsed_at_conduct} collapse at a family \
             containing `conduct`",
            EIGHT.len()
        ),
    ));

    // --------------------------------------- what the eight are still separated BY, and its ablation
    println!();
    println!("WHAT STILL SEPARATES THE EIGHT, AND THE ABLATION OF THAT COORDINATE");
    println!("-------------------------------------------------------------------");
    println!();
    let terminus_readers = atlas.surfaces_reading(|signature| signature.terminus_varies);
    println!(
        "  Every one of the eight is separated at `{conduct_alone}` by the SAME distinction:\n  \
         `holds {{}}` against `holds {{}} +terminus`. A `ConductSignature` carries two things, and\n  \
         the second -- whether the surface ever stood within the founding horizon of a WHOLE'S EDGE\n  \
         -- is a property of document length and placement rather than of how a surface is used.\n"
    );
    println!(
        "  The COMPLETE population carrying a terminus-varying reading: {} of {vocabulary} surfaces.\n",
        terminus_readers.len()
    );
    for surface in &terminus_readers {
        println!(
            "    {:<16} {:>8} occurrences   {}",
            format!("{:?}", census.surface(*surface)),
            census.occurrences(*surface),
            ConductSignature::decode(atlas.token(*surface)),
        );
    }
    println!();
    let ablated = atlas.without_terminus();
    println!(
        "  The ablation. `{conduct_alone}` block counts for the eight, with the terminus bit and\n  \
         without it. The ablated axis is strictly COARSER, so it collapses more by construction and\n  \
         the number has to be read against the constant-axis ceiling rather than on its own.\n"
    );
    println!(
        "  {:<12} {:>10} {:>12} {:>12}",
        "surface", "windows", "{conduct}", "ablated"
    );
    let mut ablation_collapses = 0usize;
    for name in EIGHT {
        let Some(surface) = census.lookup(name) else {
            continue;
        };
        let with = &reading[&surface];
        let without = separation_reading(&census, &ablated, surface, READING_HORIZON);
        let blocks = without.family_blocks(conduct_alone);
        if blocks == 1 {
            ablation_collapses += 1;
        }
        println!(
            "  {:<12} {:>10} {:>12} {:>12}",
            format!("{name:?}"),
            with.distinct_windows,
            with.family_blocks(conduct_alone),
            blocks
        );
    }
    let ablated_moved = moved_population(&sweep(&census, &ablated, READING_HORIZON));
    println!();
    println!(
        "  MOVED under the ablated axis: {} surfaces, against {} founded and the {ceiling}-surface\n  \
         ceiling a CONSTANT axis reaches. {ablation_collapses} of the eight collapse at \
         `{conduct_alone}` once the\n  terminus bit is gone.",
        ablated_moved.len(),
        founded_moved.len(),
    );
    println!();
    println!(
        "  This is reported as a measurement and NOT adopted. The declared encoding keeps the\n  \
         terminus bit, because a terminus is a distinction the material carries and no receiver's to\n  \
         delete -- `token_invariance`'s own terminus clause says so. What the ablation names is the\n  \
         next coupling: a conduct signature founded over a whole-relative frame, so that standing\n  \
         near a document edge is not a coordinate the axis inherits from the filesystem."
    );

    // ------------------------------------------------------------- control 4: exhaustion
    println!();
    println!("CONTROL 4 -- EXHAUSTIVE, NOT SAMPLED");
    println!("------------------------------------");
    println!();
    let mut checked = 0usize;
    let mut obstructed = 0usize;
    let mut collapses = 0usize;
    let mut disagreements: Vec<String> = Vec::new();
    let families: Vec<ReceiverFamily> = ReceiverFamily::FULL.subsets();
    for surface in reading.keys() {
        for family in &families {
            match cross_check_family(
                &census,
                &atlas,
                *surface,
                READING_HORIZON,
                *family,
                FAMILY_CHECK_CAPACITY,
            ) {
                Ok(check) => {
                    checked += 1;
                    if check.organ_blocks == 1 {
                        collapses += 1;
                    }
                    if !check.agrees() && disagreements.len() < 8 {
                        disagreements.push(format!(
                            "{:?} at {family}: projected {} vs organ {} (claimed {})",
                            census.surface(*surface),
                            check.projected_blocks,
                            check.organ_blocks,
                            check.collapses_claimed
                        ));
                    }
                }
                Err(_) => obstructed += 1,
            }
        }
    }
    println!(
        "  The declared family is {} axes, so the sub-family lattice is {} and it was EXHAUSTED:\n  \
         every family against every one of the {measured} measured surfaces. No surface is sampled\n  \
         and no family is omitted -- {} verdicts were returned over {} surfaces.",
        ReceiverAxis::DECLARED.len(),
        families.len(),
        reading.len(),
        measured
    );
    println!();
    println!(
        "  `receiver_exact_compression::compress` is the independent implementation and it graded\n  \
         {checked} of the {} checks; {obstructed} exceeded the declared capacity of \
         {FAMILY_CHECK_CAPACITY}\n  class pairs and REFUSED with the width the material required, \
         counted here rather than\n  skipped. {collapses} of the graded checks are a genuine \
         collapse to one block, and there are\n  {} disagreements.",
        reading.len() * families.len(),
        disagreements.len()
    );
    for line in &disagreements {
        println!("    DISAGREEMENT {line}");
    }
    holds.push((
        "control 4 -- the sub-family lattice and the measured population are both exhausted, and \
         the independent implementation agrees on every check the declared capacity admitted"
            .to_owned(),
        disagreements.is_empty()
            && checked > 0
            && collapses > 0
            && reading.len() == measured
            && families.len() == 1 << ReceiverAxis::DECLARED.len(),
        format!(
            "{} families x {measured} surfaces; {checked} graded, {obstructed} obstructed, \
             {collapses} collapses, 0 disagreements",
            families.len()
        ),
    ));

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

/// The surfaces whose maximal collapsing family contains `conduct` and holds **no** orthographic
/// axis: a collapse no declared orthographic family could have made.
fn moved_population(reading: &BTreeMap<SurfaceId, SeparationReading>) -> BTreeSet<SurfaceId> {
    reading
        .iter()
        .filter(|(_, row)| {
            let invariance = row.conduct_invariance();
            match invariance.verdict {
                ConductVerdict::ConductInvariant { collapsing, .. } => {
                    collapsing.contains(ReceiverAxis::Conduct)
                        && (collapsing.0 & ReceiverFamily::ORTHOGRAPHIC.0) == 0
                }
                _ => false,
            }
        })
        .map(|(surface, _)| *surface)
        .collect()
}

/// A declared permutation of the surface population: Fisher--Yates driven by `splitmix64`, whose
/// mixing constants are the published ones. A driver is where a literal belongs.
fn declared_permutation(population: usize) -> Vec<usize> {
    let mut permutation: Vec<usize> = (0..population).collect();
    let mut state = SHUFFLE_SEED;
    for at in (1..population).rev() {
        let swap = (mix(&mut state) % (at as u64 + 1)) as usize;
        permutation.swap(at, swap);
    }
    permutation
}

fn mix(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9E37_79B9_7F4A_7C15);
    let mut word = *state;
    word = (word ^ (word >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
    word = (word ^ (word >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
    word ^ (word >> 31)
}

/// The shuffled corpus and the atlas founded on it.
///
/// Every whole keeps its exact multiset of tokens and its stratum; only the order moves. So the
/// census's counts, kinds and weight bands are bit-identical and the only thing the atlas can be
/// reading differently is **what stands next to what**.
fn shuffled_null(census: &CorpusCensus) -> (CorpusCensus, ConductAtlas) {
    let mut shuffled = CorpusCensus::declaring(&DECLARED_STRATA, LexicalSpecies::Prose)
        .expect("this repository's own four strata");
    for (index, whole) in census.wholes().iter().enumerate() {
        let mut tokens: Vec<&str> = whole
            .stream
            .iter()
            .map(|surface| census.surface(*surface))
            .collect();
        let mut state = SHUFFLE_SEED ^ index as u64;
        for at in (1..tokens.len()).rev() {
            let swap = (mix(&mut state) % (at as u64 + 1)) as usize;
            tokens.swap(at, swap);
        }
        // Whitespace separates and produces nothing, so joining with a space reproduces exactly
        // this token sequence under the declared tokenizer and merges nothing.
        shuffled.admit_whole(
            whole.stratum,
            whole.relative_path.clone(),
            &tokens.join(" "),
        );
    }
    let atlas = ConductAtlas::found(&shuffled, FOUNDING_HORIZON);
    (shuffled, atlas)
}

/// The surface population presented as an observed system: items are surfaces, the panel is the
/// three orthographic axes, and there is **no successor relation**, because one surface does not
/// follow another.
///
/// This is what `found_to_exhaustion` is run against above, and the absent successor relation is the
/// content: both of that organ's axis species read it.
struct SurfacePanel<'a> {
    census: &'a CorpusCensus,
    atlas: &'a ConductAtlas,
    items: Vec<SurfaceId>,
}

impl ObservedSystem for SurfacePanel<'_> {
    fn items(&self) -> Vec<ItemId> {
        self.items
            .iter()
            .map(|surface| ItemId(u64::from(surface.0)))
            .collect()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        ReceiverAxis::ORTHOGRAPHIC
            .into_iter()
            .map(ReceiverAxis::id)
            .collect()
    }

    fn inputs(&self) -> Vec<InputId> {
        Vec::new()
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        let signature = reading(self.census, self.atlas, SurfaceId(item.0 as u32));
        Observation(match ReceiverAxis::from_id(receiver) {
            Some(axis) => axis.read(signature),
            None => u64::MAX,
        })
    }

    fn successor(&self, _item: ItemId, _input: InputId) -> Option<ItemId> {
        None
    }
}
