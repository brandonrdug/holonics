//! THE CIRCUIT CLOSES AND THE FACE SUPERPOSES — the contact organs driven, artifacts returned.
//!
//! ```text
//! cargo run --release -p holonic-engine --example the_circuit_closes_and_the_face_superposes
//! ```
//!
//! ## What this closes
//!
//! `contact_gluing.rs` carries the word-line complex and the contact circuit. Measured 2026-08-10,
//! before this file existed:
//!
//! ```text
//!   grep -rnE "\b(contact_complex|face_over|ContactComplex)" --include="*.rs" \
//!        crates/*/examples soma/*/examples | grep -v the_circuit_closes_and_the_face_superposes
//!       -> nothing
//!   grep -rnE "\b(ride_circuit|Circuit)" --include="*.rs" crates/*/examples soma/*/examples \
//!        | grep -v the_circuit_closes_and_the_face_superposes \
//!        | grep -vE "ConditionedCircuit|CircuitAperture|DerivationCircuit|GrownCircuit"
//!       -> one line, the_tower_climbs.rs:11, a comment saying they are undriven
//! ```
//!
//! `contact_complex` and `face_over` do *conduct* — `glue_at_contact` and `integrate_leader` call
//! them, and `the_atmosphere_and_the_ground` drives both — but nothing had ever **returned their
//! artifacts**: the line a word becomes, the subcomplex a stem occupies, the superposition standing
//! over one letter. `CLAUDE.md` §9: *return the artifact; counts are supporting receipts and never
//! substitutes.* `ride_circuit` and `Circuit` had no caller at all outside `#[cfg(test)]`.
//!
//! ## The receiver question
//!
//! **Does a contact circuit close, and what does its circulation return that neither arc returns?**
//!
//! A circuit that rides and returns its holonomy is the spine's own circulation cut. The arcs each
//! carry a weight; the loop carries the *difference the reflection did not cancel*, which is not a
//! property of either arc. And the reflection is not a name on a comparison — crossing an arc
//! against its orientation negates the increment, which is the half-turn, `−1 = e^{iπ}`.
//!
//! ## The material, and it is real on both sides
//!
//! ```text
//!   ATMOSPHERE   canon/*.md            real prose. What recurs across two documents is committed.
//!   POPULATION   standing/output/**/*.lean, every distinct word the ground exhibits.
//! ```
//!
//! Neither side is authored and neither carries a number. The population rule is *every word the
//! ground exhibits* — not a count, not a length filter, not a top-`k`. What the atmosphere commits
//! is decided by `COMMITTING_RECURRENCE` inside `conditioned_derivation`, not here.
//!
//! ## What is a control and what is bookkeeping
//!
//! Several checks below **cannot be moved by the material** — they test the organ, not the reading,
//! and a check whose material cannot vary the property under test wears a passing result without
//! earning one (`CLAUDE.md` §8). Those are printed as `[organ]` rather than `[holds]` and are not
//! evidence about the corpus, though they still gate: an organ that breaks is a defect either way.
//! The `[holds]` checks each name the material that would break them.

use std::collections::{BTreeMap, BTreeSet};
use std::path::Path as FsPath;

use holonic_engine::conditioned_derivation::{Exposure, FoundedMorphology, expose};
use holonic_engine::contact_gluing::{
    Circuit, ContactGluingRefusal, ContactGraph, LeaderCochain, contact_complex, contact_graph,
    ride_circuit,
};
use holonic_engine::rebase_invariants::{PivotRule, rebase_invariants};
use holonic_engine::running_integral::{
    Cochain, Orientation, Path, PathStep, RunningIntegralError, holonomy,
};
use num_bigint::BigInt;

/// The declared atmosphere: real prose, read whole. Roots and extensions only.
const ATMOSPHERE: (&str, &str) = ("canon", "md");

/// The declared ground the population is read off.
const GROUND: (&str, &str) = ("standing/output", "lean");

fn rule(title: &str) {
    println!("\n{}", "=".repeat(96));
    println!("{title}");
    println!("{}", "=".repeat(96));
}

fn gather(root: &FsPath, extension: &str) -> Vec<(String, String)> {
    let mut found = Vec::new();
    let mut frontier = vec![root.to_path_buf()];
    while let Some(at) = frontier.pop() {
        let Ok(entries) = std::fs::read_dir(&at) else {
            continue;
        };
        for entry in entries.flatten() {
            let path = entry.path();
            if path.is_dir() {
                frontier.push(path);
            } else if path.extension().and_then(|e| e.to_str()) == Some(extension)
                && let Ok(text) = std::fs::read_to_string(&path)
            {
                found.push((path.display().to_string(), text));
            }
        }
    }
    found.sort();
    found
}

fn main() {
    let mut failures: Vec<String> = Vec::new();
    let mut organ_failures: Vec<String> = Vec::new();
    let mut hold = |claim: &str, held: bool, evidence: String| {
        if held {
            println!("  [holds] {claim}\n            {evidence}");
        } else {
            println!("  [FAILS] {claim}\n            {evidence}");
            failures.push(claim.to_owned());
        }
    };
    // A check on the ORGAN, which the material cannot move. Printed apart so it is never read as
    // evidence about the corpus — and it still gates, because an organ that breaks is a defect
    // whether or not a corpus could have caught it.
    let mut organ = |claim: &str, held: bool, evidence: String| {
        if held {
            println!("  [organ] {claim}\n            {evidence}");
        } else {
            println!("  [ORGAN FAILS] {claim}\n            {evidence}");
            organ_failures.push(claim.to_owned());
        }
    };

    // ---------------------------------------------------------------------------------------------

    rule("THE MATERIAL — real on both sides, and neither side carries a number");

    let atmosphere = gather(FsPath::new(ATMOSPHERE.0), ATMOSPHERE.1);
    let ground = gather(FsPath::new(GROUND.0), GROUND.1);
    if atmosphere.is_empty() || ground.is_empty() {
        println!(
            "  the declared material is not here: {} atmosphere files, {} ground files.\n  \
             run from the repository root.",
            atmosphere.len(),
            ground.len()
        );
        std::process::exit(1);
    }

    let exposures: Vec<Exposure> = atmosphere
        .iter()
        .map(|(name, text)| expose(name, text))
        .collect();
    let morphology = FoundedMorphology::condition(&exposures);

    // The population: every distinct word the ground exhibits, in canonical order. A rule, not a
    // level — nothing here selects by length, frequency, or rank.
    let mut population_set: BTreeSet<String> = BTreeSet::new();
    for (name, text) in &ground {
        for word in expose(name, text).words {
            population_set.insert(word);
        }
    }
    let population: Vec<String> = population_set.into_iter().collect();

    println!("  atmosphere documents   {}", atmosphere.len());
    println!("  stems founded          {}", morphology.founded().len());
    println!(
        "  stems committed        {}",
        morphology.committed_stems().len()
    );
    println!("  ground files           {}", ground.len());
    println!("  population (words)     {}", population.len());

    // ---------------------------------------------------------------------------------------------

    rule("THE WORD IS A LINE — `contact_complex`, and its artifact returned rather than counted");

    println!("  A word's cover is not a bag of spans. It is the line the word already is: every");
    println!("  offset a 0-cell, every unit step a 1-cell, and a stem occurrence the SET of steps");
    println!("  it covers. Two occurrences then meet exactly in the letters they share.\n");

    let mut complexes: BTreeMap<String, usize> = BTreeMap::new();
    let mut line_betti: BTreeMap<Vec<usize>, usize> = BTreeMap::new();
    let mut covered_population: Vec<String> = Vec::new();
    let mut shown = 0usize;
    for word in &population {
        let Ok(cover) = morphology.cover(word) else {
            continue;
        };
        if cover.occurrences.is_empty() {
            continue;
        }
        let Ok(contact) = contact_complex(&cover) else {
            continue;
        };
        covered_population.push(word.clone());
        complexes.insert(word.clone(), contact.occurrences.len());

        let invariants = rebase_invariants(&contact.complex, PivotRule::SmallestMagnitude)
            .expect("the line complex has invariants");
        let betti: Vec<usize> = invariants.grades.iter().map(|grade| grade.betti).collect();
        *line_betti.entry(betti).or_default() += 1;

        if shown < 3 {
            println!("  {word}");
            println!(
                "    0-cells {:<4} 1-cells {:<4} occurrences {}",
                contact.offsets.len(),
                contact.steps.len(),
                contact.occurrences.len()
            );
            for (stem, at, through, cell) in contact.occurrences.iter().take(8) {
                println!("      {stem:<14} @{at}..{through}   first step {cell:?}");
            }
            if contact.occurrences.len() > 8 {
                println!("      … {} more", contact.occurrences.len() - 8);
            }
            shown += 1;
        }
    }
    println!(
        "\n  {} of {} population words carry a founded occurrence.",
        covered_population.len(),
        population.len()
    );
    println!("  Betti of the line complex, over the whole covered population: {line_betti:?}");

    organ(
        "every word's line complex is contractible — beta = [1, 0]",
        line_betti.keys().all(|betti| betti == &vec![1usize, 0]),
        format!(
            "{line_betti:?} over {} words. THIS IS BOOKKEEPING: an interval subdivided has no \
             cycle for any word whatever,\n            so no corpus can move it. It checks the \
             CONSTRUCTOR (the convicted earlier form founded one long edge per\n            \
             occurrence and would fail here), not the material. The cycles are between words, and \
             that is the next section.",
            covered_population.len()
        ),
    );

    // ---------------------------------------------------------------------------------------------

    rule("THE FACE — `face_over`, the superposition standing over one letter");

    println!("  The face over a step is every stem standing there at once. It is what a leader");
    println!("  rides at that letter, and where two stems superpose the face carries BOTH rather");
    println!("  than resolving to one. That is the causal string's raw material.\n");

    let mut widest: Option<(String, usize, Vec<String>)> = None;
    let mut superposing_steps = 0usize;
    let mut total_steps = 0usize;
    let mut face_widths: BTreeMap<usize, usize> = BTreeMap::new();
    for word in &covered_population {
        let Ok(cover) = morphology.cover(word) else {
            continue;
        };
        let Ok(contact) = contact_complex(&cover) else {
            continue;
        };
        for at in contact.steps.keys() {
            let face = contact.face_over(*at);
            total_steps += 1;
            *face_widths.entry(face.len()).or_default() += 1;
            if face.len() > 1 {
                superposing_steps += 1;
            }
            let carried = face.len();
            if widest.as_ref().is_none_or(|(_, seen, _)| carried > *seen) {
                widest = Some((
                    word.clone(),
                    carried,
                    face.iter().map(|stem| (*stem).to_owned()).collect(),
                ));
            }
        }
    }
    println!("  face width -> steps carrying it: {face_widths:?}");
    if let Some((word, width, stems)) = &widest {
        println!("  widest face: `{word}` carries {width} stems at one letter: {stems:?}");
    }

    // The whole face string of one word, returned as the artifact.
    if let Some(word) = covered_population.iter().find(|word| {
        morphology
            .cover(word)
            .ok()
            .and_then(|cover| contact_complex(&cover).ok())
            .is_some_and(|contact| {
                contact
                    .steps
                    .keys()
                    .any(|at| contact.face_over(*at).len() > 1)
            })
    }) {
        let cover = morphology.cover(word).expect("covered");
        let contact = contact_complex(&cover).expect("reads");
        println!("\n  the full face string of `{word}`, letter by letter:");
        for at in contact.steps.keys() {
            let letter = word.as_bytes()[*at].to_ascii_lowercase() as char;
            println!(
                "    @{at} `{letter}`  {}",
                contact.face_over(*at).join(" + ")
            );
        }
        // Past the extent there is no letter and no face, and the organ says so by returning
        // nothing rather than by refusing.
        let past = contact.face_over(word.len() + 1);
        println!("    @{} (past the extent) -> {:?}", word.len() + 1, past);
        organ(
            "`face_over` past the word's extent returns an empty face rather than a refusal",
            past.is_empty(),
            format!("face_over({}) = {past:?}", word.len() + 1),
        );
    }

    hold(
        "the material superposes — some letter carries a face of more than one stem",
        superposing_steps > 0,
        format!(
            "{superposing_steps} of {total_steps} unit steps carry two or more stems. \
             MATERIAL THAT WOULD FAIL THIS: a ground\n            whose words carry no nested or \
             overlapping committed stem — single letters, or an atmosphere committing only \
             maximal-length\n            stems. `FoundedCover` retains every span, so this is a \
             reading of the corpus and not of the constructor.",
        ),
    );

    // ---------------------------------------------------------------------------------------------

    rule("THE SECTION — the subcomplex a stem occupies, and the refusal when it occupies none");

    let mut sectioned = 0usize;
    let mut refusals_by_name = 0usize;
    let mut section_shown = 0usize;
    for word in covered_population.iter().take(64) {
        let Ok(cover) = morphology.cover(word) else {
            continue;
        };
        let Ok(contact) = contact_complex(&cover) else {
            continue;
        };
        let carried: Vec<String> = cover.stems().iter().map(|s| (*s).to_owned()).collect();
        let Some(present) = carried.first() else {
            continue;
        };
        let Ok(section) = contact.section(present) else {
            continue;
        };
        sectioned += 1;

        // The absent stem is chosen CANONICALLY — the first committed stem this word does not
        // carry — rather than picked by hand.
        let absent = morphology
            .committed_stems()
            .into_iter()
            .find(|stem| !carried.iter().any(|held| held == stem));
        let Some(absent) = absent else { continue };
        match contact.section(absent) {
            Err(ContactGluingRefusal::StemStandsNowhere { stem }) if stem == absent => {
                refusals_by_name += 1;
                if section_shown < 3 {
                    println!(
                        "  {word:<26} `{present}` occupies {} cells; `{absent}` refused: {}",
                        section.len(),
                        ContactGluingRefusal::StemStandsNowhere { stem: stem.clone() }
                    );
                    section_shown += 1;
                }
            }
            other => println!("  {word:<26} `{absent}` returned {other:?} — expected a refusal"),
        }
    }
    organ(
        "a stem standing nowhere is REFUSED BY NAME rather than returning an empty subcomplex",
        refusals_by_name == sectioned && sectioned > 0,
        format!(
            "{refusals_by_name} named refusals over {sectioned} words. THIS IS A CHECK ON THE \
             ORGAN: an empty section is\n            structurally impossible to distinguish from \
             a present-but-empty one, which is why the refusal exists. The\n            material \
             only chooses WHICH stem is absent.",
        ),
    );

    // ---------------------------------------------------------------------------------------------

    rule("THE CONTACT GRAPH — where the cycles actually are");

    let graph = match contact_graph(&morphology, &population) {
        Ok(graph) => graph,
        Err(refusal) => {
            println!("  the contact graph refused: {refusal}");
            std::process::exit(1);
        }
    };
    println!("  vertices (identifiers) {}", graph.identifiers.len());
    println!("  arcs (shared stems)    {}", graph.arcs.len());

    let invariants = rebase_invariants(&graph.complex, PivotRule::SmallestMagnitude)
        .expect("the contact graph has invariants");
    let graph_betti: Vec<usize> = invariants.grades.iter().map(|grade| grade.betti).collect();
    println!("  betti                  {graph_betti:?}");

    // Pairs sharing two or more stems: the smallest genuine cycles, read off the arcs.
    let mut by_pair: BTreeMap<(String, String), Vec<String>> = BTreeMap::new();
    for (left, right, stem, _) in &graph.arcs {
        by_pair
            .entry((left.clone(), right.clone()))
            .or_default()
            .push(stem.clone());
    }
    let bigons: Vec<((String, String), Vec<String>)> = by_pair
        .iter()
        .filter(|(_, stems)| stems.len() >= 2)
        .map(|(pair, stems)| (pair.clone(), stems.clone()))
        .collect();
    println!(
        "  pairs sharing >= 2 stems (circuits available) {}",
        bigons.len()
    );

    hold(
        "the material closes circuits at all — a circulation over an acyclic graph is vacuous",
        !bigons.is_empty() && graph_betti.get(1).copied().unwrap_or(0) > 0,
        format!(
            "beta1 = {:?} with {} rideable pairs. MATERIAL THAT WOULD FAIL THIS: a ground whose \
             words pairwise share at\n            most one committed stem — a tree of contacts. \
             The atmosphere decides this and it is not assumed.",
            graph_betti.get(1),
            bigons.len()
        ),
    );

    // ---------------------------------------------------------------------------------------------

    rule("THE CIRCUIT — `ride_circuit`, and the artifact it returns");

    println!("  Out along one arc, back along the other AGAINST its orientation. Going against");
    println!("  negates the increment — the half-turn — so what the sum returns is what the");
    println!("  reflection did NOT cancel: the holonomy of the loop.\n");

    let mut rides: Vec<((String, String), String, String, Circuit)> = Vec::new();
    let mut ride_refusals = 0usize;
    for ((left, right), stems) in &bigons {
        for window in stems.windows(2) {
            let (out, back) = (&window[0], &window[1]);
            match ride_circuit(
                &graph,
                &morphology,
                left,
                right,
                out,
                back,
                LeaderCochain::SpanLength,
            ) {
                Ok(circuit) => rides.push((
                    (left.clone(), right.clone()),
                    out.clone(),
                    back.clone(),
                    circuit,
                )),
                Err(refusal) => {
                    ride_refusals += 1;
                    println!("    {left} ~ {right} refused: {refusal}");
                }
            }
        }
    }
    println!(
        "  circuits ridden {}   refused {}",
        rides.len(),
        ride_refusals
    );
    for (_, out, back, circuit) in rides.iter().take(8) {
        println!(
            "    through {:?}\n      string {:?}  reflected {:?}  series {:?}  holonomy {}   (`{out}` out, `{back}` back)",
            circuit.through, circuit.string, circuit.reflected, circuit.series, circuit.holonomy
        );
    }

    // The holonomy recomputed independently from the declared cochain. Not the organ's arithmetic
    // replayed: the weights are re-derived from the stems and the difference taken here.
    let mut arithmetic_agrees = 0usize;
    for (_, out, back, circuit) in &rides {
        let expected = BigInt::from(out.len()) - BigInt::from(back.len());
        if circuit.holonomy == expected {
            arithmetic_agrees += 1;
        }
    }
    organ(
        "the loop returns w(out) - w(back) exactly — the reflected arm SUBTRACTS",
        arithmetic_agrees == rides.len() && !rides.is_empty(),
        format!(
            "{arithmetic_agrees} of {} circuits agree with a difference recomputed here from the \
             stem strings, while the\n            organ arrives at it through cell boundaries, \
             orientation application and BigInt accumulation. Two paths,\n            one number. \
             It checks the ORIENTATION handling and nothing about the corpus: no material can \
             move it, and\n            it fails the moment `Against` stops negating.",
            rides.len()
        ),
    );

    let closes = rides
        .iter()
        .all(|(_, _, _, c)| c.through.first() == c.through.last() && c.through.len() == 3);
    organ(
        "every ridden circuit closes on the vertex it left",
        closes,
        format!(
            "{} circuits, each `through` of length 3 with equal ends. `holonomy` refuses \
             otherwise — see the\n            refusal section below for the guard firing.",
            rides.len()
        ),
    );

    // ---------------------------------------------------------------------------------------------

    rule("THE ORBIT — three frames on one walk, and what must not move across them");

    // FRAME 1 — the argument order. `find` accepts an arc in either order, so `(X, Y)` and `(Y, X)`
    // describe the SAME two arcs and therefore the same traversal. The return must not know which
    // way the caller wrote it.
    let mut order_invariant = 0usize;
    let mut order_moved: Vec<String> = Vec::new();
    for ((left, right), out, back, forward) in &rides {
        let Ok(swapped) = ride_circuit(
            &graph,
            &morphology,
            right,
            left,
            out,
            back,
            LeaderCochain::SpanLength,
        ) else {
            continue;
        };
        if swapped == *forward {
            order_invariant += 1;
        } else {
            order_moved.push(format!(
                "{left}~{right}: forward through {:?} / swapped through {:?}",
                forward.through, swapped.through
            ));
        }
    }
    for moved in order_moved.iter().take(4) {
        println!("    MOVED  {moved}");
    }
    hold(
        "swapping the caller's pair order returns the IDENTICAL circuit — the walk is the same walk",
        order_invariant == rides.len() && !rides.is_empty(),
        format!(
            "{order_invariant} of {} invariant. MEASURED BEFORE THE REPAIR by reverting the return \
             block and re-running this\n            driver: **0 of 708 invariant**, every circuit \
             reporting `[right, left, right]` for a walk that departs and\n            returns at \
             the same vertex either way — `through`, `string` and `reflected` were the caller's own \
             arguments\n            restated as though they were a measurement. The fields are now \
             read off `RunningIntegral`'s per-step\n            departed/arrived/orientation. \
             MATERIAL THAT WOULD FAIL THIS: none — it is the repair's own orbit, and 0 -> 708 is \
             the\n            orbit exhibited rather than asserted.",
            rides.len()
        ),
    );

    // FRAME 2 — the direction. Riding out along `back` and home along `out` is the reversed loop,
    // and a circulation must negate exactly.
    let mut antisymmetric = 0usize;
    for ((left, right), out, back, forward) in &rides {
        let Ok(reversed) = ride_circuit(
            &graph,
            &morphology,
            left,
            right,
            back,
            out,
            LeaderCochain::SpanLength,
        ) else {
            continue;
        };
        if reversed.holonomy == -forward.holonomy.clone() {
            antisymmetric += 1;
        }
    }
    organ(
        "reversing the circuit negates the holonomy exactly",
        antisymmetric == rides.len() && !rides.is_empty(),
        format!(
            "{antisymmetric} of {} negate. No material can move this; it checks that no magnitude \
             is taken anywhere on\n            the path. Worth gating even so, because a sign \
             discarded here is the float defect one level down\n            (`CLAUDE.md` §2b: a \
             sign is a passage, never a state).",
            rides.len()
        ),
    );

    // FRAME 3 — the cochain. Two declared measurements of the same walk. This one the material CAN
    // move, and the collapsed population is exhibited rather than counted away.
    let mut separated: Vec<String> = Vec::new();
    let mut collapsed: Vec<String> = Vec::new();
    for ((left, right), out, back, by_span) in &rides {
        let Ok(by_breadth) = ride_circuit(
            &graph,
            &morphology,
            left,
            right,
            out,
            back,
            LeaderCochain::WitnessBreadth,
        ) else {
            continue;
        };
        let line = format!(
            "{left}~{right} `{out}`/`{back}`  span {}  breadth {}",
            by_span.holonomy, by_breadth.holonomy
        );
        // The walk itself is one walk under either measurement.
        if by_span.through != by_breadth.through || by_span.string != by_breadth.string {
            println!("    the two cochains disagree about the WALK, which they must not: {line}");
        }
        if by_span.holonomy == by_breadth.holonomy {
            collapsed.push(line);
        } else {
            separated.push(line);
        }
    }
    println!(
        "  separated by the gauge {}   collapsed {}",
        separated.len(),
        collapsed.len()
    );
    for line in separated.iter().take(4) {
        println!("    separated  {line}");
    }
    for line in collapsed.iter().take(4) {
        println!("    collapsed  {line}");
    }
    hold(
        "the two declared cochains are a real gauge — their orbit on this material is non-trivial",
        !separated.is_empty(),
        format!(
            "{} circuits separated, {} collapsed. MATERIAL THAT WOULD FAIL THIS: a corpus where \
             every shared stem's\n            letter count equals its witness count, in which case \
             the two cochains would be one reading wearing two\n            names and no agreement \
             between them would be evidence (`CLAUDE.md` §8, the vacuous gauge). The collapsed\n   \
                      population is the remainder and is printed, not discarded.",
            separated.len(),
            collapsed.len()
        ),
    );

    // ---------------------------------------------------------------------------------------------

    rule("THE REFUSAL — `holonomy` refuses a walk that does not close, exhibited on this graph");

    println!(
        "  `ride_circuit` CANNOT produce this refusal. Both arcs are constrained by `find` to"
    );
    println!(
        "  lie between the same pair, `contact_graph` stores every arc of a pair with the same"
    );
    println!("  tail and head, and the second is crossed Against — so every input it accepts");
    println!("  describes a walk that closes, `out_stem == back_stem` included (holonomy zero).");
    println!("  That is an unreachable refusal, reported and not counted (`CLAUDE.md` §8). The");
    println!("  guard is real and fires on walks built directly on the same `ContactGraph`.\n");

    let unit_cochain = |graph: &ContactGraph| {
        let mut weights = Cochain::new(1);
        for (_, _, stem, cell) in &graph.arcs {
            weights.set(*cell, BigInt::from(stem.len()));
        }
        weights
    };
    let weights = unit_cochain(&graph);

    // An open walk: a -> b then b -> c with a != c. It JOINS and it does not close.
    let mut open_walk_exhibited = false;
    let mut disjoint_walk_exhibited = false;
    'search: for (a, b, _, first) in &graph.arcs {
        for (c, d, _, second) in &graph.arcs {
            // The second arc must depart where the first arrived: tail(second) == head(first) == b.
            if c != b || d == a {
                continue;
            }
            let path = Path::new([
                PathStep {
                    cell: *first,
                    orientation: Orientation::Along,
                },
                PathStep {
                    cell: *second,
                    orientation: Orientation::Along,
                },
            ]);
            match holonomy(&graph.complex, &weights, &path) {
                Err(RunningIntegralError::PathIsNotClosed { start, end }) => {
                    println!(
                        "  OPEN WALK    {a} -> {b} -> {d}\n    refused: PathIsNotClosed {{ start: \
                         {start:?}, end: {end:?} }}   i.e. departed `{a}`, standing at `{d}`"
                    );
                    open_walk_exhibited = true;
                    break 'search;
                }
                Ok(_) => println!("  {a} -> {b} -> {d} closed unexpectedly"),
                Err(other) => println!("  {a} -> {b} -> {d} refused with {other:?}"),
            }
        }
    }

    // A walk that does not even join: two arcs with no shared endpoint.
    'disjoint: for (a, b, _, first) in &graph.arcs {
        for (c, d, _, second) in &graph.arcs {
            if c == a || c == b || d == a || d == b {
                continue;
            }
            let path = Path::new([
                PathStep {
                    cell: *first,
                    orientation: Orientation::Along,
                },
                PathStep {
                    cell: *second,
                    orientation: Orientation::Along,
                },
            ]);
            match holonomy(&graph.complex, &weights, &path) {
                Err(RunningIntegralError::PathDoesNotJoin {
                    index,
                    standing_at,
                    departs,
                }) => {
                    println!(
                        "  DISJOINT     {a}->{b} then {c}->{d}\n    refused: PathDoesNotJoin \
                         {{ index: {index}, standing_at: {standing_at:?}, departs: {departs:?} }}"
                    );
                    disjoint_walk_exhibited = true;
                    break 'disjoint;
                }
                other => println!("  {a}->{b} then {c}->{d} returned {other:?}"),
            }
        }
    }

    // And a closure on the same graph, so the guard is shown admitting as well as refusing.
    let closed_exhibited = rides.first().map(|(_, _, _, circuit)| {
        println!(
            "  CLOSED       {:?}\n    admitted: series {:?}   holonomy {}",
            circuit.through, circuit.series, circuit.holonomy
        );
        true
    });

    hold(
        "the closure guard fires on an open walk over the SAME graph a circuit rode",
        open_walk_exhibited,
        "PathIsNotClosed carries the departed and standing vertices, so the refusal names where \
         the walk ended up\n            rather than reporting a boolean. MATERIAL THAT WOULD FAIL \
         THIS: a contact graph with no path of length two\n            between three distinct \
         identifiers — a graph that is a disjoint union of single edges."
            .to_owned(),
    );
    hold(
        "the join guard fires on two arcs sharing no endpoint",
        disjoint_walk_exhibited,
        "PathDoesNotJoin names the step index, where the walk was standing, and where the next \
         step departs.\n            MATERIAL THAT WOULD FAIL THIS: a contact graph on fewer than \
         four identifiers, where every two arcs meet."
            .to_owned(),
    );
    hold(
        "and the same guard ADMITS a closed circuit on that graph — it is not refusing everything",
        closed_exhibited == Some(true),
        "a guard that refused every walk would be indistinguishable from a broken organ."
            .to_owned(),
    );

    // ---------------------------------------------------------------------------------------------

    rule("WHAT MOVED, WHAT DID NOT, AND WHAT IS STILL OPEN");

    println!("  MOVED");
    println!("    - `Circuit::through`, `::string` and `::reflected` are read off the traversal.");
    println!(
        "      Before: the caller's arguments restated. Measured by reverting the return block"
    );
    println!("      and re-running this driver: the swapped-order control went 0/708 -> 708/708.");
    println!("      That is the repair's orbit, exhibited, and not a claim about the corpus.");
    println!("    - `LeaderCochain`'s doc named one reading where the code has two: face");
    println!("      cardinality on the word line, stem length on the contact graph. Corrected in");
    println!("      place; no behaviour changed, and the two readings disagree numerically here.");
    println!();
    println!("  DID NOT MOVE — reported as bookkeeping");
    println!("    - The line complex's Betti reading. An interval subdivided is contractible for");
    println!("      every word, so no corpus can move it; it checks the constructor only.");
    println!("    - Direction antisymmetry and the closure of every ridden circuit. Both are");
    println!("      properties of the organ that this material cannot vary.");
    println!();
    println!("  STILL OPEN");
    println!(
        "    - `ride_circuit` rides only a BIGON: two arcs between one pair. The contact graph"
    );
    println!("      carries triangles (`contact_triangles` reads them) and longer cycles, and no");
    println!("      organ rides them, so the holonomy of anything but a two-arc loop is unowned.");
    println!("      A general circuit over a declared vertex sequence would be a NEW organ and is");
    println!("      not built here.");
    println!("    - Consequently `RunningIntegralError::PathIsNotClosed` is unreachable through");
    println!("      `ride_circuit`. It is exhibited above by building the walk directly, which is");
    println!("      the honest form: the guard is driven, its caller cannot trip it.");
    println!("    - The holonomy of a bigon is `w(out) - w(back)` and nothing more. That it is");
    println!("      exactly the arc-weight difference means this cut CONDUCTS but carries no");
    println!("      information a pair of arc weights does not already carry. A circulation that");
    println!("      returns something neither arc carries needs a cycle longer than two.");

    rule("BOUNDS");
    println!("  - One frame of material. Every figure is a reading of `canon/*.md` against the");
    println!("    words `standing/output/**/*.lean` exhibits, and moves when either does.");
    println!("  - No timing is taken and none would be falsifiable if it were.");
    println!("  - Nothing here is submitted to a kernel and no formal claim is made.");

    if failures.is_empty() && organ_failures.is_empty() {
        println!("\n  all declared controls hold, and every organ check holds.");
    } else {
        println!(
            "\n  {} material control(s) and {} organ check(s) FAILED:",
            failures.len(),
            organ_failures.len()
        );
        for failure in failures.iter().chain(&organ_failures) {
            println!("    - {failure}");
        }
        std::process::exit(1);
    }
}
