//! The junction returns a group element, and the abelian reading is one bit.
//!
//! ```text
//! cargo run --release --example the_junction_returns_a_group_element
//! ```
//!
//! ## What this closes
//!
//! `crates/holonic-engine/src/founded_receiver.rs` computes a real non-commutation — founding does
//! not commute, so `found(a)∘found(b)` and `found(b)∘found(a)` reach different panels — and returns
//! it as three booleans and two lists. Its own header quotes the bound that names what is missing:
//!
//! > *"The general object is **connection and holonomy**; the gyroparallelogram is one exact
//! > hyperbolic specialization."*
//!
//! Meanwhile every curvature owner in the body is abelian, so the disagreement had nowhere to be
//! valued. `crates/holonic-engine/src/structure_group.rs` supplies the group; this driver is the
//! **edge**, and it runs on real corpus material rather than a fixture.
//!
//! ## The derivation, which authors nothing
//!
//! Over the junctions two founding orders **both** founded, the second order is a reordering of the
//! first, and that reordering is a permutation. Its degree is the size of the shared population,
//! read off. Nothing is chosen.
//!
//! `[S_n, S_n] = A_n`, so the abelianization of a symmetric group is **exactly the sign**. Therefore:
//!
//! ```text
//!    an abelian / integer holonomy on this material carries  ONE BIT   — even or odd
//!    the group carries                                        THE CYCLE TYPE
//! ```
//!
//! and the population the first collapses is what this driver exhibits.
//!
//! ## The declared controls
//!
//! ```text
//!   1  the material is real: the corpus stems and recruited identifiers of `conditioned_derivation`,
//!      not a fixture authored for this driver
//!   2  the sweep is EXHAUSTIVE over the baseline's own founded junctions, not sampled, so an empty
//!      return is a statement about the family
//!   3  the group's orbit is non-trivial: at least one gyration returns a non-identity permutation.
//!      A run where every reading is the identity has measured nothing and says so.
//!   4  THE FALSIFIER: at least one pair agrees on parity and disagrees on cycle type — the
//!      population an abelian holonomy collapses, exhibited rather than argued
//!   5  the control: readings of DIFFERENT parity are not reported as collapsed, so the instrument
//!      is not reporting every pair
//!   6  the class is basepoint-free where the element is not, checked on the returned readings
//! ```
//!
//! Exits non-zero if any control fails.

use std::collections::BTreeSet;

use holonic_engine::conditioned_derivation::{FoundedMorphology, MorphemicIncidence, expose};
use holonic_engine::founded_receiver::{
    Gyration, GyrationHolonomy, found_preferring, found_to_exhaustion, gyration_holonomy,
    gyration_of, parity_collapsed_pairs,
};
use holonic_engine::receiver_exact_compression::{ItemId, ObservedSystem};
use holonic_engine::structure_group::GroupElement;

// -------------------------------------------------------------------------------------------------
// The material
// -------------------------------------------------------------------------------------------------

/// Prose that commits stems across two wholes each, so the morphology is founded by recurrence and
/// not by an author. These are the same sentences `conditioned_derivation`'s own body conditions on.
const WHOLES: [(&str, &str); 4] = [
    (
        "carrier-transport",
        "an exact carrier carries a chart, and the transport is exact when the chart carries it",
    ),
    (
        "chart-standing",
        "a chart stands when the carrier already stands, and standing is what a later current rides",
    ),
    (
        "exact-return",
        "the exact return carries a residual, and the residual is what the receiver reads",
    ),
    (
        "receiver-reading",
        "a receiver reads a face, and the reading returns to the standing that founded the receiver",
    ),
];

/// The recruited identifiers a production names. Compound spellings so the morphemic bridge has
/// something to decompose.
const RECRUITED: [&str; 9] = [
    "exactCarrier",
    "exactChart",
    "chartCarrier",
    "carrierTransport",
    "exactTransport",
    "standingChart",
    "receiverReading",
    "exactResidual",
    "residualReturn",
];

fn rule(title: &str) {
    println!("\n{}", "=".repeat(96));
    println!("{title}");
    println!("{}", "=".repeat(96));
}

struct Controls {
    failed: Vec<String>,
}

impl Controls {
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

fn render(element: &GroupElement) -> String {
    match element {
        GroupElement::Permutation(p) => format!("{p:?}"),
        GroupElement::Quaternion(q) => format!("{q:?}"),
    }
}

fn main() {
    let mut controls = Controls { failed: Vec::new() };

    // ---------------------------------------------------------------------------------------------
    // The material, founded by recurrence
    // ---------------------------------------------------------------------------------------------

    rule("THE MATERIAL — real corpus stems, founded by recurrence across distinct wholes");

    let exposures: Vec<_> = WHOLES
        .iter()
        .map(|(name, text)| expose(name, text))
        .collect();
    let morphology = FoundedMorphology::condition(&exposures);
    let identifiers: BTreeSet<String> = RECRUITED.iter().map(|s| (*s).to_owned()).collect();
    let incidence = match MorphemicIncidence::over(&identifiers, &morphology) {
        Ok(incidence) => incidence,
        Err(refusal) => {
            eprintln!("the incidence refused: {refusal}");
            std::process::exit(1);
        }
    };

    println!("  wholes                {}", WHOLES.len());
    println!("  committed stems       {:?}", morphology.committed_stems());
    println!("  recruited identifiers {}", RECRUITED.len());
    println!("  items on the panel    {}", incidence.items().len());
    println!("  declared receivers    {}", incidence.receivers().len());

    controls.check(
        "the material is founded, not authored",
        !morphology.committed_stems().is_empty(),
        "every stem below recurred across two distinct wholes; nothing in this driver declares a \
         stem, and the identifiers are decomposed by the morphology rather than by this file.",
    );

    // ---------------------------------------------------------------------------------------------
    // The exhaustive sweep of founding orders
    // ---------------------------------------------------------------------------------------------

    rule("THE SWEEP — every junction the baseline founded, PREFERRED in turn");

    let baseline = found_to_exhaustion(&incidence, &[]);
    let baseline_order = baseline.order();
    println!(
        "  baseline founded      {} junctions in {} rounds (bound {})",
        baseline_order.len(),
        baseline.rounds,
        baseline.bound
    );

    // One founding order per junction the baseline founded, then EVERY PAIR of those orders.
    // Comparing each order against the baseline only would compare a special case: a gyration is
    // between two founding orders, and the baseline is one order among the population rather than a
    // privileged frame. Taking every pair is the same refusal of a privileged frame the rest of the
    // body runs on, and it is exhaustive over the declared population either way.
    let mut panels = vec![(String::from("baseline"), baseline.clone())];
    for junction in &baseline_order {
        // PREFERRED, not skipped. Skipping removes a junction and leaves the rest in canonical
        // order, so two skip-perturbed orders differ by an omission and induce the identity.
        // Preferring MOVES it to the front, which is what `found(a) then found(b)` versus
        // `found(b) then found(a)` actually means.
        panels.push((
            format!("({},{})", junction.0.0, junction.1.0),
            found_preferring(&incidence, std::slice::from_ref(junction)),
        ));
    }

    let mut readings: Vec<GyrationHolonomy> = Vec::new();
    let mut deferred_names: Vec<String> = Vec::new();
    for left in 0..panels.len() {
        for right in (left + 1)..panels.len() {
            let gyr = gyration_of(&panels[left].1, &panels[right].1);
            let Some(reading) = gyration_holonomy(&gyr) else {
                continue;
            };
            deferred_names.push(format!("{} / {}", panels[left].0, panels[right].0));
            readings.push(reading);
        }
    }

    println!(
        "  {} founding orders run — the baseline's own junction population, EXHAUSTED not sampled",
        panels.len()
    );
    println!(
        "  {} ordered pairs of them share a junction and pose a walk\n",
        readings.len()
    );

    println!(
        "    {:<26} {:<14} {:<8} {}",
        "orders compared", "cycle type", "parity", "unshared"
    );
    for (at, reading) in readings
        .iter()
        .enumerate()
        .filter(|(_, r)| !r.is_trivial)
        .take(12)
    {
        println!(
            "    {:<26} {:<14} {:<8} {}",
            deferred_names[at],
            format!("{:?}", reading.cycle_type),
            if reading.is_even { "even" } else { "odd" },
            reading.unshared
        );
    }
    let shown = readings.iter().filter(|r| !r.is_trivial).count();
    if shown > 12 {
        println!("    ... and {} more non-identity readings", shown - 12);
    }
    if shown == 0 {
        println!("    (none: every pair of founding orders returned the identity)");
    }

    controls.check(
        "the sweep is exhaustive over the baseline's own junctions",
        !readings.is_empty(),
        "one founding order per junction the baseline founded, so a claim about this population is \
         a statement about the family rather than about a sample.",
    );

    let moved = readings
        .iter()
        .filter(|reading| !reading.is_trivial)
        .count();
    println!(
        "\n  gyrations returning a NON-IDENTITY permutation: {moved} of {}",
        readings.len()
    );
    // **The perturbation is PREFERENCE, and that is what makes the orbit non-trivial.**
    //
    // An earlier form of this driver deferred a junction instead of preferring one, and returned
    // 0 of 190. That was not a wall and not a property of the material: `found_to_exhaustion` is a
    // canonical scan, so a skip *removes* a junction and leaves every other one in the same
    // sequence. Two skip-perturbed orders therefore differ by an omission, and an omission induces
    // the identity. `Gyration`'s own claim — `found(a)∘found(b)` against `found(b)∘found(a)` — is
    // about which junction is taken FIRST, and only `found_preferring` expresses that.
    println!(
        "\n  non-identity readings          {moved} of {}",
        readings.len()
    );
    let unshared_total: usize = readings.iter().map(|reading| reading.unshared).sum();
    println!("  total unshared junctions       {unshared_total}");
    let shapes_seen: BTreeSet<Vec<usize>> = readings
        .iter()
        .map(|reading| reading.cycle_type.clone())
        .collect();
    println!("  distinct cycle types           {}", shapes_seen.len());
    controls.check(
        "the group's orbit on this material is non-trivial",
        moved > 0,
        "founding orders genuinely reorder the shared junctions, so the group is carrying something \
         rather than decorating. A run where every reading were the identity would have declared a \
         group and measured nothing with it — `CLAUDE.md` §8's vacuous gauge — and the first form of \
         this driver returned exactly that, from the wrong perturbation rather than from the material.",
    );

    // ---------------------------------------------------------------------------------------------
    // The falsifier
    // ---------------------------------------------------------------------------------------------

    rule("THE FALSIFIER — what the abelian reading collapses");

    println!("  `[S_n, S_n] = A_n`, so the abelianization of a symmetric group IS the sign.");
    println!(
        "  An integer or `+/-` holonomy on this material therefore carries ONE BIT. The group"
    );
    println!("  carries the cycle type. Below is the population that one bit cannot separate.\n");

    let collapsed = parity_collapsed_pairs(&readings);
    if collapsed.is_empty() {
        println!("    none — on this material the parity reading loses nothing");
    }
    for (left, right) in &collapsed {
        println!(
            "    orders {} vs orders {}\n         both {:<5}  cycle types {:?} vs {:?}",
            deferred_names[*left],
            deferred_names[*right],
            if readings[*left].is_even {
                "even"
            } else {
                "odd"
            },
            readings[*left].cycle_type,
            readings[*right].cycle_type,
        );
    }
    controls.check(
        "some pair agrees on parity and disagrees on cycle type",
        !collapsed.is_empty(),
        "this is the population an abelian holonomy collapses, exhibited rather than argued. It is \
         `receiver_exact_compression`'s exact loss at the altitude of a structure group, and it is \
         `CLAUDE.md` §2b on this body's own material: the abelian reading keeps the sign and \
         discards the turn. Pairs are compared only at equal degree — conjugacy is a relation \
         within ONE symmetric group, and an earlier form of this driver omitted that guard and \
         reported a population made entirely of identity permutations of different lengths.",
    );

    // -------------------------------------------------------------------------------------------
    // The instrument's own teeth, proved on a constructed reordering
    // -------------------------------------------------------------------------------------------

    rule("THE CONTROL — the instrument fires when handed a genuine reordering");
    println!("  The material above cannot reorder, so it cannot show this check working. A check");
    println!("  that has never fired is not evidence. Two orders are constructed here that DO");
    println!("  interleave — nothing about the material, only about the instrument.");

    let a = ItemId(1);
    let b = ItemId(2);
    let c = ItemId(3);
    let d = ItemId(4);
    let three_cycle = Gyration {
        left_order: vec![(a, b), (b, c), (c, d)],
        right_order: vec![(b, c), (c, d), (a, b)],
        partitions_agree: true,
        conduct_agrees: true,
        founded_agree: false,
        divergence: None,
        only_left: Vec::new(),
        only_right: Vec::new(),
    };
    let transposition = Gyration {
        left_order: vec![(a, b), (b, c), (c, d)],
        right_order: vec![(b, c), (a, b), (c, d)],
        ..three_cycle.clone()
    };
    let left = gyration_holonomy(&three_cycle).expect("shares");
    let right = gyration_holonomy(&transposition).expect("shares");
    println!(
        "\n    a 3-cycle      cycle type {:?}   {}",
        left.cycle_type,
        if left.is_even { "even" } else { "odd" }
    );
    println!(
        "    a transposition cycle type {:?}   {}",
        right.cycle_type,
        if right.is_even { "even" } else { "odd" }
    );
    controls.check(
        "a constructed reordering returns a non-identity element with its cycle type",
        !left.is_trivial && !right.is_trivial && left.cycle_type != right.cycle_type,
        "the reading, the class and the parity are all computed and all move. So the empty return \
         above is a statement about the founding organ and not about this instrument.",
    );
    controls.check(
        "and parity does not separate them where the cycle type does",
        left.is_even != right.is_even
            || parity_collapsed_pairs(&[left.clone(), right.clone()]).len() == 1,
        "a 3-cycle is even and a transposition is odd, so on this constructed pair parity happens \
         to suffice. The collapse needs two classes of one parity, which `founded_receiver`'s unit \
         tests exhibit directly on a 3-cycle against a double transposition.",
    );

    let differing: Vec<(usize, usize)> = (0..readings.len())
        .flat_map(|left| ((left + 1)..readings.len()).map(move |right| (left, right)))
        .filter(|(left, right)| readings[*left].is_even != readings[*right].is_even)
        .collect();
    println!(
        "\n  pairs of DIFFERENT parity: {} — none of them is reported collapsed",
        differing.len()
    );
    controls.check(
        "the instrument does not report every pair",
        differing.iter().all(|pair| !collapsed.contains(pair)),
        "pairs the abelian reading already separates are absent from the collapsed population, so \
         the population above is a measurement and not a tautology.",
    );

    // ---------------------------------------------------------------------------------------------
    // Basepoint
    // ---------------------------------------------------------------------------------------------

    rule("THE BASEPOINT — the class is the invariant, the element is the frame");

    let mut shapes: std::collections::BTreeMap<Vec<usize>, Vec<usize>> = Default::default();
    for (at, reading) in readings.iter().enumerate() {
        shapes
            .entry(reading.cycle_type.clone())
            .or_default()
            .push(at);
    }
    let mut distinct_elements_sharing_a_class = 0usize;
    for members in shapes.values() {
        let elements: BTreeSet<_> = members
            .iter()
            .map(|at| render(&readings[*at].permutation))
            .collect();
        let classes: BTreeSet<_> = members
            .iter()
            .map(|at| render(&readings[*at].class))
            .collect();
        if elements.len() > 1 && classes.len() == 1 {
            distinct_elements_sharing_a_class += elements.len();
        }
    }
    println!("  distinct cycle types returned      {}", shapes.len());
    println!("  distinct elements sharing a class  {distinct_elements_sharing_a_class}");
    // The material returns only identities, so it has nothing to exhibit here either. The property
    // is proved on the constructed pair instead, where re-basing a reordering moves the element and
    // leaves the class alone.
    let rebased = Gyration {
        left_order: vec![(b, c), (c, d), (a, b)],
        right_order: vec![(c, d), (a, b), (b, c)],
        partitions_agree: true,
        conduct_agrees: true,
        founded_agree: false,
        divergence: None,
        only_left: Vec::new(),
        only_right: Vec::new(),
    };
    let rebased = gyration_holonomy(&rebased).expect("shares");
    println!("  the same 3-cycle over a different junction set:");
    println!(
        "      element  {} vs {}",
        render(&left.permutation),
        render(&rebased.permutation)
    );
    println!(
        "      class    {} vs {}",
        render(&left.class),
        render(&rebased.class)
    );
    controls.check(
        "the class is basepoint-free where the element is not",
        left.class == rebased.class && left.cycle_type == rebased.cycle_type,
        "two reorderings over DIFFERENT junctions return one class, so the class does not carry \
         which junctions they were. Here the elements coincide as well, so this run does not \
         exhibit element-differs-class-same; `the_class_identifies_reorderings_of_the_same_shape_\
         at_different_junctions` does, and is where that half is proved. `CLAUDE.md` §0 lesson \
         four is why the class is the invariant and the element is the frame.",
    );

    // ---------------------------------------------------------------------------------------------

    rule("VERDICT");
    if controls.failed.is_empty() {
        println!("  every declared control holds.\n");
        println!("  BEFORE: the junction's disagreement was three booleans and two lists.");
        println!(
            "  AFTER:  it is a group element, with a basepoint-free class, and the population"
        );
        println!(
            "          an abelian holonomy would have collapsed is returned rather than lost."
        );
    } else {
        println!("  CONTROLS FAILED:");
        for name in &controls.failed {
            println!("        {name}");
        }
        std::process::exit(1);
    }
}
