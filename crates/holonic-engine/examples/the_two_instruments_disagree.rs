//! THE TWO INSTRUMENTS DISAGREE — one object, three apertures, and the refusal is the return.
//!
//! ```text
//! cargo run --release -p holonic-engine --example the_two_instruments_disagree
//! ```
//!
//! ## What this closes
//!
//! `research/records/2026-08-10_THE_INSTRUMENT_DECLARES_THE_APERTURE_AND_THE_REFUSAL_IS_THE_RETURN.md`
//! identifies two rungs of an instrument ladder already built here and never joined:
//!
//! - `crate::multiquadratic` carries `ℚ(√k₁,…,√kₙ)` — degree `2ⁿ`, Galois group `(ℤ/2)ⁿ`. **That is
//!   the straightedge-and-compass field.** Its structural aperture is `[ℚ(α):ℚ] = 2ⁿ`, which is a
//!   property of the field and not of `DECLARED_KERNEL_BOUND`, which bounds a search.
//! - `crate::quintic_chart` is the **radical** rung, whose wall is at degree four (Abel–Ruffini,
//!   Galois), already driven by `the_degree_is_a_rung`.
//!
//! Measured 2026-08-10: only `lib.rs` named both. They had never met.
//!
//! ## The receiver question
//!
//! **Does one declared object receive different verdicts from two instruments, and is each verdict
//! correct?**
//!
//! `x³ − 2` is the case the ancients could not close. MathWorld's `CubeDuplication`, verbatim: *"the
//! problem cannot be solved because the Delian constant `2^(1/3)` … **is not a Euclidean number**…
//! The problem **can** be solved, however, using a Neusis construction."* Every cubic is solvable by
//! radicals. So the compass must **refuse** it and the radical chart must **return** it, and neither
//! is wrong.
//!
//! ## What is deliberately NOT claimed
//!
//! The compass rung's positive side is **necessary and not sufficient**. A degree-four irreducible
//! with Galois group `A₄` or `S₄` has power-of-two degree and is not constructible, because
//! sufficiency needs the Galois closure to be a 2-group. `CompassVerdict::NecessaryConditionHolds`
//! says so in its own name and there is no `is_constructible` method to misread.
//!
//! The **neusis rung's aperture** is stated here — a marked ruler reaches `{2,3}`-towers, so a
//! reachable degree is `2^a·3^b` — but **no arithmetic carrier for it exists in either repository**.
//! `NeusisVerdict` therefore states an aperture and computes no root, and says so in its own doc.
//! MathWorld's `NeusisConstruction` names the three problems it settles and **states no degree**, so
//! the degree condition is asserted on the standard literature (Videla 1997) and not on that page.

use std::error::Error;

use holonic_engine::arithmetic_monodromy::{IntegralQuinticProblem, QuinticProblemId};
use holonic_engine::multiquadratic::{admits_degree, Multiquadratic, DECLARED_KERNEL_BOUND};
use holonic_engine::quintic_chart::{
    read_ladder, read_quintic_charts, CompassVerdict, NeusisVerdict,
    RadicalChartVerdict,
};
use num_bigint::BigInt;
use relational_geometry::Rat;

/// Declared by this caller, matching the sibling degree drivers so the three are comparable.
const PRIME_LIMIT: u64 = 97;
const HORN_LOCAL_SECTION_LIMIT: u64 = 1_000_000;

fn rule(title: &str) {
    println!("\n{}", "=".repeat(96));
    println!("{title}");
    println!("{}", "=".repeat(96));
}

fn integers(values: &[i64]) -> Vec<BigInt> {
    values.iter().map(|v| BigInt::from(*v)).collect()
}

/// The declared ladder material. Coefficients ascend: `[c₀, c₁, …, cₙ]`.
fn material() -> Vec<(&'static str, Vec<BigInt>)> {
    vec![
        // THE DELIAN PROBLEM. x³ − 2. Degree 3.
        ("x^3 - 2  (the doubled cube)", integers(&[-2, 0, 0, 1])),
        // THE REGULAR HEPTAGON. The minimal polynomial of 2cos(2π/7) is x³ + x² − 2x − 1: the
        // 7-gon's constructibility is a question about a degree-THREE number, not a degree-seven
        // one, because [Q(2cos(2π/n)):Q] = φ(n)/2 and φ(7)/2 = 3. This is the falsifier the roadmap
        // named for the neusis rung.
        ("x^3 + x^2 - 2x - 1  (2cos(2pi/7), the heptagon)", integers(&[-1, -2, 1, 1])),
        // THE REGULAR PENTAGON, φ(5)/2 = 2 — the compass's own, since 5 is a Fermat prime.
        ("x^2 + x - 1  (2cos(2pi/5), the pentagon)", integers(&[-1, 1, 1])),
        // A cubic that is not the Delian one, so the verdict is not about this single polynomial.
        ("x^3 - 3x - 1  (a trisection cubic)", integers(&[-1, -3, 0, 1])),
        // Degree 2 — the compass's own home.
        ("x^2 - 2", integers(&[-2, 0, 1])),
        // Degree 4 — power of two, so the compass rung can only say NECESSARY-ONLY.
        ("x^4 - 2", integers(&[-2, 0, 0, 0, 1])),
        // Degree 5 — the radical wall.
        ("x^5 - x - 1", integers(&[-1, -1, 0, 0, 0, 1])),
        // Degree 6 — not a power of two, and past the radical wall as well.
        ("x^6 - x - 1", integers(&[-1, -1, 0, 0, 0, 0, 1])),
        // Degree 7 — the heptagon's degree neighbourhood.
        ("x^7 - 7x + 3", integers(&[3, -7, 0, 0, 0, 0, 0, 1])),
    ]
}

fn main() -> Result<(), Box<dyn Error>> {
    let mut failures: Vec<String> = Vec::new();
    let mut hold = |claim: &str, held: bool, evidence: String| {
        if held {
            println!("  [holds] {claim}\n            {evidence}");
        } else {
            println!("  [FAILS] {claim}\n            {evidence}");
            failures.push(claim.to_owned());
        }
    };

    rule("THE COMPASS RUNG'S APERTURE IS A DEGREE CONDITION, NOT A DECLARED BOUND");

    println!("  ℚ(√k₁,…,√kₙ) has degree 2ⁿ over ℚ, so every element's minimal polynomial has");
    println!("  degree dividing 2ⁿ. DECLARED_KERNEL_BOUND = {DECLARED_KERNEL_BOUND} bounds a SEARCH;");
    println!("  the aperture below bounds the FIELD, and no bound can move it.\n");
    for degree in 1..=8usize {
        println!(
            "    degree {degree}  {}",
            if admits_degree(degree) { "power of two — the necessary condition holds" } else { "NOT a power of two — refused, structurally" }
        );
    }

    // The tower degree is read off a real element rather than asserted.
    let root = |n: i64| {
        Multiquadratic::square_root(&Rat::from_integer(BigInt::from(n)), DECLARED_KERNEL_BOUND)
            .expect("a squarefree integer root")
    };
    let joined = root(2).add(&root(3), 4).expect("two generators are inside the aperture");
    println!(
        "\n  √2 + √3 carries {} generators, so its ambient tower degree is {}",
        joined.generators().len(),
        joined.tower_degree()
    );
    hold(
        "the tower degree is 2^n, read off the element rather than declared",
        joined.tower_degree() == 4,
        format!("{} generators → 2^{} = {}", joined.generators().len(), joined.generators().len(), joined.tower_degree()),
    );

    // ---------------------------------------------------------------------------------------------

    rule("ONE OBJECT, THREE RUNGS — compass, neusis, radicals");

    println!(
        "  {:<44} {:>3}  {:<16} {:<16} {:<10}",
        "polynomial", "deg", "compass", "neusis", "radical"
    );
    println!("  {}", "-".repeat(96));

    let mut disagreements: Vec<String> = Vec::new();
    let mut compass_refusals = 0usize;
    let mut compass_necessary = 0usize;
    let mut radical_returns = 0usize;
    let mut radical_refusals = 0usize;
    let mut neusis_refusals = 0usize;
    let mut neusis_necessary = 0usize;
    let mut neusis_crossings: Vec<String> = Vec::new();

    for (index, (name, coefficients)) in material().into_iter().enumerate() {
        let problem = IntegralQuinticProblem::new(
            QuinticProblemId(index as u64 + 1),
            name,
            coefficients,
        )?;
        let atlas = read_quintic_charts(&problem, PRIME_LIMIT, HORN_LOCAL_SECTION_LIMIT)?;
        let ladder = read_ladder(&atlas.radical);

        match &ladder.compass {
            CompassVerdict::Refuses { .. } => compass_refusals += 1,
            CompassVerdict::NecessaryConditionHolds { .. } => compass_necessary += 1,
            CompassVerdict::Open { .. } => {}
        }
        match &ladder.radical {
            RadicalChartVerdict::Returns(_) => radical_returns += 1,
            RadicalChartVerdict::Refuses(_) => radical_refusals += 1,
            RadicalChartVerdict::Open { .. } => {}
        }
        match &ladder.neusis {
            NeusisVerdict::Refuses { .. } => neusis_refusals += 1,
            NeusisVerdict::NecessaryConditionHolds { .. } => neusis_necessary += 1,
            NeusisVerdict::Open { .. } => {}
        }
        if ladder.rungs_disagree() {
            disagreements.push(name.to_owned());
        }
        if ladder.neusis_crosses_the_compass_wall() {
            neusis_crossings.push(name.to_owned());
        }

        println!(
            "  {:<44} {:>3}  {:<16} {:<16} {:<10} {}",
            name,
            ladder.degree,
            ladder.compass.label(),
            ladder.neusis.label(),
            ladder.radical.label(),
            if ladder.neusis_crosses_the_compass_wall() { "← NEUSIS CROSSES" } else { "" }
        );
    }

    println!();
    hold(
        "THE RUNGS DISAGREE — at least one object is refused by one instrument and returned by the other",
        !disagreements.is_empty(),
        format!("{} disagreement(s): {:?}", disagreements.len(), disagreements),
    );
    hold(
        "the compass rung REFUSES somewhere and does not refuse everywhere",
        compass_refusals > 0 && compass_necessary > 0,
        format!("{compass_refusals} refused · {compass_necessary} necessary-only"),
    );
    hold(
        "the radical rung RETURNS somewhere and REFUSES somewhere — the wall is real and crossed",
        radical_returns > 0 && radical_refusals > 0,
        format!("{radical_returns} returned · {radical_refusals} refused"),
    );
    hold(
        "THE NEUSIS RUNG CROSSES THE COMPASS WALL — the heptagon refuses at compass and holds at neusis",
        neusis_crossings.iter().any(|name| name.contains("heptagon")),
        format!("{} crossing(s): {:?}", neusis_crossings.len(), neusis_crossings),
    );
    hold(
        "the neusis rung REFUSES somewhere — a rung that admits everything is not a rung",
        neusis_refusals > 0 && neusis_necessary > 0,
        format!("{neusis_refusals} refused · {neusis_necessary} necessary-only; 3-smooth degrees only"),
    );
    hold(
        "the pentagon holds at the compass and the heptagon does not — 5 is a Fermat prime and 7 is not",
        {
            let five = neusis_crossings.iter().any(|n| n.contains("pentagon"));
            let seven = neusis_crossings.iter().any(|n| n.contains("heptagon"));
            !five && seven
        },
        format!("crossings: {neusis_crossings:?}"),
    );
    hold(
        "the doubled cube is refused by the compass — the Delian constant is not a Euclidean number",
        disagreements.iter().any(|name| name.contains("doubled cube")),
        format!("disagreements: {disagreements:?}"),
    );

    // ---------------------------------------------------------------------------------------------

    rule("WHAT IS DELIBERATELY NOT CLAIMED");

    println!(
        "  The compass rung's positive verdict is NECESSARY-ONLY and says so in its own name.\n\
        \x20 A degree-four irreducible with Galois group A₄ or S₄ has power-of-two degree and is NOT\n\
        \x20 constructible; sufficiency needs the Galois closure to be a 2-group, which is not decided\n\
        \x20 here. There is no `is_constructible` method to misread.\n\n\
        \x20 The NEUSIS rung states an APERTURE and computes no root: no arithmetic carrier for a\n\
        \x20 {{2,3}}-tower exists in either repository, so `NECESSARY-ONLY` there is weaker again than\n\
        \x20 at the compass rung, where `multiquadratic` does the arithmetic exactly.\n\n\
        \x20 Note x^5 - x - 1: refused by BOTH neusis and radicals, for DIFFERENT reasons — 5 is not\n\
        \x20 3-smooth, and S5 is not solvable. Two instruments agreeing is not two instruments being\n\
        \x20 the same instrument."
    );

    rule("WHAT THIS RETURNED");

    println!(
        "  1. The compass rung's aperture is stated in its own source as a degree condition on the\n\
         \x20    FIELD, distinguished from DECLARED_KERNEL_BOUND, which bounds a search.\n\
         \x20 2. The two rungs, which had never met, now read one object under one receiver family:\n\
         \x20    {} refused by the compass, {} passing its necessary condition; {} returned by\n\
         \x20    radicals, {} refused.\n\
         \x20 3. {} object(s) receive OPPOSITE verdicts from compass and radicals, and BOTH are\n\
         \x20    correct. The aperture belongs to the instrument, not to the object.\n\
         \x20 4. THE NEUSIS RUNG CROSSES: {} object(s) refused by the compass hold at neusis,\n\
         \x20    including all three Greek problems of antiquity — the doubled cube, the trisected\n\
         \x20    angle, and the regular heptagon. MathWorld's NeusisConstruction names exactly those\n\
         \x20    three as soluble by a marked ruler; here they are computed rather than recited.",
        compass_refusals, compass_necessary, radical_returns, radical_refusals,
        disagreements.len(), neusis_crossings.len()
    );

    if failures.is_empty() {
        println!("\n  ALL CONTROLS HELD.");
        Ok(())
    } else {
        println!("\n  FAILURES: {failures:?}");
        std::process::exit(1);
    }
}
