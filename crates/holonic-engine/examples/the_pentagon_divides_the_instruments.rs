//! THE PENTAGON DIVIDES THE INSTRUMENTS — two classical theorems disagree, and both are right.
//!
//! ```text
//! cargo run --release -p holonic-engine --example the_pentagon_divides_the_instruments
//! ```
//!
//! ## What this closes
//!
//! Roadmap open item 3. `winding_inertia.rs:62` has computed the crystallographic restriction since
//! it was written, under Niven's name:
//!
//! > *"By Niven's theorem `2cos(2πm/n)` is rational exactly when `n/gcd(m,n) ∈ {1,2,3,4,6}`, with
//! > values `2, −2, −1, 0, 1`."*
//!
//! A rotation of order `n` preserving a lattice acts on a lattice basis by an **integer** matrix, so
//! its trace `2cos(2π/n)` is an integer, forcing that same set. Niven gives the rational version and
//! the two coincide because a rational algebraic integer is an integer. The word
//! `crystallographic` occurred nowhere in the live tree before 2026-08-10.
//!
//! ## The receiver question
//!
//! **Do the compass and the lattice disagree about a regular polygon, and is each verdict correct?**
//!
//! The falsifier the roadmap named: **the pentagon must be admitted by the compass and refused by
//! the lattice, in the same run.** It is compass-constructible because 5 is a Fermat prime; it is
//! crystallographically forbidden because 5 ∉ {1,2,3,4,6}. Both are theorems.
//!
//! **A claim was falsified here on the first run and the correction is the better result.** The
//! record's §1.4 said *"neither aperture contains the other"*. That is false for regular polygons:
//! every crystallographic order has `φ(n) ∈ {1,2}`, a power of two, so **the lattice aperture is
//! contained in the compass aperture**, and the pentagon witnesses that the containment is *strict*.
//! With the neusis rung above (powers of two are 3-smooth) the polygon ladder is a **chain**:
//!
//! ```text
//!   lattice  ⊊  compass  ⊆  neusis  ⊆  radicals
//! ```
//!
//! which is a stronger statement than the one it replaces, and it makes the ladder an actual ladder
//! rather than a set of incomparable instruments.
//!
//! ## What is deliberately NOT claimed
//!
//! Both predicates are **derived**: `lattice_admits_order` calls `niven_value` rather than carrying a
//! written-out list, so the two cannot drift; `polygon_turn_degree` is `φ(n)/2` computed by trial
//! division with no table. And the compass test is decisive here where it was only necessary in
//! `the_two_instruments_disagree`, because a cyclotomic extension is **abelian**, so the Galois
//! closure is automatically a 2-group when the degree is a power of two. That is stated below rather
//! than assumed silently.
//!
//! Quasicrystals are named and not modelled: dropping periodicity admits five-fold symmetry, which is
//! `H.0420`'s purchased channel again, and nothing here computes one.

use std::error::Error;

use holonic_engine::multiquadratic::admits_degree;
use holonic_engine::quintic_chart::neusis_admits_degree;
use holonic_engine::winding_inertia::{lattice_admits_order, polygon_turn_degree};

/// APERTURE — how far up the polygon family to walk. Declared by this caller; every verdict below is
/// a function of `n` alone and nothing depends on where the walk stops.
const POLYGON_WALK: usize = 24;

fn rule(title: &str) {
    println!("\n{}", "=".repeat(96));
    println!("{title}");
    println!("{}", "=".repeat(96));
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

    rule("THE LATTICE RUNG IS NIVEN'S SET, DERIVED AND NOT WRITTEN DOWN");

    let admitted: Vec<usize> = (1..=POLYGON_WALK)
        .filter(|n| lattice_admits_order(*n))
        .collect();
    println!("  orders a periodic lattice admits, walked to {POLYGON_WALK}: {admitted:?}");
    println!(
        "  reason: a lattice-preserving rotation has an INTEGER matrix in a lattice basis, so"
    );
    println!("  its trace 2cos(2π/n) is an integer, so 2cos(2π/n) ∈ {{2,1,0,−1,−2}}.");
    hold(
        "the crystallographic restriction is derived from the Niven carrier, not carried beside it",
        admitted == vec![1, 2, 3, 4, 6],
        format!("{admitted:?} — the same five values winding_inertia already returns"),
    );

    // ---------------------------------------------------------------------------------------------

    rule("ONE POLYGON FAMILY, THREE INSTRUMENTS");

    println!(
        "  {:>4}  {:>10}  {:<12}  {:<12}  {:<12}",
        "n", "deg 2cos", "compass", "neusis", "lattice"
    );
    println!("  {}", "-".repeat(64));

    let mut compass_only: Vec<usize> = Vec::new();
    let mut lattice_only: Vec<usize> = Vec::new();
    let mut both: Vec<usize> = Vec::new();
    let mut neither: Vec<usize> = Vec::new();

    for sides in 3..=POLYGON_WALK {
        let degree = polygon_turn_degree(sides);
        let compass = admits_degree(degree);
        let neusis = neusis_admits_degree(degree);
        let lattice = lattice_admits_order(sides);
        match (compass, lattice) {
            (true, true) => both.push(sides),
            (true, false) => compass_only.push(sides),
            (false, true) => lattice_only.push(sides),
            (false, false) => neither.push(sides),
        }
        let mark = match (compass, lattice) {
            (true, false) => "  ← COMPASS ONLY",
            (false, true) => "  ← LATTICE ONLY",
            _ => "",
        };
        println!(
            "  {:>4}  {:>10}  {:<12}  {:<12}  {:<12}{}",
            sides,
            degree,
            if compass { "admits" } else { "REFUSES" },
            if neusis { "admits" } else { "REFUSES" },
            if lattice { "admits" } else { "REFUSES" },
            mark
        );
    }

    println!("\n  compass only {compass_only:?}");
    println!("  lattice only {lattice_only:?}");
    println!("  both         {both:?}");
    println!("  neither      {neither:?}");

    hold(
        "THE PENTAGON DIVIDES THE INSTRUMENTS — admitted by the compass, refused by the lattice",
        compass_only.contains(&5),
        format!(
            "5: degree {} is a power of two; 5 ∉ {{1,2,3,4,6}}",
            polygon_turn_degree(5)
        ),
    );
    hold(
        "the 17-gon divides them the same way — Gauss's own case, φ(17)/2 = 8",
        compass_only.contains(&17),
        format!("17: degree {}", polygon_turn_degree(17)),
    );
    hold(
        "the heptagon is refused by BOTH — 7 is not a Fermat prime and 7 ∉ {1,2,3,4,6}",
        neither.contains(&7),
        format!("7: degree {}", polygon_turn_degree(7)),
    );
    // FALSIFIED ON FIRST RUN, and the claim was mine rather than the code's. The record's §1.4 said
    // "neither aperture contains the other". It is false for regular polygons and provably so: every
    // crystallographic order has φ(n) ∈ {1,2}, a power of two, so the lattice aperture is CONTAINED
    // in the compass aperture. The pentagon witnesses that the containment is STRICT. The control
    // now asserts what is true and still fires if a lattice-only case ever appears.
    hold(
        "THE LATTICE APERTURE IS STRICTLY CONTAINED IN THE COMPASS APERTURE",
        lattice_only.is_empty() && !compass_only.is_empty(),
        format!(
            "lattice-only {lattice_only:?} (empty: every crystallographic order has φ(n) a power of \
             two) · compass-only {compass_only:?} (non-empty: the containment is strict)"
        ),
    );
    hold(
        "the two apertures agree somewhere, so the disagreement is not a sign error",
        !both.is_empty(),
        format!("both admit {both:?}"),
    );
    hold(
        "the neusis rung admits the heptagon where the compass refuses it",
        neusis_admits_degree(polygon_turn_degree(7)) && !admits_degree(polygon_turn_degree(7)),
        format!(
            "7: degree {} is 3-smooth and not a power of two",
            polygon_turn_degree(7)
        ),
    );

    // ---------------------------------------------------------------------------------------------

    rule("WHY THE COMPASS TEST IS DECISIVE HERE AND ONLY NECESSARY ELSEWHERE");

    println!(
        "  `the_two_instruments_disagree` reports NECESSARY-ONLY for a power-of-two degree, because\n\
        \x20 sufficiency needs the Galois closure to be a 2-group and a degree-four irreducible with\n\
        \x20 group A₄ or S₄ passes the degree test and is not constructible.\n\n\
        \x20 Here the extension is CYCLOTOMIC, hence ABELIAN, so its Galois group is its own closure\n\
        \x20 and a 2-power degree makes it a 2-group automatically. The degree test is therefore\n\
        \x20 decisive for regular polygons and only necessary in general. That is Gauss–Wantzel:\n\
        \x20 φ(n) a power of two, equivalently n = 2^k times distinct Fermat primes.\n\n\
        \x20 The Fermat primes among the walk: 3, 5, 17 — and 257, 65537 beyond it."
    );

    rule("WHAT THIS RETURNED");

    println!(
        "  1. The crystallographic restriction is now NAMED where it is computed, and derived from\n\
         \x20    the Niven carrier so the two cannot drift.\n\
         \x20 2. Walked to n = {POLYGON_WALK}: {} admitted by the compass alone, {} by the lattice\n\
         \x20    alone, {} by both, {} by neither.\n\
         \x20 3. THE POLYGON LADDER IS A CHAIN: lattice ⊊ compass ⊆ neusis ⊆ radicals. The\n\
         \x20    pentagon is constructible and crystallographically impossible, which makes the\n\
         \x20    first containment strict; the heptagon is refused by both ends of it; the hexagon\n\
         \x20    is admitted by both. This CORRECTS the record's claim that neither aperture\n\
         \x20    contains the other, which the first run of this driver falsified.",
        compass_only.len(),
        lattice_only.len(),
        both.len(),
        neither.len()
    );

    if failures.is_empty() {
        println!("\n  ALL CONTROLS HELD.");
        Ok(())
    } else {
        println!("\n  FAILURES: {failures:?}");
        std::process::exit(1);
    }
}
