//! Hermite reduction as a **coboundary move**, with the invariant it may not
//! touch computed exactly and compared across a gauge whose orbit is measured.
//!
//! # Why this is not the same move as a substitution
//!
//! A table of integration methods carries two species. A **substitution** is a
//! chart transition and carries a Jacobian. **Integration by parts and Hermite
//! reduction are coboundary moves**: they stay in one chart and change the
//! representative by an exact term. Merging the species destroys the invariant,
//! because the whole reason a coboundary move is *lawful* is that the integral
//! depends only on the cohomology class and an exact term is zero in it.
//!
//! ```text
//! f = h' + g       h rational, so Res_alpha(h') = 0 at every alpha
//! ```
//!
//! **So the representative moves and the residues do not.** That is the entire
//! mechanism, and this driver measures both halves of it.
//!
//! # The gauge, and why its orbit is measured rather than assumed
//!
//! Two reduction schedules are declared — descend the highest multiplicity
//! first, or the lowest. Nothing in the mathematics prefers either. **A gauge
//! whose group acts trivially on the declared material is not a gauge**, and a
//! family that agrees because its members did the same thing has proved
//! nothing. So this driver first exhibits that the schedules visit *different*
//! states, and only then reads their agreement as evidence.
//!
//! # The invariant is returned with no root extracted
//!
//! The residues come back as the **Rothstein–Trager resultant**
//!
//! ```text
//! R(z) = Res_x( B(x) - z D*'(x), D*(x) )
//! ```
//!
//! a polynomial over the rationals whose roots are exactly the residues.
//! Nothing is isolated, nothing is approximated, and two of them are compared
//! by exact equality rather than by magnitude.
//!
//! # What would refute the claim
//!
//! An `h` that fails to differentiate back; two schedules returning different
//! residue polynomials; a coboundary that moves a nonzero residue; or a change
//! that is *not* a coboundary leaving the residue polynomial unmoved — the last
//! being the control, since an invariant nothing can move is not measuring
//! anything.
//!
//! # What this may not be reported as
//!
//! This is not integration and not Risch. The field is `Q(x)`; there is no
//! algebraic or logarithmic extension, no field tower, and the log part is
//! returned as its resultant rather than as a sum of logarithms.
//!
//! ```text
//! cargo run --release -p holonic-engine --example the_representative_moves_and_the_residue_does_not
//! ```

use holonic_engine::hermite_reduction::{RationalFunction, ReductionSchedule, reduce};
use holonic_engine::rational_polynomial::RationalPolynomial;
use relational_geometry::exact::rat;

fn polynomial(coefficients: &[i64]) -> RationalPolynomial {
    RationalPolynomial::new(coefficients.iter().map(|value| rat(*value, 1)).collect())
}

fn product(factors: &[&RationalPolynomial]) -> RationalPolynomial {
    factors
        .iter()
        .fold(polynomial(&[1]), |carried, factor| carried.times(factor))
}

fn main() {
    println!("{}", "=".repeat(96));
    println!("THE REPRESENTATIVE MOVES AND THE RESIDUE DOES NOT");
    println!("{}", "=".repeat(96));
    println!();

    let x_minus_one = polynomial(&[-1, 1]);
    let x_plus_one = polynomial(&[1, 1]);
    let x = polynomial(&[0, 1]);

    // D = (x-1)^2 (x+1)^3 -- two multiplicities available, so the schedules
    // have something to disagree about.
    let denominator = product(&[
        &x_minus_one,
        &x_minus_one,
        &x_plus_one,
        &x_plus_one,
        &x_plus_one,
    ]);
    let numerator = polynomial(&[1, 2, 3]);

    println!(
        "  f = ({}) / ({})",
        numerator.written("x"),
        denominator.written("x")
    );
    println!("  D = (x - 1)^2 (x + 1)^3");
    println!();

    println!("{}", "-".repeat(96));
    println!("THE ORBIT -- measured BEFORE agreement is read as evidence");
    println!("{}", "-".repeat(96));

    let mut readings = Vec::new();
    for schedule in ReductionSchedule::DECLARED {
        let reading = reduce(&numerator, &denominator, schedule).expect("the fixture reduces");
        let descent: Vec<String> = reading
            .states
            .iter()
            .map(|state| format!("{}->{}", state.descended, state.descended - 1))
            .collect();
        println!("  {schedule:?}");
        println!(
            "      steps           {}   descent order   {}",
            reading.states.len(),
            descent.join("  ")
        );
        for (ordinal, state) in reading.states.iter().enumerate() {
            println!(
                "      state {ordinal}         {}",
                state.remaining.written("x")
            );
        }
        readings.push(reading);
    }

    let first: Vec<u32> = readings[0].states.iter().map(|s| s.descended).collect();
    let second: Vec<u32> = readings[1].states.iter().map(|s| s.descended).collect();
    let orbit_is_nontrivial = first != second;
    println!();
    println!(
        "  the two schedules visited different states   {}",
        if orbit_is_nontrivial {
            "YES"
        } else {
            "NO -- the gauge is vacuous on this material"
        }
    );
    if readings[0].states.len() != readings[1].states.len() {
        println!();
        println!(
            "  They did not even take the same NUMBER of steps. Descending (x+1)^3 to (x+1)^2"
        );
        println!(
            "  brings it level with (x-1)^2, so the squarefree decomposition then returns their"
        );
        println!(
            "  PRODUCT at multiplicity two and one step descends both. Descending (x-1)^2 first"
        );
        println!("  never creates that coincidence.");
    }

    println!();
    println!("{}", "-".repeat(96));
    println!("WHAT EACH SCHEDULE RETURNED");
    println!("{}", "-".repeat(96));
    for reading in &readings {
        println!("  {:?}", reading.schedule);
        println!("      h  = {}", reading.exact_part.written("x"));
        println!("      g  = {}", reading.remaining.written("x"));
        println!("      Res(z) = {}", reading.residue_polynomial.written("z"));
        println!(
            "      f = h' + g verified exactly                  {}",
            if reading.returns_under_differentiation {
                "YES"
            } else {
                "NO"
            }
        );
        println!(
            "      remaining denominator squarefree             {}",
            if reading.remaining_denominator_is_squarefree {
                "YES"
            } else {
                "NO"
            }
        );
    }

    let residues_agree = readings[0].residue_polynomial == readings[1].residue_polynomial;
    let both_return = readings.iter().all(|r| r.returns_under_differentiation);
    println!();
    println!(
        "  the residue polynomials agree across the gauge   {}",
        if residues_agree { "YES" } else { "NO" }
    );

    println!();
    println!("{}", "-".repeat(96));
    println!("A COBOUNDARY MAY CREATE A POLE, BUT ONLY AT RESIDUE ZERO");
    println!("{}", "-".repeat(96));

    let base = RationalFunction::new(polynomial(&[1]), x_minus_one.clone()).expect("nonzero");
    let at_a_new_pole = base.plus(
        &RationalFunction::new(polynomial(&[1]), product(&[&x, &x]))
            .expect("nonzero")
            .derivative(),
    );
    let at_a_standing_pole = base.plus(
        &RationalFunction::new(polynomial(&[1]), x_minus_one.clone())
            .expect("nonzero")
            .derivative(),
    );

    let plain = reduce(
        &base.numerator,
        &base.denominator,
        ReductionSchedule::HighestMultiplicityFirst,
    )
    .expect("reduces");
    let standing = reduce(
        &at_a_standing_pole.numerator,
        &at_a_standing_pole.denominator,
        ReductionSchedule::HighestMultiplicityFirst,
    )
    .expect("reduces");
    let fresh = reduce(
        &at_a_new_pole.numerator,
        &at_a_new_pole.denominator,
        ReductionSchedule::HighestMultiplicityFirst,
    )
    .expect("reduces");

    println!("  f              = 1/(x - 1)");
    println!(
        "      Res(z) = {:<22}  nonzero part {}",
        plain.residue_polynomial.written("z"),
        plain.nonzero_residue_polynomial().written("z")
    );
    println!("  f + d/dx[1/(x - 1)]        -- exact, at a pole f already has");
    println!(
        "      Res(z) = {:<22}  nonzero part {}",
        standing.residue_polynomial.written("z"),
        standing.nonzero_residue_polynomial().written("z")
    );
    println!("  f + d/dx[1/x^2]            -- exact, at a pole f does NOT have");
    println!(
        "      Res(z) = {:<22}  nonzero part {}",
        fresh.residue_polynomial.written("z"),
        fresh.nonzero_residue_polynomial().written("z")
    );
    println!();
    println!("  The third grew a root at z = 0 and moved nothing else. A rational function's");
    println!("  derivative has zero residue at every pole, so a coboundary can add a POLE but");
    println!("  never a RESIDUE.");

    let standing_pole_holds = standing.residue_polynomial == plain.residue_polynomial;
    let new_pole_holds = fresh.nonzero_residue_polynomial() == plain.nonzero_residue_polynomial()
        && fresh.residue_polynomial != plain.residue_polynomial;

    println!();
    println!("{}", "-".repeat(96));
    println!("THE CONTROL -- a change that is NOT a coboundary must move the class");
    println!("{}", "-".repeat(96));
    let doubled = reduce(
        &polynomial(&[2]),
        &x_minus_one,
        ReductionSchedule::HighestMultiplicityFirst,
    )
    .expect("reduces");
    println!(
        "  1/(x - 1)  ->  Res(z) = {}",
        plain.residue_polynomial.written("z")
    );
    println!(
        "  2/(x - 1)  ->  Res(z) = {}",
        doubled.residue_polynomial.written("z")
    );
    let control_moves = doubled.residue_polynomial != plain.residue_polynomial;
    println!(
        "  the non-coboundary moved the class              {}",
        if control_moves {
            "YES"
        } else {
            "NO -- the invariant is insensitive and proves nothing"
        }
    );

    println!();
    println!("{}", "=".repeat(96));
    println!("WHAT RETURNED");
    println!("{}", "=".repeat(96));
    println!(
        "  schedules declared                             {}",
        ReductionSchedule::DECLARED.len()
    );
    println!("  gauge orbit non-trivial on this material       {orbit_is_nontrivial}");
    println!("  every h differentiated back exactly            {both_return}");
    println!("  residue polynomials agree across the gauge     {residues_agree}");
    println!("  coboundary at a standing pole moved nothing    {standing_pole_holds}");
    println!("  coboundary at a new pole added only z          {new_pole_holds}");
    println!("  non-coboundary control moved the class         {control_moves}");

    println!();
    println!("{}", "-".repeat(96));
    println!("WHAT THIS RUN DOES NOT ESTABLISH");
    println!("{}", "-".repeat(96));
    println!("  The field is Q(x). No algebraic or logarithmic extension is constructed, no");
    println!("  logarithm is emitted, and no root of the residue polynomial is isolated. This is");
    println!("  the reduction phase of a two-phase algorithm, not the algorithm.");

    println!();
    println!("{}", "=".repeat(96));
    if orbit_is_nontrivial
        && both_return
        && residues_agree
        && standing_pole_holds
        && new_pole_holds
        && control_moves
    {
        println!(
            "HELD -- the gauge has a real orbit, every reduction differentiated back, and the"
        );
        println!("        residues survived every coboundary while a non-coboundary moved them.");
    } else {
        println!(
            "REFUTED -- orbit={orbit_is_nontrivial} return={both_return} agree={residues_agree} standing={standing_pole_holds} fresh={new_pole_holds} control={control_moves}"
        );
        println!("{}", "=".repeat(96));
        std::process::exit(1);
    }
    println!("{}", "=".repeat(96));
}
