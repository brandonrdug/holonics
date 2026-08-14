//! Whether a three-site turning equation's solution **closes**, decided by
//! sorting integers on a circle.
//!
//! # The object, in composable terms
//!
//! A second-order transport law well behaved everywhere except at three sites —
//! `0`, `1`, infinity. At each site a solution carried once round in a small
//! loop comes back **turned**; those three amounts are the **local turn
//! numbers**. Composing the loops generates the **return group**.
//!
//! **Finite return group means the solution takes finitely many values and
//! closes. Infinite means it never closes.**
//!
//! (Classical labels, for looking things up: the *hypergeometric equation*, its
//! *exponent differences*, and its *monodromy group*.)
//!
//! # What decides it
//!
//! Put the dials on a circle. Two families of marks appear — the **numerator**
//! marks for `a` and `b`, and the **denominator** marks for `c` and for `1`,
//! which sits at position zero because a whole turn is no turn.
//!
//! **The group is finite exactly when the two families take turns round the
//! circle**, and it must keep taking turns under **every restretching** —
//! multiply every mark by a whole number sharing no factor with the circle and
//! look again. (Classically: the *Beukers–Heckman interlacing criterion*, and
//! the restretchings are its *Galois conjugates*.)
//!
//! Over a common denominator every mark is an integer. So the whole decision is
//! sorting integers and checking labels alternate. **Nothing is extracted, no
//! angle is taken, no matrix is built, and no float appears.**
//!
//! # The two frames, and only one is allowed to decide
//!
//! There is a classical table of fifteen closing turn-number rows, one per
//! finite rotation group of the sphere (classically *Schwarz's list*). **It is
//! the control here and never the decider.** A table consulted to classify its
//! own rows returns the preimage of its own declaration and carries no evidence.
//! The alternation test computes from the dials; the fifteen rows check it.
//!
//! # What would refute the claim
//!
//! A classically closing row that the alternation test refuses; a triple off the
//! table that it admits; a non-spherical triple that closes; or a family in
//! which **no** material fails only under a restretching — which would prove the
//! restretching loop is decorative and could be deleted with every test still
//! passing.
//!
//! # What this may not be reported as
//!
//! This decides finiteness of the return group. It does not build the group, does
//! not produce the algebraic solution, and does not integrate anything. Second
//! order only, rational dials only.
//!
//! ```text
//! cargo run --release -p holonic-engine --example the_solution_closes_when_the_marks_take_turns
//! ```

use holonic_engine::hypergeometric_closure::{
    closing_turn_table, read_from_turns, read_return_group, ClosureReading, CurvatureSign,
    LocalTurns, ThreeSiteDials,
};
use num_bigint::BigInt;
use relational_geometry::Rat;

fn rational(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn turns(p: i64, q: i64, r: i64, s: i64, t: i64, u: i64) -> LocalTurns {
    LocalTurns::new(rational(p, q), rational(r, s), rational(t, u))
}

fn written(turns: &LocalTurns) -> String {
    format!(
        "({}, {}, {})",
        turns.at_zero, turns.at_one, turns.at_infinity
    )
}

fn main() {
    println!("{}", "=".repeat(96));
    println!("THE SOLUTION CLOSES WHEN THE MARKS TAKE TURNS");
    println!("{}", "=".repeat(96));
    println!();
    println!("  Three sites. Three local turn numbers. Put the dials on a circle as two families");
    println!("  of marks and ask whether they alternate -- under every restretching of the circle.");
    println!();

    println!("{}", "-".repeat(96));
    println!("THE CONTROL -- fifteen classically closing rows, each decided by the test alone");
    println!("{}", "-".repeat(96));
    println!(
        "{:>4} {:>22} {:>26} {:>7} {:>6} {:>10}",
        "row", "turn numbers", "dials (a, b, c)", "circle", "spins", "closes"
    );
    let mut rows_closing = 0_u32;
    for (row, (turn_numbers, solid)) in closing_turn_table() {
        let reading = read_from_turns(&turn_numbers).expect("the row is inside the aperture");
        let spins = match &reading.closure {
            ClosureReading::Closes {
                restretchings_checked,
                ..
            } => *restretchings_checked,
            ClosureReading::DoesNotClose {
                restretchings_checked,
                ..
            } => *restretchings_checked,
            ClosureReading::Splits { .. } => 0,
        };
        if reading.closure.closes() {
            rows_closing += 1;
        }
        println!(
            "{:>4} {:>22} {:>26} {:>7} {:>6} {:>10}   {:?}",
            row,
            written(&turn_numbers),
            format!(
                "({}, {}, {})",
                reading.dials.a, reading.dials.b, reading.dials.c
            ),
            reading.closure.circle(),
            spins,
            if reading.closure.closes() { "YES" } else { "NO" },
            solid
        );
    }

    println!();
    println!("{}", "-".repeat(96));
    println!("WHAT DOES NOT CLOSE, WITH THE OBSTRUCTION EXHIBITED");
    println!("{}", "-".repeat(96));
    let refused = [
        ("the elliptic case", turns(0, 1, 0, 1, 0, 1)),
        ("saddle, all quarters", turns(1, 4, 1, 4, 1, 4)),
        ("saddle, all sevenths", turns(1, 7, 1, 7, 1, 7)),
        ("saddle, all eighths", turns(1, 8, 1, 8, 1, 8)),
    ];
    let mut refusals = 0_u32;
    for (name, turn_numbers) in &refused {
        let reading = read_from_turns(turn_numbers).expect("inside the aperture");
        let geometry = match reading.curvature {
            CurvatureSign::Spherical => "sphere",
            CurvatureSign::Flat => "flat",
            CurvatureSign::Saddle => "saddle",
        };
        println!(
            "  {name:<24} {:<18} {geometry:<8} circle {}",
            written(turn_numbers),
            reading.closure.circle()
        );
        println!(
            "      numerator marks {:?}   denominator marks {:?}",
            reading.numerator_marks, reading.denominator_marks
        );
        match &reading.closure {
            ClosureReading::DoesNotClose {
                failing_restretching,
                adjacency,
                ..
            } => {
                refusals += 1;
                println!(
                    "      REFUSED  spin x{failing_restretching} put {:?} marks {} and {} next to each other",
                    adjacency.family, adjacency.first, adjacency.second
                );
            }
            ClosureReading::Closes { .. } => println!("      CLOSES -- which would refute the split"),
            ClosureReading::Splits { coincident_mark, .. } => {
                println!("      SPLITS at mark {coincident_mark}")
            }
        }
    }

    println!();
    println!("{}", "-".repeat(96));
    println!("THE THIRD OUTCOME -- THE FLAT LOCUS IS THE SPLITTING LOCUS");
    println!("{}", "-".repeat(96));
    println!("  The signed turn sum is 1 - 2b identically, so a FLAT triple forces a dial to zero,");
    println!("  and a dial at zero lands on the denominator family's mark at zero. Every flat");
    println!("  triple therefore splits rather than merely failing to close. This was found by");
    println!("  this driver refuting a fixture that had listed a flat triple as a refusal.");
    println!();
    let flat = [
        turns(1, 3, 1, 3, 1, 3),
        turns(1, 2, 1, 3, 1, 6),
        turns(1, 2, 1, 4, 1, 4),
        turns(1, 6, 1, 3, 1, 2),
    ];
    let mut all_flat_split = true;
    for triple in &flat {
        let reading = read_from_turns(triple).expect("inside the aperture");
        let split_at = match &reading.closure {
            ClosureReading::Splits {
                coincident_mark, ..
            } => Some(*coincident_mark),
            _ => None,
        };
        all_flat_split &= split_at.is_some() && reading.curvature == CurvatureSign::Flat;
        println!(
            "  {:<18} dials ({}, {}, {})   marks {:?} against {:?}   {}",
            written(triple),
            reading.dials.a,
            reading.dials.b,
            reading.dials.c,
            reading.numerator_marks,
            reading.denominator_marks,
            match split_at {
                Some(mark) => format!("SPLITS at {mark}"),
                None => format!("{:?} -- refutes the law", reading.closure),
            }
        );
    }
    let splits_by_name = all_flat_split;

    println!();
    println!("{}", "-".repeat(96));
    println!("THE RESTRETCHING IS LOAD-BEARING -- material that alternates AS DRAWN and fails spun");
    println!("{}", "-".repeat(96));
    let mut found = Vec::new();
    for numerator in 1..30_i64 {
        for denominator in 1..30_i64 {
            let dials = ThreeSiteDials::new(
                rational(numerator, 30),
                rational(denominator, 30),
                rational(1, 2),
            );
            let Ok(reading) = read_return_group(&dials) else {
                continue;
            };
            if let ClosureReading::DoesNotClose {
                failing_restretching,
                adjacency,
                ..
            } = &reading.closure
            {
                if *failing_restretching > 1 {
                    found.push((
                        numerator,
                        denominator,
                        *failing_restretching,
                        reading.numerator_marks.clone(),
                        reading.denominator_marks.clone(),
                        *adjacency,
                    ));
                }
            }
        }
    }
    println!("  swept a/30 and b/30 with c = 1/2, over a circle of 60");
    println!(
        "  material alternating as drawn but failing under a spin   {}",
        found.len()
    );
    for (numerator, denominator, multiplier, marks, denominator_marks, adjacency) in
        found.iter().take(5)
    {
        println!(
            "      a = {numerator}/30  b = {denominator}/30   drawn {marks:?} against {denominator_marks:?}"
        );
        println!(
            "          spin x{multiplier} put {:?} marks {} and {} together",
            adjacency.family, adjacency.first, adjacency.second
        );
    }
    if found.len() > 5 {
        println!("      ... and {} more", found.len() - 5);
    }
    let restretching_is_load_bearing = !found.is_empty();

    println!();
    println!("{}", "=".repeat(96));
    println!("WHAT RETURNED");
    println!("{}", "=".repeat(96));
    println!("  classically closing rows, all decided by the test   {rows_closing} of 15");
    println!("  declared non-closing triples refused                {refusals} of {}", refused.len());
    println!("  every flat triple split rather than refusing        {splits_by_name}");
    println!("  restretching loop exercised by real material        {restretching_is_load_bearing}");

    println!();
    println!("{}", "-".repeat(96));
    println!("WHAT THIS RUN DOES NOT ESTABLISH");
    println!("{}", "-".repeat(96));
    println!("  This decides FINITENESS of the return group. It does not build the group, does not");
    println!("  produce the algebraic solution, and does not integrate anything. Second order only,");
    println!("  rational dials only. The fifteen rows were never consulted to decide any verdict.");

    println!();
    println!("{}", "=".repeat(96));
    if rows_closing == 15
        && refusals as usize == refused.len()
        && splits_by_name
        && restretching_is_load_bearing
    {
        println!("HELD -- every classically closing row was recovered by sorting integers, every");
        println!("        declared non-closing triple was refused with its adjacent pair exhibited,");
        println!("        and the restretching is doing work rather than decorating the criterion.");
    } else {
        println!("REFUTED -- rows={rows_closing}/15 refusals={refusals} splits={splits_by_name} spins={restretching_is_load_bearing}");
        println!("{}", "=".repeat(96));
        std::process::exit(1);
    }
    println!("{}", "=".repeat(96));
}
