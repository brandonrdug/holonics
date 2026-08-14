//! The deficit organ and the winding organ operate on one matrix, and this is where they meet.
//!
//! `discrete_curvature` reads a vertex's deficit from the responses on its incident hinges.
//! `winding_inertia` reads a circulant form's inertia as named passages, each labelled by the star
//! polygon `{n/k}` its character traces. They were built for different questions and until
//! 2026-08-08 **no file in the repository consumed both** — measured, not assumed.
//!
//! They are the same operator. On a cycle `C_n` every vertex has link size two, so the deficit
//! functional's homogeneous part is
//!
//! ```text
//!   I - Bᵀ D⁻¹ B  =  -A/2
//! ```
//!
//! where `B` is the unsigned vertex–hinge incidence, `D` the hinge degree, and `A` the adjacency
//! whose characters `winding_inertia` names. The identity is elementary — `BᵀB = D_v + A` and
//! `D_v = 2I` on a cycle — and it is checked here in the engine's own exact rationals rather than
//! asserted.
//!
//! **What this does NOT say.** It is not the identification refused on 2026-08-08 in
//! `research/records/2026-08-08_THE_DEFICIT_IS_THE_OCTAVE_THE_LINEAGE_TORSION_IS_THE_HAND.md`. That
//! refusal was *deficit angle against lineage torsion*, it had a witness — torsion created with every
//! deficit held fixed — and it stands. This is *the deficit functional's homogeneous part against the
//! adjacency spectrum*, on the one family where both organs are defined, and it is an identity rather
//! than a correspondence. The two claims are about different pairs of objects and neither bears on
//! the other.
//!
//! Run: `PATH=/opt/cuda/bin:$PATH cargo run -p holonic-engine --example curvature_is_the_adjacency`

use holonic_engine::discrete_curvature::{DiscreteCurvatureConfiguration, FLAT_COORDINATION};
use holonic_engine::winding_inertia::{Hand, PassageReturn, SymmetricCirculant, winding_inertia};
use holonic_engine::{HingeId, VertexId};
use num_bigint::BigInt;
use relational_geometry::Rat;

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

/// The cycle `C_n` as a curvature configuration: `n` vertices of link size two, `n` hinges at unit
/// response.
fn cycle_configuration(n: usize) -> DiscreteCurvatureConfiguration {
    let vertices = (0..n).map(|index| (VertexId(index as u64), 2usize));
    let hinges = (0..n).map(|index| {
        (
            HingeId(index as u64),
            [VertexId(index as u64), VertexId(((index + 1) % n) as u64)],
            integer(1),
        )
    });
    DiscreteCurvatureConfiguration::found(vertices, hinges).expect("a cycle is a lawful hinge body")
}

/// `I − BᵀD⁻¹B` on `C_n`, built from the incidence directly and in exact rationals.
fn homogeneous_part(n: usize) -> Vec<Vec<Rat>> {
    let mut matrix = vec![vec![integer(0); n]; n];
    for (index, row) in matrix.iter_mut().enumerate().take(n) {
        row[index] = integer(1);
    }
    // Bᵀ D⁻¹ B, with D = 2I over the hinges and B the unsigned incidence.
    let half = Rat::new(BigInt::from(1), BigInt::from(2));
    for edge in 0..n {
        let ends = [edge, (edge + 1) % n];
        for &a in &ends {
            for &b in &ends {
                matrix[a][b] = matrix[a][b].clone() - half.clone();
            }
        }
    }
    matrix
}

/// `−A/2` for the cycle `C_n`.
fn negative_half_adjacency(n: usize) -> Vec<Vec<Rat>> {
    let half = Rat::new(BigInt::from(1), BigInt::from(2));
    let mut matrix = vec![vec![integer(0); n]; n];
    for (i, row) in matrix.iter_mut().enumerate().take(n) {
        for (j, entry) in row.iter_mut().enumerate().take(n) {
            let apart = (i + n - j) % n;
            if apart == 1 || apart == n - 1 {
                *entry = -half.clone();
            }
        }
    }
    matrix
}

fn main() {
    println!("THE DEFICIT FUNCTIONAL AND THE ADJACENCY ARE ONE OPERATOR");
    println!("=========================================================\n");
    println!("  Both organs are defined on the cycle C_n and neither has ever consumed the other.");
    println!(
        "  FLAT_COORDINATION = {FLAT_COORDINATION}, and every vertex of a cycle has link two,"
    );
    println!("  so every deficit below is the same number; what differs is the spectrum.\n");

    let mut identity_held = 0usize;
    let mut checked = 0usize;
    let mut failures = Vec::new();

    for n in 3..=12usize {
        let configuration = cycle_configuration(n);

        // The deficit organ's return.
        let deficits: Vec<Rat> = (0..n)
            .map(|index| {
                configuration
                    .deficit(VertexId(index as u64))
                    .expect("every vertex of the configuration has a deficit")
            })
            .collect();
        let total = configuration.total_deficit();

        // The winding organ's return, on the adjacency of the same cycle.
        let mut first_row = vec![integer(0); n];
        first_row[1] = integer(1);
        first_row[n - 1] = integer(1);
        let circulant =
            SymmetricCirculant::from_first_row(first_row).expect("a cycle adjacency is circulant");
        let reading = winding_inertia(&circulant).expect("the cycle adjacency reads");
        let split = reading.split();
        let against = reading.windings_of(Hand::AgainstTheTurn);
        let nulls: Vec<String> = reading
            .passages
            .iter()
            .filter(|passage| passage.returns == PassageReturn::OnTheNullCone)
            .map(|passage| format!("{}", passage.winding))
            .collect();

        // The identity, in exact rationals.
        let homogeneous = homogeneous_part(n);
        let target = negative_half_adjacency(n);
        checked += 1;
        if homogeneous == target {
            identity_held += 1;
        } else {
            failures.push(n);
        }

        let against_named: Vec<String> = against.iter().map(|w| format!("{w}")).collect();
        println!(
            "  C_{n:<2}  deficit/vertex {:>3}   total {:>5}   split ({}, {}, {})",
            deficits[0], total, split.positive, split.zero, split.negative
        );
        println!(
            "        against the turn at {:?}{}",
            against_named,
            if nulls.is_empty() {
                String::new()
            } else {
                format!("   null at {nulls:?}")
            }
        );
        println!(
            "        I - Bt D^-1 B == -A/2 : {}",
            if homogeneous == target {
                "HELD"
            } else {
                "BROKE"
            }
        );
    }

    println!("\n  ----------------------------------------------------------------");
    println!("  the identity held on {identity_held} of {checked} cycles");
    if !failures.is_empty() {
        println!("  BROKE at n = {failures:?}");
    }

    // ---- the declared controls -------------------------------------------------------------
    let mut controls: Vec<(&str, bool, String)> = Vec::new();

    controls.push((
        "the identity holds on every cycle in the declared range",
        failures.is_empty() && checked == 10,
        format!("{identity_held}/{checked}"),
    ));

    // The deficit is CONSTANT across the family while the spectrum is not. That is the whole reason
    // the two organs are not interchangeable even though they share an operator.
    let deficits: Vec<Rat> = (3..=12usize)
        .map(|n| {
            cycle_configuration(n)
                .deficit(VertexId(0))
                .expect("defined")
        })
        .collect();
    let deficit_constant = deficits.windows(2).all(|pair| pair[0] == pair[1]);
    let splits: Vec<(usize, usize, usize)> = (3..=12usize)
        .map(|n| {
            let mut row = vec![integer(0); n];
            row[1] = integer(1);
            row[n - 1] = integer(1);
            let circulant = SymmetricCirculant::from_first_row(row).unwrap();
            let split = winding_inertia(&circulant).unwrap().split();
            (split.positive, split.zero, split.negative)
        })
        .collect();
    let spectrum_varies = splits
        .iter()
        .collect::<std::collections::BTreeSet<_>>()
        .len()
        > 1;
    controls.push((
        "the deficit is constant across the family while the spectrum is not",
        deficit_constant && spectrum_varies,
        format!(
            "deficit constant {deficit_constant}, distinct splits {}",
            splits
                .iter()
                .collect::<std::collections::BTreeSet<_>>()
                .len()
        ),
    ));

    // The nulls appear exactly when 4 | n -- the quarter turn, CLAUDE.md section 2b. Read here
    // through the same organ that computes the split, on the same material the deficit reads.
    let mut null_law = true;
    for n in 3..=12usize {
        let mut row = vec![integer(0); n];
        row[1] = integer(1);
        row[n - 1] = integer(1);
        let circulant = SymmetricCirculant::from_first_row(row).unwrap();
        let nulls = winding_inertia(&circulant)
            .unwrap()
            .passages
            .iter()
            .filter(|passage| passage.returns == PassageReturn::OnTheNullCone)
            .count();
        if (n % 4 == 0) != (nulls == 2) {
            null_law = false;
        }
    }
    controls.push((
        "the cycle returns nothing at exactly the quarter turn, and only when 4 divides n",
        null_law,
        "n = 3..12".to_owned(),
    ));

    println!("\nDECLARED CONTROLS");
    println!("-----------------");
    let mut failed = 0usize;
    for (name, held, detail) in &controls {
        println!("  [{}] {name}", if *held { "holds" } else { "FAILED" });
        println!("          {detail}");
        if !held {
            failed += 1;
        }
    }
    println!(
        "\n{} -- {} declared controls, {failed} failed",
        if failed == 0 { "HELD" } else { "BROKE" },
        controls.len()
    );
    if failed != 0 {
        std::process::exit(1);
    }
}
