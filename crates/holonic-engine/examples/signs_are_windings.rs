//! Signs, returned as windings.
//!
//! ## What this is
//!
//! `inertia.rs` computes the split of a symmetric form correctly, by elimination, with no
//! trigonometry anywhere. What it returns is a **count of signs**, and `CLAUDE.md` §2b strikes that
//! reading:
//!
//! > *"What the signed floor signs is the PASSAGE, never the state."* — Brandon, 2026-08-08
//!
//! > **A count of signs is a state reading. Name the windings instead.**
//!
//! Holomorphically `−1 = e^{iπ}`. There is no separate species of quantity called negative; there is
//! rotation, and a sign is what remains of a phase once the winding has been deleted. A float keeps
//! the magnitude and discards the residual; the unsigned floor keeps the magnitude and discards the
//! turn. This driver keeps the turn.
//!
//! When a symmetric form carries a circulant symmetry its inertia **factors through the character
//! group**: every eigendirection is a character `χ_k` and its sign is fixed by `k` alone. So the
//! lawful return is not *"five negative directions"* but *these five passages, each labelled by how
//! far it winds* — and for the cycle's own adjacency the label is exact:
//!
//! ```text
//!   2cos(2πk/n) < 0   ⟺   2πk/n > π/2   ⟺   the step exceeds ONE QUARTER TURN
//! ```
//!
//! ## The exactness route
//!
//! Exact algebraic, with an exact rational special case wherever Niven's theorem supplies one. There
//! is no float, no tolerance and no epsilon anywhere below.
//!
//! - `2cos(2πm/n)` is isolated by **Sturm bisection** on the squarefree part of the Dickson
//!   polynomial `D_n(x) − 2`, driving the `AlgebraicRoot` carrier `CLAUDE.md` §11 measured at zero
//!   drivers in any `examples/`, `tests/` or `bin/` path. This file is the driver.
//! - Nullity is decided **algebraically and finitely**, never as a limit: `λ_k = 0` exactly when the
//!   cyclotomic `Φ_{n/gcd(k,n)}` divides the symbol, which is one exact polynomial division. That
//!   cyclotomic is the passage's own star polygon in lowest terms, so the null test asks whether
//!   this passage's star polygon divides the form.
//! - Every passage is certified against `det(xI − C)` computed by **Faddeev–LeVerrier** — a
//!   determinant, which knows nothing of characters or roots of unity.
//!
//! ## The declared controls
//!
//! Per `CLAUDE.md` §8, a law that returns zero proves nothing about itself, and a receipt that could
//! not have come out otherwise carries no evidence. So:
//!
//! - the character split is compared with the **elimination's** split, on a family carrying definite,
//!   indefinite and degenerate shapes — a family of one shape could not disagree;
//! - the elimination is then handed `P^T C P` for a non-circulant `P`, which is **refused as not
//!   circulant** and still returns the split the characters named, so it cannot have been reading
//!   the symmetry;
//! - the quarter-turn law is swept over **both halves** of `4 | n`, so neither "always null" nor
//!   "never null" can pass;
//! - a circulant whose passages are all one hand must report **no** winding past the hand;
//! - circulants with entries far beyond `{0,1}` are read, so the law is not a property of the
//!   adjacency fixture;
//! - and one form is taken from a circuit the machine actually **grew**.

use holonic_engine::exact_linear::ExactRatMatrix;
use holonic_engine::grown_cell::{ComplexAperture, Schedule, found_complex, grow, standard_cells};
use holonic_engine::inertia::{Inertia, PivotOrder, SymmetricForm, congruence, inertia};
use holonic_engine::winding_inertia::{
    Hand, PassageReturn, StarTable, SymmetricCirculant, WindingError, WindingInertia,
    cycle_adjacency, cycle_laplacian, cyclic_receiver_of_growth, quarter_turn_reading,
    winding_inertia,
};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use relational_geometry::{Rat, format_rat};

fn circulant(first_row: &[i64]) -> SymmetricCirculant {
    SymmetricCirculant::from_integers(first_row).expect("the declared row is reversal-symmetric")
}

fn interval_text(reading: &WindingInertia, character: usize) -> String {
    let passage = &reading.passages[character];
    let enclosure = passage.enclosure(&reading.integral_scale);
    if enclosure.is_point() {
        format!("= {}", format_rat(&enclosure.lower))
    } else {
        format!(
            "in [{}, {}]",
            format_rat(&enclosure.lower),
            format_rat(&enclosure.upper)
        )
    }
}

/// The artifact. Every passage, named by its winding, never counted.
fn print_passages(title: &str, reading: &WindingInertia) {
    let split = reading.split();
    println!(
        "\n  {title}   extent {}   split ({}, {}, {})   symbol {:?}",
        reading.extent, split.positive, split.zero, split.negative, reading.symbol
    );
    println!(
        "      k    winding   star polygon   what traversal returns   eigenvalue      certificate"
    );
    for passage in &reading.passages {
        let witness = match &passage.null_witness {
            Some(witness) => format!("Phi_{} divides f", witness.order),
            None => format!(
                "1 root of deg {} in [{}, {}]",
                passage.certificate.polynomial.degree(),
                format_rat(&passage.certificate.isolating_interval.lower),
                format_rat(&passage.certificate.isolating_interval.upper)
            ),
        };
        println!(
            "    {:>3}   {:>8}   {:>12}   {:<22}   {:<14}  {}",
            passage.character,
            format_rat(&passage.winding),
            passage.star_polygon.label(),
            passage.returns.name(),
            interval_text(reading, passage.character),
            witness
        );
    }
    let past: Vec<String> = reading
        .windings_past_the_hand()
        .iter()
        .map(format_rat)
        .collect();
    let nulls: Vec<String> = reading.null_windings().iter().map(format_rat).collect();
    println!("      against the turn at windings: {past:?}");
    println!("      returns nothing at windings:  {nulls:?}");
}

/// A unitriangular rational basis that is deliberately not circulant.
fn scrambling_basis(extent: usize) -> ExactRatMatrix {
    let mut rows = vec![vec![Rat::zero(); extent]; extent];
    for (index, row) in rows.iter_mut().enumerate() {
        row[index] = Rat::one();
    }
    if extent >= 3 {
        rows[0][2] = Rat::from_integer(BigInt::from(3));
    }
    if extent >= 4 {
        rows[1][3] = -Rat::from_integer(BigInt::from(2));
    }
    if extent >= 5 {
        rows[0][4] = Rat::new(BigInt::from(1), BigInt::from(2));
    }
    ExactRatMatrix::new(rows).expect("the basis is rectangular")
}

type Holds = Vec<(&'static str, bool, String)>;

fn main() {
    let mut holds: Holds = Vec::new();

    // =========================================================================================
    println!("\n=========================================================================");
    println!("  THE MEASURED CLAIM: a sign is the winding of a star polygon past the hand");
    println!("=========================================================================");
    println!(
        "\n  The cycle C_n's adjacency eigenvalues are 2cos(2*pi*k/n), one per star polygon {{n/k}}\n  \
         -- the n-grams on the same vertex set. The eigenvalue is negative exactly when the step\n  \
         exceeds one quarter turn, and the form returns NOTHING precisely at the hand."
    );

    let triangle = winding_inertia(&cycle_adjacency(3).unwrap()).unwrap();
    print_passages("C_3 adjacency  (the triangle)", &triangle);
    holds.push((
        "the triangle returns one zero-frequency passage and two that wind past the quarter",
        triangle.split()
            == Inertia {
                positive: 1,
                zero: 0,
                negative: 2,
            }
            && triangle.windings_past_the_hand()
                == vec![Rat::new(1.into(), 3.into()), Rat::new(2.into(), 3.into())],
        format!(
            "split {:?}, against the turn at {:?}",
            triangle.split(),
            triangle
                .windings_past_the_hand()
                .iter()
                .map(format_rat)
                .collect::<Vec<_>>()
        ),
    ));

    let twelve = winding_inertia(&cycle_adjacency(12).unwrap()).unwrap();
    print_passages("C_12 adjacency  (4 | n, so the hand is occupied)", &twelve);

    let eleven = winding_inertia(&cycle_adjacency(11).unwrap()).unwrap();
    print_passages("C_11 adjacency  (4 does not divide n)", &eleven);

    // =========================================================================================
    println!("\n\n=========================================================================");
    println!("  THE QUARTER-TURN LAW, SWEPT OVER BOTH HALVES OF `4 | n`");
    println!("=========================================================================");
    println!(
        "\n  Two independent routes. The EXACT RATIONAL one compares the winding k/n against 1/4\n  \
         and 3/4 and touches no algebra at all. The EXACT ALGEBRAIC one isolates 2cos(2*pi*k/n)\n  \
         by Sturm bisection on the Dickson polynomial and decides nullity by cyclotomic division.\n"
    );
    println!(
        "     n   4|n   split (p,z,q)   nulls at        against the turn at\n     \
         --------------------------------------------------------------------------"
    );
    let mut quarter_turn_agrees = true;
    let mut null_bearing = 0;
    let mut null_free = 0;
    let mut law_held = true;
    let quarter = Rat::new(BigInt::one(), BigInt::from(4));
    let three_quarters = Rat::new(BigInt::from(3), BigInt::from(4));
    for extent in 3..=16_usize {
        let reading = winding_inertia(&cycle_adjacency(extent).unwrap()).unwrap();
        let rational_route = quarter_turn_reading(extent).unwrap();
        let returns: Vec<PassageReturn> = reading
            .passages
            .iter()
            .map(|passage| passage.returns)
            .collect();
        quarter_turn_agrees &= returns == rational_route;
        for passage in &reading.passages {
            let expected = if passage.winding == quarter || passage.winding == three_quarters {
                PassageReturn::OnTheNullCone
            } else if quarter < passage.winding && passage.winding < three_quarters {
                PassageReturn::Handed(Hand::AgainstTheTurn)
            } else {
                PassageReturn::Handed(Hand::WithTheTurn)
            };
            law_held &= passage.returns == expected;
        }
        let nulls: Vec<String> = reading.null_windings().iter().map(format_rat).collect();
        if extent % 4 == 0 {
            null_bearing += usize::from(nulls.len() == 2);
        } else {
            null_free += usize::from(nulls.is_empty());
        }
        let split = reading.split();
        println!(
            "    {:>2}   {:>3}   ({:>2},{:>2},{:>2})        {:<14}  {:?}",
            extent,
            if extent % 4 == 0 { "yes" } else { "no" },
            split.positive,
            split.zero,
            split.negative,
            format!("{nulls:?}"),
            reading
                .windings_past_the_hand()
                .iter()
                .map(format_rat)
                .collect::<Vec<_>>()
        );
    }
    holds.push((
        "sign(lambda_k) < 0 exactly when 1/4 < k/n < 3/4, over n = 3..16",
        law_held,
        "every character of every cycle in the sweep".to_string(),
    ));
    holds.push((
        "the exact-rational quarter-turn route and the exact-algebraic character route agree",
        quarter_turn_agrees,
        "k/n against 1/4 and 3/4 versus Sturm isolation and cyclotomic division".to_string(),
    ));
    let divisible = (3..=16_usize).filter(|extent| extent % 4 == 0).count();
    let indivisible = (3..=16_usize).filter(|extent| extent % 4 != 0).count();
    holds.push((
        "the null directions appear EXACTLY when 4 | n -- both halves swept, neither can pass alone",
        null_bearing == divisible && null_free == indivisible && divisible > 0 && indivisible > 0,
        format!(
            "{null_bearing} of {divisible} cycles with 4 | n carry two nulls; \
             {null_free} of {indivisible} without carry none"
        ),
    ));

    // =========================================================================================
    println!("\n\n=========================================================================");
    println!("  TWO INDEPENDENT ROUTES TO ONE SPLIT");
    println!("=========================================================================");
    println!(
        "\n  The character route reads the symmetry. The elimination reads entries: it is never\n  \
         told n, never told k, and never shown the first row. To prove that, the elimination is\n  \
         then handed P^T C P for a NON-circulant P -- a form that no longer has the symmetry at\n  \
         all, and is refused by type as not circulant -- and it still returns the same split.\n"
    );
    let family: Vec<(&str, Vec<i64>)> = vec![
        ("C_3 adjacency", vec![0, 1, 1]),
        ("C_4 adjacency", vec![0, 1, 0, 1]),
        ("K_5 = C_5^2", vec![0, 1, 1, 1, 1]),
        ("L(C_6) laplacian", vec![2, -1, 0, 0, 0, -1]),
        ("Q(C_5) signless", vec![2, 1, 0, 0, 1]),
        ("identity", vec![1, 0, 0, 0, 0, 0]),
        ("negated identity", vec![-1, 0, 0, 0, 0, 0]),
        ("weighted (0,2,3,3,2)", vec![0, 2, 3, 3, 2]),
        ("mixed (1,-2,3,-4,3,-2)", vec![1, -2, 3, -4, 3, -2]),
        ("mixed n=8", vec![3, -1, 0, 2, -5, 2, 0, -1]),
        ("sparse n=12", vec![0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1]),
        ("the zero form", vec![0, 0, 0, 0]),
    ];
    println!(
        "     form                     characters     elimination    de-symmetrized    refused\n     \
         ----------------------------------------------------------------------------------"
    );
    let mut routes_agree = true;
    let mut transported_agree = true;
    let mut refused_count = 0;
    let mut nonzero_forms = 0;
    let mut nonzero_refused = 0;
    let mut saw_definite = false;
    let mut saw_indefinite = false;
    let mut saw_degenerate = false;
    let mut beyond_zero_one = 0;
    for (name, first_row) in &family {
        let form = circulant(first_row);
        let reading = winding_inertia(&form).unwrap();
        let by_elimination = inertia(&form.as_symmetric_form().unwrap());
        routes_agree &= reading.split() == by_elimination;
        saw_definite |=
            by_elimination.is_positive_definite() || by_elimination.is_negative_definite();
        saw_indefinite |= by_elimination.is_indefinite();
        saw_degenerate |= by_elimination.is_degenerate();
        beyond_zero_one += usize::from(first_row.iter().any(|entry| entry.abs() > 1));

        let transported = congruence(
            &form.as_symmetric_form().unwrap(),
            &scrambling_basis(first_row.len()),
        )
        .expect("the unitriangular basis is invertible");
        let refused = matches!(
            SymmetricCirculant::from_symmetric_form(&transported),
            Err(WindingError::NotCirculant { .. })
        );
        refused_count += usize::from(refused);
        if first_row.iter().any(|entry| *entry != 0) {
            nonzero_forms += 1;
            nonzero_refused += usize::from(refused);
        }
        let mut after = Inertia::default();
        for order in PivotOrder::ALL {
            after = holonic_engine::inertia::inertia_with_order(&transported, order);
            transported_agree &= after == reading.split();
        }
        let show = |reading: Inertia| {
            format!(
                "({},{},{})",
                reading.positive, reading.zero, reading.negative
            )
        };
        println!(
            "     {:<24} {:<14} {:<14} {:<17} {}",
            name,
            show(reading.split()),
            show(by_elimination),
            show(after),
            if refused { "yes" } else { "NO" }
        );
    }
    holds.push((
        "the character split equals the split the elimination finds",
        routes_agree,
        format!("{} forms", family.len()),
    ));
    holds.push((
        "the family carries definite, indefinite AND degenerate shapes, so it could disagree",
        saw_definite && saw_indefinite && saw_degenerate,
        format!(
            "definite {saw_definite}, indefinite {saw_indefinite}, degenerate {saw_degenerate}"
        ),
    ));
    // The zero form is the one place this check provably CANNOT fire: `P^T · 0 · P = 0` is still
    // circulant, so no basis destroys a symmetry there. Naming the exception is the point --
    // `CLAUDE.md` §8, a negative control's absence is evidence, not an unbuilt output.
    holds.push((
        "a congruence by a non-circulant basis destroys the symmetry of every form that has one",
        nonzero_forms > 0 && nonzero_refused == nonzero_forms && refused_count == nonzero_forms,
        format!(
            "{nonzero_refused} of {nonzero_forms} nonzero forms refused as not circulant; the zero form is the \
             one exception and it is necessary, since P^T . 0 . P = 0 is still circulant"
        ),
    ));
    holds.push((
        "the elimination still returns the named split after the symmetry is gone, under all four pivot orders",
        transported_agree,
        "so the elimination was never reading n or k".to_string(),
    ));
    holds.push((
        "circulants with entries beyond {0,1} are read, so the law is not a property of the adjacency fixture",
        beyond_zero_one >= 4,
        format!("{beyond_zero_one} of {} forms carry |c_j| > 1", family.len()),
    ));

    // =========================================================================================
    println!("\n\n=========================================================================");
    println!("  THE POLES");
    println!("=========================================================================");

    let identity = winding_inertia(&circulant(&[1, 0, 0, 0, 0, 0])).unwrap();
    print_passages(
        "the identity circulant  (every passage one hand)",
        &identity,
    );
    let negated = winding_inertia(&circulant(&[-1, 0, 0, 0, 0, 0])).unwrap();
    print_passages("the negated identity  (the other hand)", &negated);
    holds.push((
        "a circulant of one hand reports NO winding past the hand, and its negation reports NO winding with it",
        identity.windings_past_the_hand().is_empty()
            && identity.null_windings().is_empty()
            && negated.windings_of(Hand::WithTheTurn).is_empty()
            && negated.null_windings().is_empty()
            && negated.windings_past_the_hand().len() == 6,
        format!(
            "identity: {} past the hand; negated: {} with the turn",
            identity.windings_past_the_hand().len(),
            negated.windings_of(Hand::WithTheTurn).len()
        ),
    ));

    let zero = winding_inertia(&circulant(&[0, 0, 0, 0, 0])).unwrap();
    print_passages(
        "the zero circulant  (traversal returns nothing anywhere)",
        &zero,
    );
    holds.push((
        "the wholly-null pole returns nothing on every passage and no hand anywhere",
        zero.null_windings().len() == 5
            && zero.windings_past_the_hand().is_empty()
            && zero.windings_of(Hand::WithTheTurn).is_empty(),
        format!("{:?}", zero.split()),
    ));

    let laplacian = winding_inertia(&cycle_laplacian(8).unwrap()).unwrap();
    print_passages(
        "L(C_8), the cycle laplacian  (one null, at winding 0)",
        &laplacian,
    );
    holds.push((
        "the cycle laplacian returns nothing at exactly the zero-frequency passage",
        laplacian.null_windings() == vec![Rat::zero()]
            && laplacian.windings_past_the_hand().is_empty(),
        format!(
            "nulls {:?}, split {:?}",
            laplacian
                .null_windings()
                .iter()
                .map(format_rat)
                .collect::<Vec<_>>(),
            laplacian.split()
        ),
    ));

    // =========================================================================================
    println!("\n\n=========================================================================");
    println!("  NON-CYCLE CIRCULANTS, AND THE EXACT NULL WITNESS");
    println!("=========================================================================");
    println!(
        "\n  A null is proved, never approached. omega^k is a PRIMITIVE d-th root of unity for\n  \
         d = n/gcd(k,n), so its minimal polynomial over Q is the cyclotomic Phi_d, and\n  \
         lambda_k = f(omega^k) = 0 exactly when Phi_d divides f. That is one exact polynomial\n  \
         division, and Phi_d is the passage's own star polygon in lowest terms.\n"
    );
    let mut witnesses_verified = 0;
    let mut witnesses_seen = 0;
    for (name, first_row) in [
        ("weighted (0,2,3,3,2)", vec![0, 2, 3, 3, 2]),
        ("mixed (1,-2,3,-4,3,-2)", vec![1, -2, 3, -4, 3, -2]),
        ("mixed n=8", vec![3, -1, 0, 2, -5, 2, 0, -1]),
        ("sparse n=12", vec![0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1]),
    ] {
        let reading = winding_inertia(&circulant(&first_row)).unwrap();
        print_passages(name, &reading);
        for passage in &reading.passages {
            if let Some(witness) = &passage.null_witness {
                witnesses_seen += 1;
                witnesses_verified += usize::from(witness.verify(&reading.symbol));
            }
        }
    }
    holds.push((
        "every null carries a cyclotomic divisor that re-multiplies to the symbol exactly",
        witnesses_seen > 0 && witnesses_seen == witnesses_verified,
        format!("{witnesses_verified} of {witnesses_seen} witnesses re-multiplied to f"),
    ));

    // =========================================================================================
    println!("\n\n=========================================================================");
    println!("  NIVEN AND STURM: TWO ROUTES TO THE STAR TABLE");
    println!("=========================================================================");
    println!(
        "\n  2cos(2*pi*m/n) is rational exactly when n/gcd(m,n) is in {{1,2,3,4,6}}. Those entries\n  \
         are exact points; the rest are isolated by Sturm bisection -- and each rational value is\n  \
         checked to lie inside the interval Sturm independently isolated for that position.\n"
    );
    let table = StarTable::found(12).unwrap();
    println!("     m   n/gcd(m,n)   2cos(2*pi*m/12)                  route");
    for step in 0..=6_usize {
        let value = table.value(step).unwrap();
        println!(
            "    {:>2}   {:>10}   {:<30}   {}",
            step,
            12 / gcd(step, 12),
            if value.is_point() {
                format_rat(&value.lower)
            } else {
                format!(
                    "in [{}, {}]",
                    format_rat(&value.lower),
                    format_rat(&value.upper)
                )
            },
            if table.is_exact(step) {
                "Niven, exact rational"
            } else {
                "Sturm, isolated irrational"
            }
        );
    }
    let exact_positions: Vec<usize> = (0..=6).filter(|step| table.is_exact(*step)).collect();
    let irrational_positions: Vec<usize> = (0..=6).filter(|step| !table.is_exact(*step)).collect();
    holds.push((
        "both branches of the star table fire: Niven's rationals AND Sturm's irrationals",
        exact_positions == vec![0, 2, 3, 4, 6] && irrational_positions == vec![1, 5],
        format!("rational at {exact_positions:?}, irrational at {irrational_positions:?}"),
    ));

    // =========================================================================================
    println!("\n\n=========================================================================");
    println!("  GROWN MATERIAL: a circuit the machine grew, read on a cyclic receiver");
    println!("=========================================================================");
    println!(
        "\n  Not a fixture. `grown_cell` grows a Brent-Kung adder from a recursive cell with no N,\n  \
         no loop bound and no `if`; the 2-complex it founds carries the conduction arcs. The\n  \
         receiver is the declaration `net |-> net mod n`, and what it keeps is conduction counted\n  \
         by displacement class, in both orientations -- so the return is a symmetric circulant by\n  \
         construction and not by a repair.\n\n  \
         The net identifier is a SCHEDULE coordinate: `grown_cell` declares that two schedules\n  \
         produce the same circuit under different symbols. So this chart is receiver-relative and\n  \
         measurably so, and the frame is varied here rather than held fixed. What survives every\n  \
         frame is the claim under test: the character route and the elimination return one split.\n"
    );
    let cells = standard_cells();
    let mut grown_agree = true;
    let mut grown_beyond_zero_one = 0;
    let mut grown_charts = 0;
    let mut grown_indefinite = 0;
    let mut grown_past_the_hand = 0;
    let mut splits_by_extent: Vec<(usize, Vec<Inertia>)> = Vec::new();
    let mut printed = false;
    for extent in [5_usize, 7, 9, 11] {
        let mut splits = Vec::new();
        for schedule in Schedule::ALL {
            let growth = grow(&cells, "brent-kung-adder", &[8, 8, 1], schedule)
                .expect("the standard cells grow an eight-bit adder");
            let complex = found_complex(&growth, ComplexAperture::DIVISION)
                .expect("the growth founds its complex");
            let receiver = cyclic_receiver_of_growth(&complex, extent).unwrap();
            let reading = winding_inertia(&receiver).unwrap();
            let by_elimination = inertia(&receiver.as_symmetric_form().unwrap());
            grown_agree &= reading.split() == by_elimination;
            grown_charts += 1;
            grown_beyond_zero_one += usize::from(
                receiver
                    .first_row()
                    .iter()
                    .any(|entry| *entry > Rat::from_integer(BigInt::one())),
            );
            grown_indefinite += usize::from(reading.split().is_indefinite());
            grown_past_the_hand += usize::from(!reading.windings_past_the_hand().is_empty());
            if !printed {
                println!(
                    "\n  the growth: {} gates, {} instances, {} nets, depth {}, {} conduction arcs",
                    growth.gate_count(),
                    growth.instance_count(),
                    growth.net_count(),
                    growth.depth(),
                    complex.arcs.len()
                );
                print_passages(
                    &format!(
                        "grown Brent-Kung adder on a {extent}-fold cyclic receiver, schedule `{}`",
                        schedule.name()
                    ),
                    &reading,
                );
                printed = true;
            }
            splits.push(reading.split());
        }
        splits_by_extent.push((extent, splits));
    }
    println!("\n     receiver   instantiation   widest-first    deepest         frame moves");
    println!("     ---------------------------------------------------------------------");
    let mut frames_moved = 0;
    for (extent, splits) in &splits_by_extent {
        let moved = splits.windows(2).any(|pair| pair[0] != pair[1]);
        frames_moved += usize::from(moved);
        let show = |reading: &Inertia| {
            format!(
                "({},{},{})",
                reading.positive, reading.zero, reading.negative
            )
        };
        println!(
            "     n = {:<6} {:<15} {:<15} {:<15} {}",
            extent,
            show(&splits[0]),
            show(&splits[1]),
            show(&splits[2]),
            if moved { "yes" } else { "no" }
        );
    }
    holds.push((
        "on grown material the character route and the elimination still return one split",
        grown_agree && grown_charts == 12,
        format!("{grown_charts} grown charts, all agreeing"),
    ));
    holds.push((
        "the grown receiver carries entries beyond {0,1} -- real conduction, not a fixture",
        grown_beyond_zero_one == grown_charts,
        format!("{grown_beyond_zero_one} of {grown_charts} charts"),
    ));
    holds.push((
        "the law fires on grown material: both cones occupied, and passages named past the hand",
        grown_indefinite > 0 && grown_past_the_hand > 0,
        format!("{grown_indefinite} indefinite charts, {grown_past_the_hand} with a winding past the hand"),
    ));
    holds.push((
        "the frame really moves -- at least one grown chart differs across expansion schedules",
        frames_moved > 0,
        format!(
            "{frames_moved} of {} receiver extents moved with the schedule",
            splits_by_extent.len()
        ),
    ));

    // =========================================================================================
    println!("\n\n=========================================================================");
    println!("  REFUSALS");
    println!("=========================================================================");
    let not_circulant =
        SymmetricForm::from_integers(&[vec![1, 2, 0], vec![2, 5, 0], vec![0, 0, -3]]).unwrap();
    let refusal = SymmetricCirculant::from_symmetric_form(&not_circulant);
    println!("\n     a symmetric non-circulant form  ->  {refusal:?}");
    let asymmetric = SymmetricCirculant::from_integers(&[0, 1, 2, 0]);
    println!("     a circulant with c_1 != c_3     ->  {asymmetric:?}");
    let empty = SymmetricCirculant::from_integers(&[]);
    println!("     a circulant on no characters    ->  {empty:?}");
    holds.push((
        "a matrix that is not circulant is refused BY TYPE, naming the entry that breaks it",
        matches!(
            refusal,
            Err(WindingError::NotCirculant { row: 1, column: 0 })
        ) && matches!(
            asymmetric,
            Err(WindingError::NotReversalSymmetric { step: 1 })
        ) && matches!(empty, Err(WindingError::EmptyCirculant)),
        format!("{refusal:?} / {asymmetric:?} / {empty:?}"),
    ));

    // =========================================================================================
    println!("\n\nDECLARED CONTROLS");
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

fn gcd(mut left: usize, mut right: usize) -> usize {
    while right != 0 {
        let remainder = left % right;
        left = right;
        right = remainder;
    }
    left
}
