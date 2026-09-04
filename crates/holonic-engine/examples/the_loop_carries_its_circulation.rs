//! The loop carries its circulation, and closure is the only thing that can fail.
//!
//! `crates/holonic-engine/src/kelvin.rs` has **no library caller and no driver**. `pub mod kelvin;`
//! in `lib.rs` is the only mention of it in the tree, and two prose references — `parcel.rs:5` and
//! `analytic_field.rs:1331` — point at it without conducting through it. This file conducts through
//! it.
//!
//! `docs/canon/THE_HOLOBROCHOS_SPINE.md` §1 names five cuts a body can be at and says which one applies
//! is a **measurement**. `kelvin.rs` carries the `j != 0` cut literally: a material loop, moved by
//! the flow, whose circulation `Gamma = <c, v>` is conserved.
//!
//! ## What the module says it does, and what this driver holds it to
//!
//! The module's own doc names the tautology it had to avoid. With `v(t+1) = U v(t)`, the covector
//! transport `c(t+1) = (U^T)^-1 c(t)` preserves the pairing **identically, by associativity**. So
//! conservation of `Gamma` is a receipt that could not have come out otherwise, and `CLAUDE.md` §8
//! says such a receipt carries no evidence. This driver therefore states it as a control that
//! **cannot fail** and does not count it, and puts the weight on the three things the module says
//! it re-checks:
//!
//! 1. the carried loop is **still a loop** — `d^T c = 0` at every junction, re-checked every step;
//! 2. the loop **actually moved** — otherwise this is the fixed-probe case wearing a new name;
//! 3. a loop the existing fixed-probe machinery **must refuse** is admitted here.
//!
//! ## Declared apertures
//!
//! - **Carrier.** Exact `Rat` throughout. No float, no tolerance, no threshold appears below.
//! - **Incidence A — the theta graph.** Three parallel arcs `0, 1, 2` from junction `0` to junction
//!   `1`. Two junctions, so the cycle space is `3 - 2 + 1 = 2`-dimensional and there exist closed
//!   loops that are not the all-ones covector. On a simple cycle the cycle space is one-dimensional
//!   and every closed loop is left-fixed, which would make the whole movement vacuous.
//! - **Capacities `diag(1, 2, 3)` — deliberately unequal.** With equal capacities `U` is orthogonal,
//!   `(U^T)^-1 = U`, and the material transport coincides with the naive one; every check below
//!   would still pass and the falsifier would be vacuous. `CLAUDE.md` §8: *a gauge whose group acts
//!   trivially on the declared material is not a gauge.* Section 2 measures the orbit rather than
//!   asserting it.
//! - **Horizon.** Eight enacted events. The advection law refuses a repeated `EventId`, so each step
//!   carries its own.
//! - **Incidence B — three junctions.** Arcs `10, 11: j0 -> j1` and `12, 13: j1 -> j2`, capacities
//!   `diag(1, 2, 3, 4)`. Four arcs, three junctions, so the cycle space is `4 - 3 + 1 = 2` while the
//!   sum-zero hyperplane is `3`-dimensional. This is the aperture at which the module's own closure
//!   argument stops applying, and section 8 runs it.
//!
//! ```text
//! cargo run --release --example the_loop_carries_its_circulation
//! ```
//!
//! Exits non-zero if any declared control fails.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::analytic_field::{
    AnalyticCirculationProbeId, AnalyticFieldArcId, AnalyticFieldError, AnalyticFieldJunctionId,
    ExactAnalyticAdvectionEvent, ExactAnalyticAdvectionLaw, ExactAnalyticAdvectionStanding,
    ExactAnalyticCirculationProbe,
};
use holonic_engine::exact_linear::ExactRatMatrix;
use holonic_engine::kelvin::{
    ArcIncidence, KelvinError, MaterialLoop, read_fixed_step, read_material_step,
};
use holonic_engine::{EventId, ExactEventLaw};
use num_traits::Zero;
use relational_geometry::{Rat, format_rat, integer, rat};

fn arc(index: u64) -> AnalyticFieldArcId {
    AnalyticFieldArcId(index)
}

fn junction(index: u64) -> AnalyticFieldJunctionId {
    AnalyticFieldJunctionId(index)
}

// -------------------------------------------------------------------------------------------
// incidence A — the theta graph

fn theta_incidence() -> ArcIncidence {
    let (j0, j1) = (junction(0), junction(1));
    [(arc(0), (j0, j1)), (arc(1), (j0, j1)), (arc(2), (j0, j1))]
        .into_iter()
        .collect()
}

/// Capacity-skew (`w_i A_ij = -w_j A_ji`) with zero row sums, on capacities `diag(1, 2, 3)`.
fn theta_law() -> ExactAnalyticAdvectionLaw {
    let capacities: BTreeMap<AnalyticFieldArcId, Rat> = [
        (arc(0), integer(1)),
        (arc(1), integer(2)),
        (arc(2), integer(3)),
    ]
    .into_iter()
    .collect();
    let generator = ExactRatMatrix::new(vec![
        vec![Rat::zero(), integer(1), integer(-1)],
        vec![rat(-1, 2), Rat::zero(), rat(1, 2)],
        vec![rat(1, 3), rat(-1, 3), Rat::zero()],
    ])
    .expect("a square generator");
    ExactAnalyticAdvectionLaw::new(capacities, generator, integer(1), vec![])
        .expect("capacity-skew with zero row sums passes both upstream gates")
}

/// The same incidence with **equal** capacities, kept only to measure the gauge orbit.
fn equal_capacity_law() -> ExactAnalyticAdvectionLaw {
    let capacities: BTreeMap<AnalyticFieldArcId, Rat> = [
        (arc(0), integer(1)),
        (arc(1), integer(1)),
        (arc(2), integer(1)),
    ]
    .into_iter()
    .collect();
    let generator = ExactRatMatrix::new(vec![
        vec![Rat::zero(), integer(1), integer(-1)],
        vec![integer(-1), Rat::zero(), integer(1)],
        vec![integer(1), integer(-1), Rat::zero()],
    ])
    .expect("a square generator");
    ExactAnalyticAdvectionLaw::new(capacities, generator, integer(1), vec![])
        .expect("antisymmetric with zero row sums passes both upstream gates")
}

// -------------------------------------------------------------------------------------------
// incidence B — three junctions, where the closure argument stops applying

fn chain_incidence() -> ArcIncidence {
    let (j0, j1, j2) = (junction(0), junction(1), junction(2));
    [
        (arc(10), (j0, j1)),
        (arc(11), (j0, j1)),
        (arc(12), (j1, j2)),
        (arc(13), (j1, j2)),
    ]
    .into_iter()
    .collect()
}

/// `A_ij = S_ij / w_i` for an antisymmetric integer `S` whose every row sums to zero, on
/// `diag(1, 2, 3, 4)`. Capacity-skew and divergence-free by construction, so it passes the same two
/// upstream gates the theta law does.
fn chain_law() -> ExactAnalyticAdvectionLaw {
    let capacities: BTreeMap<AnalyticFieldArcId, Rat> = [
        (arc(10), integer(1)),
        (arc(11), integer(2)),
        (arc(12), integer(3)),
        (arc(13), integer(4)),
    ]
    .into_iter()
    .collect();
    let skew: [[i64; 4]; 4] = [[0, 1, 1, -2], [-1, 0, 3, -2], [-1, -3, 0, 4], [2, 2, -4, 0]];
    let weights = [1i64, 2, 3, 4];
    let generator = ExactRatMatrix::new(
        (0..4)
            .map(|row| {
                (0..4)
                    .map(|column| rat(skew[row][column], weights[row]))
                    .collect()
            })
            .collect(),
    )
    .expect("a square generator");
    ExactAnalyticAdvectionLaw::new(capacities, generator, integer(1), vec![])
        .expect("capacity-skew with zero row sums passes both upstream gates")
}

// -------------------------------------------------------------------------------------------
// rendering

fn print_matrix(indent: &str, label: &str, matrix: &ExactRatMatrix) {
    println!("{indent}{label}");
    for row in 0..matrix.rows() {
        let entries: Vec<String> = (0..matrix.columns())
            .map(|column| {
                format!(
                    "{:>10}",
                    format_rat(matrix.get(row, column).expect("inside the matrix"))
                )
            })
            .collect();
        println!("{indent}  [ {} ]", entries.join("  "));
    }
}

fn render_coefficients(
    coefficients: &BTreeMap<AnalyticFieldArcId, Rat>,
    order: &[AnalyticFieldArcId],
) -> String {
    order
        .iter()
        .map(|arc| match coefficients.get(arc) {
            Some(value) => format!("{:>12}", format_rat(value)),
            None => format!("{:>12}", "."),
        })
        .collect::<Vec<_>>()
        .join(" ")
}

fn render_standing(
    standing: &ExactAnalyticAdvectionStanding,
    order: &[AnalyticFieldArcId],
) -> String {
    render_coefficients(&standing.values, order)
}

fn standing_of(
    law: &ExactAnalyticAdvectionLaw,
    values: &[(u64, i64)],
) -> ExactAnalyticAdvectionStanding {
    law.initial_standing(
        values
            .iter()
            .map(|(index, value)| (arc(*index), integer(*value)))
            .collect(),
    )
    .expect("the declared population matches the law's arcs")
}

fn step(
    law: &ExactAnalyticAdvectionLaw,
    before: &ExactAnalyticAdvectionStanding,
    event: u64,
) -> ExactAnalyticAdvectionStanding {
    law.enact(
        before,
        &ExactAnalyticAdvectionEvent {
            event: EventId(event),
        },
    )
    .expect("the conservative successor enacts")
    .standing_after
}

fn junction_residuals(
    arcs: &ArcIncidence,
    coefficients: &BTreeMap<AnalyticFieldArcId, Rat>,
) -> BTreeMap<AnalyticFieldJunctionId, Rat> {
    let mut boundary = BTreeMap::<AnalyticFieldJunctionId, Rat>::new();
    for (arc_id, coefficient) in coefficients {
        let (from, to) = arcs.get(arc_id).expect("the arc is in the declared field");
        *boundary.entry(*from).or_default() -= coefficient;
        *boundary.entry(*to).or_default() += coefficient;
    }
    boundary
}

fn main() {
    println!("THE LOOP CARRIES ITS CIRCULATION");
    println!("================================");
    println!("truth_status=established-bounded");
    println!("evidence=computational-witness");
    println!("law=the circulation of a MATERIAL loop is conserved; what can fail is its closure");
    println!("organ=crates/holonic-engine/src/kelvin.rs   (zero library callers, zero drivers)");

    let mut holds: Vec<(&str, bool, String)> = Vec::new();

    let arcs = theta_incidence();
    let law = theta_law();
    let order = law.arc_order().to_vec();

    // ===========================================================================================
    println!("\n\n1. THE DECLARED APERTURE, AND THE OPERATORS IT FIXES");
    println!("---------------------------------------------------");
    println!("  incidence A: theta graph, arcs 0,1,2 all running junction 0 -> junction 1");
    println!("    |E| = 3, |V| = 2, cycle space dimension 3 - 2 + 1 = 2");
    println!("    closedness on this incidence is exactly `c0 + c1 + c2 = 0`");
    println!("  capacities  Omega = diag(1, 2, 3)");
    println!("  interval    1");
    println!(
        "  arc order   {:?}",
        order.iter().map(|arc| arc.0).collect::<Vec<_>>()
    );
    print_matrix(
        "  ",
        "successor U (exact Cayley transform of the generator)",
        law.successor(),
    );
    let inverse_transpose = law
        .successor()
        .transpose()
        .and_then(|transposed| transposed.inverse())
        .expect("the successor is invertible by construction");
    print_matrix(
        "  ",
        "material covector transport (U^T)^-1",
        &inverse_transpose,
    );

    let ones = vec![integer(1); 3];
    let divergence_free = law.successor().apply(&ones).expect("square") == ones;
    println!(
        "\n  the advection law's own certificate, re-read here:  U . 1 = 1  ->  {divergence_free}"
    );
    println!("  that is incompressibility, and it is what makes the SUM of a carried covector");
    println!("  invariant:  1^T (U^T)^-1 c = (U^-1 1)^T c = 1^T c.");

    // ===========================================================================================
    println!("\n\n2. CONTROL — DOES THE MATERIAL SEPARATE THE TWO TRANSPORTS AT ALL?");
    println!("------------------------------------------------------------------");
    println!("  A gauge whose group acts trivially on the declared material is not a gauge. The");
    println!(
        "  two transports here are `U` (naive) and `(U^T)^-1` (material). On equal capacities"
    );
    println!("  they COLLAPSE, and every reading below would pass without testing anything.");

    let equal = equal_capacity_law();
    let equal_inverse_transpose = equal
        .successor()
        .transpose()
        .and_then(|transposed| transposed.inverse())
        .expect("invertible");
    let collapsed = &equal_inverse_transpose == equal.successor();
    let separated = &inverse_transpose != law.successor();
    print_matrix("  ", "equal capacities: U", equal.successor());
    print_matrix("  ", "equal capacities: (U^T)^-1", &equal_inverse_transpose);
    println!("\n  equal capacities collapse the two transports : {collapsed}");
    println!("  unequal capacities separate them             : {separated}");
    holds.push((
        "the declared material separates the naive and material transports (the gauge acts)",
        collapsed && separated,
        format!("equal-capacity collapse {collapsed}, unequal-capacity separation {separated}"),
    ));

    // ===========================================================================================
    println!("\n\n3. REFUSALS — WHAT `MaterialLoop::found` WILL NOT ADMIT");
    println!("-------------------------------------------------------");
    let open_chain =
        MaterialLoop::found(&arcs, "open", [(arc(0), integer(1))].into_iter().collect());
    let empty = MaterialLoop::found(&arcs, "empty", BTreeMap::new());
    let outside = MaterialLoop::found(
        &arcs,
        "outside",
        [(arc(97), integer(1)), (arc(98), integer(-1))]
            .into_iter()
            .collect(),
    );
    println!("  a single arc, boundary -1 at j0 and +1 at j1   ->  {open_chain:?}");
    println!("  no arcs at all                                  ->  {empty:?}");
    println!("  arcs 97, 98, which the field does not carry     ->  {outside:?}");
    holds.push((
        "a covector whose junction boundary does not vanish is refused by name",
        matches!(open_chain, Err(KelvinError::LoopNotClosed))
            && matches!(empty, Err(KelvinError::EmptyLoop))
            && matches!(outside, Err(KelvinError::ArcOutsideField(_))),
        format!("{open_chain:?} / {empty:?} / {outside:?}"),
    ));

    // ===========================================================================================
    println!("\n\n4. THE LOOP THE EXISTING MACHINERY MUST REFUSE");
    println!("----------------------------------------------");
    println!("  `ExactAnalyticAdvectionLaw` admits a circulation probe only when it is a LEFT");
    println!("  EIGENVECTOR of the successor, and refuses anything else at construction with");
    println!("  `NoninvariantCirculationProbe`. On this fixture the two admissibility conditions");
    println!("  — closed, and left-fixed — have only the zero covector in common, and both halves");
    println!("  are exhibited rather than argued.");

    let theta_loop: BTreeMap<AnalyticFieldArcId, Rat> =
        [(arc(0), integer(1)), (arc(1), integer(-1))]
            .into_iter()
            .collect();
    let probe_refusal = ExactAnalyticAdvectionLaw::new(
        [
            (arc(0), integer(1)),
            (arc(1), integer(2)),
            (arc(2), integer(3)),
        ]
        .into_iter()
        .collect(),
        ExactRatMatrix::new(vec![
            vec![Rat::zero(), integer(1), integer(-1)],
            vec![rat(-1, 2), Rat::zero(), rat(1, 2)],
            vec![rat(1, 3), rat(-1, 3), Rat::zero()],
        ])
        .expect("a square generator"),
        integer(1),
        vec![ExactAnalyticCirculationProbe {
            id: AnalyticCirculationProbeId(1),
            name: "theta".to_owned(),
            coefficients: theta_loop.clone(),
        }],
    );
    println!(
        "\n  declaring c = (1, -1, 0) as a FIXED probe  ->  {:?}",
        probe_refusal.as_ref().err()
    );

    // The one direction the fixed-probe gate does admit: Omega . 1 = (1, 2, 3).
    let fixed_covector = vec![integer(1), integer(2), integer(3)];
    let transported = law
        .successor()
        .transpose()
        .expect("square")
        .apply(&fixed_covector)
        .expect("square");
    let is_left_fixed = transported == fixed_covector;
    let admitted_but_open = MaterialLoop::found(
        &arcs,
        "omega-ones",
        order
            .iter()
            .zip(&fixed_covector)
            .map(|(arc, value)| (*arc, value.clone()))
            .collect(),
    );
    println!(
        "  the left-fixed direction is Omega . 1 = (1, 2, 3):  U^T c = c  ->  {is_left_fixed}"
    );
    println!("  and that covector founds as a material loop     ->  {admitted_but_open:?}");
    println!("  its coefficients sum to 6, so it is not closed.");
    println!();
    println!("  And the left-fixed SPACE is exactly that one line, computed rather than asserted.");
    println!(
        "  U^T c = c  <=>  Omega^-1 c is in ker A, because U is Omega-orthogonal with U.1 = 1."
    );
    println!("  A . 1 = 0 gives rank A <= 2; one nonvanishing 2x2 minor gives rank A >= 2. So");
    println!(
        "  dim ker A = 1, ker A = span{{1}}, and the left-fixed covectors are span{{Omega . 1}}."
    );
    let generator = ExactRatMatrix::new(vec![
        vec![Rat::zero(), integer(1), integer(-1)],
        vec![rat(-1, 2), Rat::zero(), rat(1, 2)],
        vec![rat(1, 3), rat(-1, 3), Rat::zero()],
    ])
    .expect("a square generator");
    let minor = generator.get(0, 0).expect("in range") * generator.get(1, 1).expect("in range")
        - generator.get(0, 1).expect("in range") * generator.get(1, 0).expect("in range");
    let generator_annihilates_ones = generator
        .apply(&vec![integer(1); 3])
        .expect("square")
        .iter()
        .all(Rat::is_zero);
    println!(
        "    A . 1 = 0 : {generator_annihilates_ones}      minor of rows 0,1 and columns 0,1 = {}  (nonzero: {})",
        format_rat(&minor),
        !minor.is_zero()
    );
    println!(
        "  Every nonzero covector on that line has coefficient sum 6k != 0, so the left-fixed"
    );
    println!("  line meets the closed subspace only at zero:");
    println!("  ON THIS FIXTURE THE FIXED-PROBE APPARATUS CAN CERTIFY NO CIRCULATION AT ALL.");
    holds.push((
        "a closed loop is refused as a fixed probe, and the one admitted probe is not closed",
        matches!(
            probe_refusal.as_ref().err(),
            Some(AnalyticFieldError::NoninvariantCirculationProbe(_))
        ) && is_left_fixed
            && matches!(admitted_but_open, Err(KelvinError::LoopNotClosed)),
        format!(
            "probe refusal {:?}; left-fixed {is_left_fixed}; that covector as a loop {admitted_but_open:?}",
            probe_refusal.as_ref().err()
        ),
    ));
    holds.push((
        "the left-fixed space is EXACTLY one line, so no closed loop anywhere is a lawful fixed probe",
        generator_annihilates_ones && !minor.is_zero() && is_left_fixed,
        format!(
            "rank A = 2 exactly: A.1 = 0 and the (0,1)x(0,1) minor is {}",
            format_rat(&minor)
        ),
    ));

    // ===========================================================================================
    println!("\n\n5. THE TWO READINGS OF ONE LOOP, ON ONE STEP");
    println!("--------------------------------------------");
    let material = MaterialLoop::found(&arcs, "theta", theta_loop.clone())
        .expect("sum zero is closed on the theta graph");
    let before = standing_of(&law, &[(0, 5), (1, 2), (2, -1)]);
    let after = step(&law, &before, 1);

    println!(
        "  arcs                    {}",
        order
            .iter()
            .map(|arc| format!("{:>12}", format!("arc {}", arc.0)))
            .collect::<Vec<_>>()
            .join(" ")
    );
    println!(
        "  field before            {}",
        render_standing(&before, &order)
    );
    println!(
        "  field after             {}",
        render_standing(&after, &order)
    );
    println!(
        "  loop c(0)               {}",
        render_coefficients(material.coefficients(), &order)
    );

    let held = read_fixed_step(&material, &before, &after);
    let (carried, receipt) = read_material_step(&arcs, &law, &material, &before, &after)
        .expect("the carried loop closes");
    println!(
        "  loop c(1) = (U^T)^-1 c  {}",
        render_coefficients(carried.coefficients(), &order)
    );
    println!(
        "\n  HELD FIXED     Gamma {} -> {}   residual {}   loop_moved {}   field_moved {}",
        format_rat(&held.before),
        format_rat(&held.after),
        format_rat(&held.residual),
        held.loop_moved,
        held.field_moved
    );
    println!(
        "  CARRIED        Gamma {} -> {}   residual {}   loop_moved {}   field_moved {}",
        format_rat(&receipt.before),
        format_rat(&receipt.after),
        format_rat(&receipt.residual),
        receipt.loop_moved,
        receipt.field_moved
    );
    println!(
        "\n  The conserved residual is NOT the evidence. <c(t+1), v(t+1)> = <c(t), v(t)> is an"
    );
    println!(
        "  identity in `(U^T)^-1` and could not have come out otherwise; it is stated here and"
    );
    println!("  not counted. What is evidence is that the held reading MOVED, so the two readings");
    println!("  are distinguishable on this material at all.");
    holds.push((
        "held fixed, this loop's circulation is NOT conserved — a nonzero control",
        !held.residual.is_zero() && held.field_moved,
        format!("held residual {}", format_rat(&held.residual)),
    ));
    holds.push((
        "carried materially, the same loop moved and its circulation did not",
        receipt.loop_moved
            && receipt.field_moved
            && receipt.conserved()
            && held.after != receipt.after,
        format!(
            "carried residual {}, held after {} against carried after {}",
            format_rat(&receipt.residual),
            format_rat(&held.after),
            format_rat(&receipt.after)
        ),
    ));

    // ===========================================================================================
    println!("\n\n6. THE ARTIFACT — EIGHT STEPS, EVERYTHING MOVING BUT GAMMA");
    println!("----------------------------------------------------------");
    let mut material = MaterialLoop::found(&arcs, "theta", theta_loop.clone()).expect("closed");
    let mut field = standing_of(&law, &[(0, 5), (1, 2), (2, -1)]);
    let founding = material.circulation(&field);
    println!(
        "  founding Gamma = <c(0), v(0)> = {}",
        format_rat(&founding)
    );
    println!(
        "\n  {:>4}  {:^38}  {:^38}  {:>8}  {:>10}",
        "step", "loop c(t)", "field v(t)", "Gamma", "residual"
    );
    println!(
        "  {:>4}  {}  {}  {:>8}  {:>10}",
        0,
        render_coefficients(material.coefficients(), &order),
        render_standing(&field, &order),
        format_rat(&founding),
        "-"
    );

    let mut loop_positions = BTreeSet::new();
    let mut field_positions = BTreeSet::new();
    let mut every_step_conserved = true;
    let mut every_step_moved = true;
    let mut bit_identical = true;
    let mut closure_held = true;
    loop_positions.insert(render_coefficients(material.coefficients(), &order));
    field_positions.insert(render_standing(&field, &order));

    for tick in 1..=8u64 {
        let next = step(&law, &field, tick);
        let (advanced, receipt) = read_material_step(&arcs, &law, &material, &field, &next)
            .expect("the carried loop stays closed on the theta incidence");
        let residuals = junction_residuals(&arcs, advanced.coefficients());
        closure_held &= residuals.values().all(Rat::is_zero);
        every_step_conserved &= receipt.conserved();
        every_step_moved &= receipt.loop_moved && receipt.field_moved;
        bit_identical &= receipt.after == founding;
        println!(
            "  {:>4}  {}  {}  {:>8}  {:>10}",
            tick,
            render_coefficients(advanced.coefficients(), &order),
            render_standing(&next, &order),
            format_rat(&receipt.after),
            format_rat(&receipt.residual)
        );
        loop_positions.insert(render_coefficients(advanced.coefficients(), &order));
        field_positions.insert(render_standing(&next, &order));
        material = advanced;
        field = next;
    }
    println!(
        "\n  distinct loop positions {}   distinct field positions {}   carried_steps {}",
        loop_positions.len(),
        field_positions.len(),
        material.carried_steps
    );
    println!(
        "  closure re-checked at every junction after every step, all residuals zero: {closure_held}"
    );
    holds.push((
        "the loop and the field both occupied more than one position over the horizon",
        loop_positions.len() > 1 && field_positions.len() > 1 && every_step_moved,
        format!(
            "{} loop positions, {} field positions over 8 steps",
            loop_positions.len(),
            field_positions.len()
        ),
    ));
    holds.push((
        "Gamma is bit-identical to its founding value at every step, not merely stationary",
        bit_identical && every_step_conserved && closure_held,
        format!(
            "founding Gamma {} held for 8 steps; closure held {closure_held}",
            format_rat(&founding)
        ),
    ));

    // ===========================================================================================
    println!("\n\n7. THE FALSIFIER — TRANSPORT THE LOOP THE WRONG WAY");
    println!("---------------------------------------------------");
    println!("  If Gamma were conserved by the pairing rather than by the transport, carrying the");
    println!("  loop by `U` instead of `(U^T)^-1` would leave it alone. It does not.");
    let founding_loop = MaterialLoop::found(&arcs, "theta", theta_loop.clone()).expect("closed");
    let before = standing_of(&law, &[(0, 5), (1, 2), (2, -1)]);
    let after = step(&law, &before, 1);
    let vector: Vec<Rat> = order
        .iter()
        .map(|arc| {
            founding_loop
                .coefficients()
                .get(arc)
                .cloned()
                .unwrap_or_else(Rat::zero)
        })
        .collect();
    let wrong = law.successor().apply(&vector).expect("square");
    let wrong_gamma: Rat = order
        .iter()
        .zip(&wrong)
        .map(|(arc, coefficient)| {
            coefficient.clone() * after.values.get(arc).cloned().unwrap_or_else(Rat::zero)
        })
        .sum();
    let right_gamma = founding_loop.circulation(&before);
    println!(
        "  loop carried by U       {}",
        wrong
            .iter()
            .map(|value| format!("{:>12}", format_rat(value)))
            .collect::<Vec<_>>()
            .join(" ")
    );
    println!(
        "  Gamma under U           {}      Gamma under (U^T)^-1   {}",
        format_rat(&wrong_gamma),
        format_rat(&right_gamma)
    );
    holds.push((
        "the wrong transport moves Gamma, so the conservation is a property of the transport",
        wrong_gamma != right_gamma,
        format!(
            "wrong {} against founding {}",
            format_rat(&wrong_gamma),
            format_rat(&right_gamma)
        ),
    ));

    // ===========================================================================================
    println!("\n\n8. THE WIDER APERTURE — WHERE THE CLOSURE ARGUMENT STOPS APPLYING");
    println!("-----------------------------------------------------------------");
    println!("  `kelvin.rs`'s own explanation of why a carried loop stays closed is:");
    println!("      1^T (U^T)^-1 c = (U^-1 1)^T c = 1^T c,  because U . 1 = 1");
    println!(
        "  That preserves the TOTAL SUM of the covector. On the theta graph closedness IS the"
    );
    println!("  vanishing of that sum, so the argument closes. It does not close in general: for");
    println!(
        "  |V| junctions the cycle space has dimension |E| - |V| + 1, and only at |V| = 2 does"
    );
    println!("  it fill the sum-zero hyperplane.");
    println!();
    println!("  incidence B: arcs 10,11: j0 -> j1 and arcs 12,13: j1 -> j2");
    println!("    |E| = 4, |V| = 3, cycle space dimension 2, sum-zero hyperplane dimension 3");
    println!("    closedness is `c10 + c11 = 0` AND `c12 + c13 = 0`, not one equation but two");

    let chain_arcs = chain_incidence();
    let chain = chain_law();
    let chain_order = chain.arc_order().to_vec();
    print_matrix("  ", "successor U on incidence B", chain.successor());
    let chain_ones = vec![integer(1); 4];
    println!(
        "  U . 1 = 1 on incidence B too: {}",
        chain.successor().apply(&chain_ones).expect("square") == chain_ones
    );

    let mut broke = Vec::new();
    let mut sums_preserved = true;
    let mut broken_junctions = 0usize;
    let mut junctions_read = 0usize;
    for (name, coefficients) in [
        (
            "c = (1, -1, 0, 0)",
            vec![integer(1), integer(-1), Rat::zero(), Rat::zero()],
        ),
        (
            "c = (0, 0, 1, -1)",
            vec![Rat::zero(), Rat::zero(), integer(1), integer(-1)],
        ),
        (
            "c = (1, -1, 2, -2)",
            vec![integer(1), integer(-1), integer(2), integer(-2)],
        ),
    ] {
        let founded = MaterialLoop::found(
            &chain_arcs,
            name,
            chain_order
                .iter()
                .zip(&coefficients)
                .filter(|(_, value)| !value.is_zero())
                .map(|(arc, value)| (*arc, value.clone()))
                .collect(),
        )
        .expect("the declared covector is closed on incidence B");
        let inverse = chain
            .successor()
            .transpose()
            .and_then(|transposed| transposed.inverse())
            .expect("invertible");
        let carried_values = inverse.apply(&coefficients).expect("square");
        let carried_map: BTreeMap<AnalyticFieldArcId, Rat> = chain_order
            .iter()
            .zip(&carried_values)
            .map(|(arc, value)| (*arc, value.clone()))
            .collect();
        let residuals = junction_residuals(&chain_arcs, &carried_map);
        let carried_sum: Rat = carried_values.iter().cloned().sum();
        sums_preserved &= carried_sum.is_zero();
        let outcome = founded.carried(&chain_arcs, &chain);
        println!(
            "\n  {name}\n    carried  {}",
            render_coefficients(&carried_map, &chain_order)
        );
        println!(
            "    total sum after carrying: {}   (the module's argument preserves exactly this)",
            format_rat(&carried_sum)
        );
        for (junction, residual) in &residuals {
            junctions_read += 1;
            if !residual.is_zero() {
                broken_junctions += 1;
            }
            println!(
                "    junction {:>2} boundary residual: {}",
                junction.0,
                format_rat(residual)
            );
        }
        println!("    kelvin.rs returns: {:?}", outcome.as_ref().err());
        broke.push(matches!(
            outcome.as_ref().err(),
            Some(KelvinError::CarriedLoopNotClosed { .. })
        ));
    }
    println!(
        "\n  So the third thing the module says it re-checks is the one that fires. The pairing"
    );
    println!("  <c, v> is still conserved on incidence B — that identity does not care about the");
    println!("  incidence — but the carried covector is no longer a LOOP, so what is conserved is");
    println!("  not a circulation. The refusal is the honest return and the module makes it.");
    holds.push((
        "at three junctions the carried covector breaks closure and is refused by name",
        broke.iter().all(|fired| *fired),
        format!(
            "{} of {} declared closed covectors returned CarriedLoopNotClosed",
            broke.iter().filter(|fired| **fired).count(),
            broke.len()
        ),
    ));
    holds.push((
        "the quantity the module's argument DOES preserve is preserved, so the break is per-junction",
        sums_preserved && broken_junctions > 0,
        format!(
            "every carried covector on incidence B still sums to zero, while {broken_junctions} of \
             {junctions_read} junction readings do not vanish"
        ),
    ));

    // ===========================================================================================
    println!("\n\n9. THE TWO REFUSALS THAT CANNOT BE REACHED THROUGH THE PUBLIC CONSTRUCTOR");
    println!("--------------------------------------------------------------------------");
    println!("  `KelvinError` carries six variants. Four are exercised above. The other two are");
    println!(
        "  unreachable so long as the loop is carried against an `ExactAnalyticAdvectionLaw`:"
    );
    println!();
    println!(
        "    LoopCollapsed  needs (U^T)^-1 c = 0 for c != 0. `ExactAnalyticAdvectionLaw::new`"
    );
    println!("                   already inverted the successor at construction, so the transport");
    println!("                   is a bijection and no nonzero loop can collapse.");
    println!("    Linear         needs the transpose or the inverse to fail. Same reason.");
    println!();
    println!("  This is reported, not counted as a control: an absence is a measurement of the");
    println!("  reachable set and it decays. Both would become reachable if `carried` were ever");
    println!("  pointed at a successor that did not come through that constructor, and the module");
    println!("  takes `&ExactAnalyticAdvectionLaw`, so today it cannot be.");

    // ===========================================================================================
    println!("\n\nBOUNDS");
    println!("------");
    println!(
        "  - This is not Navier-Stokes, not existence, not smoothness, not viscosity, and not"
    );
    println!("    a fluid solver. It is one exact finite conservative advection chart with a");
    println!("    covector carried on it. The cpu module's bound stands unsoftened.");
    println!("  - `Gamma` conservation is an ALGEBRAIC IDENTITY here, not a measurement. It is");
    println!("    stated and not counted. Nothing below it establishes Kelvin's theorem in any");
    println!("    setting where the flow is not a declared linear successor.");
    println!("  - The horizon is eight steps on one initial field on one incidence. Nothing is");
    println!("    established about longer horizons, other fields, or other incidences.");
    println!(
        "  - Section 8 exhibits ONE three-junction incidence on which closure breaks. It does"
    );
    println!("    not establish that closure breaks on every incidence with |V| > 2, and it does");
    println!(
        "    not exhibit a |V| > 2 incidence on which a nontrivial loop survives — whether one"
    );
    println!("    exists for this generator family is not decided here.");
    println!("  - `read_material_step` does not check that `after_standing` is the transport of");
    println!("    `before_standing`; this driver supplies the transport and the caller owns that");
    println!("    obligation. A caller that supplied an unrelated pair would get a residual that");
    println!("    means nothing, and no refusal.");
    println!("  - No claim is made about any Millennium problem, about turbulence, or about the");
    println!("    continuum limit of any of this.");

    // ===========================================================================================
    println!("\n\nDECLARED CONTROLS");
    println!("-----------------");
    let mut failed = 0;
    for (claim, verdict, evidence) in &holds {
        if *verdict {
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
