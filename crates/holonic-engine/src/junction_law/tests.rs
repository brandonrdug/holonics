//! Tests for the junction law. Every value is exact; no float decides anything.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::{One, Zero};
use relational_geometry::Rat;

use super::*;
use crate::algebraic::CausalCellId;
use crate::hodge_receiver::{BoundaryCondition, HodgeOperator, MetricDeclaration};
use crate::quantity::BaseUnits;

fn rat(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

fn integer(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

fn vector(values: &[i64]) -> Vec<Rat> {
    values.iter().map(|value| integer(*value)).collect()
}

// ---------------------------------------------------------------------------------------------
// 1. the joint in the tower
// ---------------------------------------------------------------------------------------------

/// Lean: `join_is_exactly_the_compatible_pairs`.
#[test]
fn the_joint_of_two_charts_is_the_pullback_of_compatible_pairs() {
    let left = ["a".to_owned(), "b".to_owned(), "a".to_owned()];
    let right = ["a".to_owned(), "c".to_owned()];
    let joint = Joint::pullback(&left, &right, 2).expect("the populations are small");
    match &joint {
        Joint::Pullback { pairs, valence } => {
            // Both occurrences whose target is `a` join with the one source at `a`, and nothing
            // else joins: the pullback is exactly the compatible pairs, and it keeps *both*
            // occurrences rather than the fact that one exists.
            assert_eq!(pairs.len(), 2);
            assert!(pairs.contains(&(0, 0, "a".to_owned())));
            assert!(pairs.contains(&(2, 0, "a".to_owned())));
            assert_eq!(*valence, 2);
        }
        other => panic!("the pullback is nonempty here: {other:?}"),
    }
    assert!(!joint.is_junction(), "valence two is a serial join");
}

/// Lean: `noSharedBoundary_isEmpty_join`, and the span-level
/// `Transport/WorldTube.lean::openGap_has_no_joined_occurrence`.
#[test]
fn an_open_gap_carries_no_joint() {
    let left = ["a".to_owned()];
    let right = ["b".to_owned()];
    let joint = Joint::pullback(&left, &right, 2).expect("the populations are small");
    assert!(matches!(joint, Joint::OpenGap { .. }));
    assert_eq!(joint.valence(), None, "a gap has no valence to report");
    assert!(!joint.is_junction());
}

/// Lean: `IsJunction`, `serial_station_is_not_a_junction`, `trivalent_station_is_a_junction`.
#[test]
fn a_trivalent_station_is_a_junction_and_a_serial_one_is_not() {
    let faces = ["x".to_owned()];
    assert!(!Joint::pullback(&faces, &faces, 2).expect("small").is_junction());
    assert!(Joint::pullback(&faces, &faces, 3).expect("small").is_junction());
    assert!(Joint::pullback(&faces, &faces, 7).expect("small").is_junction());
    assert!(matches!(
        Joint::pullback(&[], &faces, 3),
        Err(JunctionRefusal::EmptyInterface)
    ));
}

// ---------------------------------------------------------------------------------------------
// 2. the law on a circuit
// ---------------------------------------------------------------------------------------------

/// Four nodes, five branches, unit conductance: two independent loops.
fn two_loop_network() -> ResistiveNetwork {
    let branches = [
        (0usize, 1usize, Rat::one()),
        (1, 2, Rat::one()),
        (2, 3, Rat::one()),
        (3, 0, Rat::one()),
        (0, 2, Rat::one()),
    ];
    ResistiveNetwork::declare("test|two-loop", 4, &branches).expect("the network stands")
}

#[test]
fn a_two_loop_network_solves_exactly_and_its_currents_are_rational() {
    let network = two_loop_network();
    let injection = vec![Rat::one(), Rat::zero(), -Rat::one(), Rat::zero()];
    let solution = network.solve(&injection).expect("the solve returns");
    assert!(solution.solved());
    assert_eq!(solution.gauge.len(), 1, "the gauge is the constants");

    // The currents are the same for every member of the fibre: the gauge is annihilated by the
    // coboundary, which is checked here rather than asserted.
    let coboundary = network.operator().coboundary(0).expect("the coboundary");
    for direction in &solution.gauge {
        let drop = coboundary.apply(direction).expect("applies");
        assert!(drop.iter().all(Zero::is_zero), "the gauge carries no drop");
    }

    // KCL: the divergence of the drop cochain is the declared injection, exactly.
    let divergence = network
        .operator()
        .codifferential(0)
        .expect("the codifferential")
        .apply(&solution.drops)
        .expect("applies");
    assert_eq!(divergence, injection, "KCL is the divergence, exactly");

    // KVL: the drop cochain is exact by construction, and its sum around a declared loop is zero.
    let loop_sum = &solution.drops[0] + &solution.drops[1] + &solution.drops[2] + &solution.drops[3];
    assert!(loop_sum.is_zero(), "KVL around the outer loop");

    assert_eq!(solution.currents, solution.drops, "unit conductance");
    assert_eq!(solution.drops[4], rat(-1, 2), "the chord carries one half");
}

/// Lean: `tellegen`.
#[test]
fn tellegen_balances_exactly_on_a_resistive_network() {
    let network = two_loop_network();
    let injection = vec![Rat::one(), Rat::zero(), -Rat::one(), Rat::zero()];
    let solution = network.solve(&injection).expect("the solve returns");
    let receipt = network
        .power_ledger(&solution.potentials)
        .expect("the ledger returns");
    assert!(receipt.balances(), "power delivered is power dissipated");
    assert_eq!(receipt.checked.len(), 4, "every node was read");
    assert_eq!(
        receipt.dissipated.rational().ok(),
        None,
        "a power reading is not dimensionless and cannot be read as a bare rational"
    );
    let watt = receipt.dissipated.dimension().clone();
    let expected = Quantity::new(rat(1, 2), watt);
    assert_eq!(receipt.dissipated, expected, "one half of a watt-unit");
    assert_eq!(receipt.delivered, expected);
    assert!(receipt.residual.is_zero());
}

/// Lean: `mem_harmonic_iff` at `d₁ = 0`; the harmonic 1-cochains of a graph are its loops.
#[test]
fn the_circulating_currents_are_the_harmonic_one_cochains_and_count_the_first_betti_number() {
    let network = two_loop_network();
    let reading = network.circulating().expect("the harmonic reading returns");
    assert_eq!(reading.dimension, 2, "five branches, four nodes, connected");
    assert_eq!(
        reading.betti, reading.dimension,
        "the rational harmonic dimension and the integral Betti number are two computations"
    );
    assert_eq!(reading.basis.len(), 2);
    // A circulating current is divergence-free: it injects nothing anywhere.
    let codifferential = network.operator().codifferential(0).expect("the codifferential");
    for circulation in &reading.basis {
        let divergence = codifferential.apply(circulation).expect("applies");
        assert!(
            divergence.iter().all(Zero::is_zero),
            "a circulating current has no source"
        );
    }
}

#[test]
fn an_injection_that_does_not_sum_to_zero_returns_the_annihilator() {
    let network = two_loop_network();
    let injection = vec![Rat::one(), Rat::zero(), Rat::zero(), Rat::zero()];
    let solution = network.solve(&injection).expect("the solve returns");
    assert!(!solution.solved(), "no potential drives a net injection");
    let annihilator = solution
        .unreachable
        .expect("the obstruction is returned, not a default");
    // The covector is constant: it annihilates the image of a graph Laplacian and pairs nonzero
    // with an injection that does not sum to zero.
    assert!(annihilator.iter().all(|value| !value.is_zero()));
}

#[test]
fn a_network_declaration_is_bounded_and_its_refusals_are_named() {
    assert!(matches!(
        ResistiveNetwork::declare("test|huge", usize::MAX, &[(0, 1, Rat::one())]),
        Err(JunctionRefusal::ExtentBeyondCeiling { .. })
    ));
    assert!(matches!(
        ResistiveNetwork::declare("test|loop", 2, &[(0, 0, Rat::one())]),
        Err(JunctionRefusal::DegenerateTriangulation { .. })
    ));
    assert!(matches!(
        ResistiveNetwork::declare("test|negative", 2, &[(0, 1, -Rat::one())]),
        Err(JunctionRefusal::NonPositiveIndexSquared { .. })
    ));
    assert!(matches!(
        ResistiveNetwork::declare("test|empty", 2, &[]),
        Err(JunctionRefusal::EmptyInterface)
    ));
}

#[test]
fn source_units_must_match_the_declared_flux_cochain_units() {
    let base = BaseUnits::declare(["V", "A"]).expect("base units");
    let potential = base.unit("V").expect("potential");
    let flux = base.unit("A").expect("flux");
    let source = base.unit("V").expect("deliberately mismatched source");
    assert!(matches!(
        JointUnits::declare("test|bad-source-unit", base, potential, flux, source),
        Err(JunctionRefusal::SourceDimensionDisagrees { .. })
    ));
}

#[test]
fn a_junction_law_requires_all_three_cochains_on_the_same_joint() {
    let units = JointUnits::electrical().expect("units");
    let joint = CausalCellId(0);
    let foreign = CausalCellId(1);
    assert!(matches!(
        JunctionLaw::found(
            "test|mismatched-joint",
            3,
            BTreeMap::from([(foreign, Rat::one())]),
            BTreeMap::from([(joint, Rat::one())]),
            BTreeMap::from([(joint, Rat::one())]),
            -1,
            OrientationBit::NotDeclared,
            units,
        ),
        Err(JunctionRefusal::JunctionCochainKeysDisagree)
    ));
}

// ---------------------------------------------------------------------------------------------
// 3. the checker
// ---------------------------------------------------------------------------------------------

/// A three-node chain with declared permittivities on its two branches: a dielectric interface.
fn dielectric_chain(left_permittivity: i64, right_permittivity: i64) -> ResistiveNetwork {
    let branches = [
        (0usize, 1usize, integer(left_permittivity)),
        (1, 2, integer(right_permittivity)),
    ];
    ResistiveNetwork::declare("test|dielectric", 3, &branches).expect("the chain stands")
}

/// **A finite Maxwell-type interface**: the normal displacement jumps by the surface charge, and
/// the jump is `δ E` at the interface node with the permittivity as the declared metric.
#[test]
fn a_dielectric_interface_jumps_the_normal_displacement_by_the_surface_charge() {
    let chain = dielectric_chain(2, 3);
    let operator = chain.operator();
    let units = JointUnits::electrostatic().expect("units");
    // Potential 0, 1, 4/3: the field is 1 on the left branch and 1/3 on the right, so the
    // displacement is 2 on the left and 1 on the right and jumps by one at the interface.
    let potential = vec![Rat::zero(), Rat::one(), rat(4, 3)];
    let field = operator
        .coboundary(0)
        .expect("coboundary")
        .apply(&potential)
        .expect("applies");
    assert_eq!(field, vec![Rat::one(), rat(1, 3)]);
    let source = vec![integer(-2), Rat::one(), Rat::one()];
    let interface = Interface::declare(
        "test|dielectric|interface",
        operator,
        0,
        BTreeMap::from([
            (operator.cells(1)[0], Side::Left),
            (operator.cells(1)[1], Side::Right),
        ]),
        BTreeSet::from([operator.cells(0)[1]]),
    )
    .expect("the interface stands");
    let verdict = check_junction(
        operator,
        &interface,
        &JunctionField {
            potential: &potential,
            field: &field,
            source: &source,
        },
        &units,
    )
    .expect("the check returns");
    match &verdict {
        JunctionVerdict::Balanced { law, checked } => {
            assert_eq!(checked.len(), 1, "one joint cell, and it was read");
            assert_eq!(law.normal_jump()[&operator.cells(0)[1]], Rat::one());
            assert_eq!(law.tangential()[&operator.cells(0)[1]], Rat::one());
            assert_eq!(law.valence(), 2, "two branches meet at the interface node");
            assert_eq!(
                law.euler_contribution(),
                0,
                "a valence-2 station thickens to an annulus"
            );
            assert!(!law.is_junction(), "valence two is a serial joint");
        }
        other => panic!("the interface balances: {other:?}"),
    }
}

/// **The same checker one grade up: the tangential magnetic field jumps by the surface current.**
///
/// The junction law is grade-parametric, and this is the other Maxwell interface condition read by
/// exactly the same function: the joint is a codimension-1 edge of a two-triangle complex, the two
/// triangles are its two sides, and `δ₁` of the 2-cochain at that edge is the jump the declared
/// surface current has to match.
#[test]
fn the_same_checker_one_grade_up_jumps_the_tangential_field_by_the_surface_current() {
    let triangulation = Triangulation::declare(
        "test|two-triangles",
        vec![
            ["a".to_owned(), "b".to_owned(), "c".to_owned()],
            ["b".to_owned(), "c".to_owned(), "d".to_owned()],
        ],
    )
    .expect("declares");
    let complex = triangulation.complex().expect("the complex stands");
    let operator = HodgeOperator::found(
        "test|two-triangles",
        &complex,
        &MetricDeclaration::unit("test|unit"),
        &BoundaryCondition::Free,
    )
    .expect("the operator stands");
    assert_eq!(operator.extent(1), 5, "five edges");
    assert_eq!(operator.extent(2), 2, "two triangles");

    // A magnetostatic declaration of its own: the tangential field and the surface current.
    let base = BaseUnits::declare(["H", "K"]).expect("the base stands");
    let units = JointUnits::declare(
        "test|magnetostatic|H,K",
        base.clone(),
        base.unit("H").expect("H"),
        base.unit("K").expect("K"),
        base.unit("K").expect("K"),
    )
    .expect("the units stand");

    let shared = operator.cells(1)[2];
    let field = vector(&[5, -2]);
    let source = vector(&[5, -5, 3, 2, -2]);
    let potential = vector(&[0, 0, 7, 0, 0]);
    let interface = Interface::declare(
        "test|two-triangles|seam",
        &operator,
        1,
        BTreeMap::from([
            (operator.cells(2)[0], Side::Left),
            (operator.cells(2)[1], Side::Right),
        ]),
        BTreeSet::from([shared]),
    )
    .expect("the interface stands");
    let verdict = check_junction(
        &operator,
        &interface,
        &JunctionField {
            potential: &potential,
            field: &field,
            source: &source,
        },
        &units,
    )
    .expect("the check returns");
    match &verdict {
        JunctionVerdict::Balanced { law, checked } => {
            assert_eq!(checked, &vec![shared]);
            assert_eq!(law.normal_jump()[&shared], integer(3), "5 + (-2)");
            assert_eq!(law.tangential()[&shared], integer(7));
            assert_eq!(law.valence(), 2, "two sheets meet along this crease");
            assert_eq!(law.euler_contribution(), 0);
        }
        other => panic!("the seam balances: {other:?}"),
    }
}

#[test]
fn an_unbalanced_junction_returns_the_whole_residual() {
    let chain = dielectric_chain(2, 3);
    let operator = chain.operator();
    let units = JointUnits::electrostatic().expect("units");
    let potential = vec![Rat::zero(), Rat::one(), rat(4, 3)];
    let field = operator
        .coboundary(0)
        .expect("coboundary")
        .apply(&potential)
        .expect("applies");
    let source = vec![integer(-2), integer(5), Rat::one()];
    let interface = Interface::whole(
        "test|dielectric|whole",
        operator,
        0,
        &BTreeSet::from([operator.cells(1)[0]]),
    )
    .expect("the interface stands");
    let verdict = check_junction(
        operator,
        &interface,
        &JunctionField {
            potential: &potential,
            field: &field,
            source: &source,
        },
        &units,
    )
    .expect("the check returns");
    match verdict {
        JunctionVerdict::Unbalanced {
            residual,
            offending,
            ..
        } => {
            assert_eq!(offending, vec![operator.cells(0)[1]]);
            assert_eq!(residual[&operator.cells(0)[1]], integer(-4));
            assert!(residual[&operator.cells(0)[0]].is_zero());
        }
        other => panic!("the declared source is wrong at the interface: {other:?}"),
    }
}

#[test]
fn an_empty_joint_is_refused_by_name_and_no_certificate_is_minted() {
    let chain = dielectric_chain(2, 3);
    let operator = chain.operator();
    assert!(matches!(
        Interface::declare(
            "test|empty",
            operator,
            0,
            BTreeMap::from([(operator.cells(1)[0], Side::Left)]),
            BTreeSet::new(),
        ),
        Err(JunctionRefusal::EmptyJoint)
    ));
    assert!(matches!(
        Interface::declare(
            "test|empty-sides",
            operator,
            0,
            BTreeMap::new(),
            BTreeSet::from([operator.cells(0)[1]]),
        ),
        Err(JunctionRefusal::EmptyInterface)
    ));
    assert!(matches!(
        check_tangential(&BTreeMap::new(), &BTreeMap::new(), &BTreeSet::new()),
        Err(JunctionRefusal::EmptyJoint)
    ));
    assert!(matches!(assemble_euler(&[]), Err(JunctionRefusal::EmptyJoint)));
}

#[test]
fn an_undecided_cell_returns_both_bounds_and_neither_is_a_default() {
    let chain = dielectric_chain(2, 3);
    let operator = chain.operator();
    let units = JointUnits::electrostatic().expect("units");
    let potential = vec![Rat::zero(), Rat::one(), rat(4, 3)];
    let field = operator
        .coboundary(0)
        .expect("coboundary")
        .apply(&potential)
        .expect("applies");
    let source = vec![integer(-2), Rat::one(), Rat::one()];
    let interface = Interface::declare(
        "test|open",
        operator,
        0,
        BTreeMap::from([
            (operator.cells(1)[0], Side::Left),
            (operator.cells(1)[1], Side::OpenExistence),
        ]),
        BTreeSet::from([operator.cells(0)[1]]),
    )
    .expect("the interface stands");
    let verdict = check_junction(
        operator,
        &interface,
        &JunctionField {
            potential: &potential,
            field: &field,
            source: &source,
        },
        &units,
    )
    .expect("the check returns");
    match verdict {
        JunctionVerdict::Open {
            undecided,
            present,
            absent,
        } => {
            assert_eq!(undecided, vec![operator.cells(1)[1]]);
            assert!(present.is_balanced(), "with the branch present it balances");
            assert!(
                !absent.is_balanced(),
                "without it the jump is two and the source is one"
            );
        }
        other => panic!("an undecided cell is carried as a family: {other:?}"),
    }
}

/// Lean: `glues_iff_agree`, `descend_restricts_right`, `no_descent_of_nonzero_jump`.
#[test]
fn a_nonzero_tangential_jump_admits_no_field_on_the_union() {
    let chain = dielectric_chain(2, 3);
    let operator = chain.operator();
    let shared = BTreeSet::from([operator.cells(0)[1]]);
    let agreeing_left = BTreeMap::from([
        (operator.cells(0)[0], Rat::zero()),
        (operator.cells(0)[1], Rat::one()),
    ]);
    let agreeing_right = BTreeMap::from([
        (operator.cells(0)[1], Rat::one()),
        (operator.cells(0)[2], rat(4, 3)),
    ]);
    match check_tangential(&agreeing_left, &agreeing_right, &shared).expect("returns") {
        TangentialVerdict::Continuous { checked } => assert_eq!(checked, vec![operator.cells(0)[1]]),
        other => panic!("they agree: {other:?}"),
    }
    let merged = descend(&agreeing_left, &agreeing_right, &shared)
        .expect("returns")
        .expect("a field on the union exists");
    assert_eq!(merged[&operator.cells(0)[0]], Rat::zero());
    assert_eq!(merged[&operator.cells(0)[2]], rat(4, 3));

    let disagreeing_right = BTreeMap::from([
        (operator.cells(0)[1], integer(5)),
        (operator.cells(0)[2], rat(4, 3)),
    ]);
    match check_tangential(&agreeing_left, &disagreeing_right, &shared).expect("returns") {
        TangentialVerdict::Jump { at } => {
            assert_eq!(at[&operator.cells(0)[1]], integer(-4));
        }
        other => panic!("they disagree: {other:?}"),
    }
    assert!(
        descend(&agreeing_left, &disagreeing_right, &shared)
            .expect("returns")
            .is_none(),
        "a nonzero jump is exactly the obstruction to being one field"
    );
}

/// Lean: `discrete_gauss` and `interior_cell_carries_no_boundary_flux`.
#[test]
fn the_discrete_gauss_statement_holds_over_a_declared_region() {
    let network = two_loop_network();
    let operator = network.operator();
    let injection = vec![Rat::one(), Rat::zero(), -Rat::one(), Rat::zero()];
    let solution = network.solve(&injection).expect("solves");
    let region = BTreeSet::from([operator.cells(0)[0], operator.cells(0)[1]]);
    let (interior, boundary) =
        gauss_region(operator, 0, &region, &solution.drops).expect("the region reading returns");
    assert_eq!(interior, boundary, "the source inside is the flux across");
    assert_eq!(interior, Rat::one(), "the declared injection inside the region");
    assert!(matches!(
        gauss_region(operator, 0, &BTreeSet::new(), &solution.drops),
        Err(JunctionRefusal::EmptyJoint)
    ));
}

#[test]
fn only_the_crossing_cells_carry_region_flux() {
    let network = two_loop_network();
    let operator = network.operator();
    let region = BTreeSet::from([operator.cells(0)[0], operator.cells(0)[1]]);
    let indicator: Vec<Rat> = operator
        .cells(0)
        .iter()
        .map(|cell| {
            if region.contains(cell) {
                Rat::one()
            } else {
                Rat::zero()
            }
        })
        .collect();
    let crossing = operator
        .coboundary(0)
        .expect("coboundary")
        .apply(&indicator)
        .expect("applies");
    // Branch 0 joins the two nodes inside the region and carries nothing; branches 1, 3 and 4
    // cross the region's boundary and branch 2 lies wholly outside.
    assert!(crossing[0].is_zero(), "the interior branch carries no flux");
    assert!(crossing[2].is_zero(), "the exterior branch carries none either");
    assert!(!crossing[1].is_zero());
    assert!(!crossing[3].is_zero());
    assert!(!crossing[4].is_zero());
}

/// Lean: `codiff_comp_zero`, `vertex_closure`, `no_interface_flux_for_a_nonclosing_source`.
#[test]
fn the_junction_sources_close_around_a_vertex_and_a_nonclosing_source_is_an_obstruction() {
    // A single filled triangle: three vertices, three edges, one face. The interfaces are the
    // edges (codimension one) and the vertices are the codimension-two strata.
    let triangulation = Triangulation::declare(
        "test|filled-triangle",
        vec![["a".to_owned(), "b".to_owned(), "c".to_owned()]],
    )
    .expect("declares");
    let complex = triangulation.complex().expect("the complex stands");
    let operator = HodgeOperator::found(
        "test|triangle",
        &complex,
        &MetricDeclaration::unit("test|unit"),
        &BoundaryCondition::Free,
    )
    .expect("the operator stands");

    // A source that *is* the interface flux of a 2-cochain closes at every vertex.
    let deposited = vec![integer(7)];
    let interface_source = operator
        .codifferential(1)
        .expect("codifferential")
        .apply(&deposited)
        .expect("applies");
    match check_vertex_closure(&operator, 1, &interface_source).expect("returns") {
        VertexVerdict::Closes { checked } => assert_eq!(checked.len(), 3, "three vertices read"),
        other => panic!("delta delta is zero: {other:?}"),
    }

    // And one that is not admits no 2-cochain at all: the obstruction is returned whole.
    let nonclosing = vector(&[1, 0, 0]);
    match check_vertex_closure(&operator, 1, &nonclosing).expect("returns") {
        VertexVerdict::Obstructed {
            residual,
            annihilator,
        } => {
            assert!(!residual.is_empty(), "the residual names where it fails");
            let annihilator = annihilator.expect("the covector proving no flux produces it");
            assert!(annihilator.iter().any(|value| !value.is_zero()));
        }
        other => panic!("this source does not close: {other:?}"),
    }
    assert!(matches!(
        check_vertex_closure(&operator, 0, &vector(&[0, 0, 0])),
        Err(JunctionRefusal::EmptyJoint)
    ));
}

// ---------------------------------------------------------------------------------------------
// 4. refraction
// ---------------------------------------------------------------------------------------------

/// Lean: `snell_squared`.
#[test]
fn snell_holds_exactly_in_squares_at_a_rational_interface() {
    let normal = vector(&[0, 0, 1]);
    let incident = vector(&[3, 0, 4]);
    // |k|^2 = 25, so with n1^2 = 1 the declared kappa^2 is 25 and sin^2 theta1 = 9/25.
    let reading = refract(&normal, &incident, &Rat::one(), &integer(4)).expect("refracts");
    assert_eq!(reading.tangential, vector(&[3, 0, 0]));
    assert_eq!(reading.tangential_squared, integer(9));
    assert_eq!(reading.wavenumber_squared, integer(25));
    assert_eq!(reading.incident_sine_squared, rat(9, 25));
    assert_eq!(reading.transmitted_sine_squared, rat(9, 100));
    assert!(reading.snell_identity_holds());
    assert_eq!(reading.snell_incident, rat(9, 25));
    match &reading.outcome {
        InterfaceOutcome::Transmitted { normal_squared } => {
            assert_eq!(*normal_squared, integer(91), "4 * 25 - 9");
        }
        other => panic!("a denser medium transmits: {other:?}"),
    }
}

/// Lean: `no_transmitted_covector_beyond_the_critical_angle`, `totally_reflected_iff`.
#[test]
fn total_internal_reflection_is_a_typed_deficit_and_never_a_nan() {
    let normal = vector(&[0, 0, 1]);
    let incident = vector(&[3, 0, 4]);
    // From n1^2 = 4 into n2^2 = 1: kappa^2 = 25/4, the far side offers 25/4 and the tangential
    // part demands 9, so there is no real normal component.
    let reading = refract(&normal, &incident, &integer(4), &Rat::one()).expect("refracts");
    match &reading.outcome {
        InterfaceOutcome::TotallyReflected { deficit } => {
            assert_eq!(*deficit, rat(11, 4), "9 - 25/4, exactly");
        }
        other => panic!("beyond the critical angle nothing is transmitted: {other:?}"),
    }
    assert!(
        reading.transmitted_sine_squared > Rat::one(),
        "the transmitted sine squared exceeds one, which is why there is no angle"
    );
    assert!(reading.snell_identity_holds(), "the identity in squares holds anyway");
}

#[test]
fn the_grazing_case_is_its_own_return() {
    let outcome = classify_interface(&integer(9), &Rat::one(), &integer(9));
    assert_eq!(outcome, InterfaceOutcome::Grazing);
    let transmitted = classify_interface(&integer(9), &Rat::one(), &integer(10));
    assert_eq!(
        transmitted,
        InterfaceOutcome::Transmitted {
            normal_squared: Rat::one()
        }
    );
}

/// Lean: `tangentialPart_orthogonal`.
#[test]
fn the_tangential_covector_is_orthogonal_to_the_normal_and_a_degenerate_normal_is_refused() {
    let normal = vector(&[1, 2, 2]);
    let covector = vector(&[5, -1, 3]);
    let tangential = tangential_part(&normal, &covector).expect("projects");
    assert!(
        dot_exact(&tangential, &normal).expect("pairs").is_zero(),
        "the tangential part is orthogonal to the normal, exactly"
    );
    assert!(matches!(
        tangential_part(&vector(&[0, 0, 0]), &covector),
        Err(JunctionRefusal::DegenerateNormal)
    ));
    assert!(matches!(
        refract(&normal, &covector, &Rat::zero(), &Rat::one()),
        Err(JunctionRefusal::NonPositiveIndexSquared { .. })
    ));
    assert!(matches!(
        dot_exact(&[], &[]),
        Err(JunctionRefusal::EmptyCovector)
    ));
}

// ---------------------------------------------------------------------------------------------
// 5. shocks
// ---------------------------------------------------------------------------------------------

/// Lean: `rankine_hugoniot_speed`, `rankine_hugoniot_balance`, `lax_admissible_iff`.
#[test]
fn the_burgers_shock_speed_is_the_exact_mean_and_the_balance_closes() {
    let reading = rankine_hugoniot(&integer(3), &Rat::one()).expect("reads");
    assert_eq!(reading.speed.parts().0, &integer(2), "(3 + 1) / 2");
    assert_eq!(reading.state_jump.parts().0, &integer(-2));
    assert_eq!(reading.flux_jump.parts().0, &integer(-4), "1/2 - 9/2");
    assert!(
        reading.balance_holds().expect("the dimensional product"),
        "s [[u]] = [[f]], value and dimension together"
    );
    assert_eq!(reading.verdict, ShockVerdict::Admissible);
}

#[test]
fn an_expansion_shock_violates_the_entropy_condition_and_reversal_reverses_the_verdict() {
    let forward = rankine_hugoniot(&Rat::one(), &integer(3)).expect("reads");
    assert_eq!(forward.verdict, ShockVerdict::EntropyViolating);
    assert_eq!(forward.speed.parts().0, &integer(2), "the speed is the same");
    let reversed = rankine_hugoniot(&integer(3), &Rat::one()).expect("reads");
    assert_eq!(reversed.verdict, ShockVerdict::Admissible);
    assert!(
        forward.balance_holds().expect("product")
            && reversed.balance_holds().expect("product"),
        "the balance is symmetric; only the entropy condition is one-way"
    );
    assert!(matches!(
        rankine_hugoniot(&integer(2), &integer(2)),
        Err(JunctionRefusal::NoJump)
    ));
}

// ---------------------------------------------------------------------------------------------
// 6. the Newtonian sheet, and what is only stated
// ---------------------------------------------------------------------------------------------

#[test]
fn the_newtonian_sheet_jumps_the_normal_derivative_by_the_declared_source() {
    let reading = newtonian_sheet(3, &integer(6)).expect("the sheet stands");
    assert!(reading.verdict.is_balanced());
    assert_eq!(reading.normal_jump.parts().0, &integer(6));
    assert_eq!(
        reading.normal_jump.dimension(),
        reading.source.dimension(),
        "the jump and the source carry one declared unit"
    );
    assert_eq!(reading.potential.len(), 7);
    assert!(matches!(
        newtonian_sheet(0, &Rat::one()),
        Err(JunctionRefusal::ExtentBeyondCeiling { .. })
    ));
}

#[test]
fn the_israel_conditions_are_stated_and_say_what_a_faithful_instance_would_owe() {
    let law = israel_junction_conditions();
    assert_eq!(law.grade, "proved-standard");
    assert!(law.statement.contains("induced"));
    assert!(law.owed.contains("Lorentzian"));
    assert!(
        law.owed.contains("Gauss-Codazzi"),
        "the junction must name the geometric realization it still requires"
    );
}

// ---------------------------------------------------------------------------------------------
// 7. films
// ---------------------------------------------------------------------------------------------

/// Lean: `three_conormals_balance_iff`. An exact rational configuration of the 120-degree law.
#[test]
fn three_conormals_of_equal_tension_balance_exactly_when_the_pairwise_products_are_minus_half() {
    let conormals = vec![vector(&[1, 1, 0]), vector(&[-1, 0, 1]), vector(&[0, -1, -1])];
    match plateau_line_balance(&conormals).expect("reads") {
        PlateauVerdict::Balanced {
            tension_squared,
            pairwise,
            required,
        } => {
            assert_eq!(tension_squared, integer(2));
            assert_eq!(required, -Rat::one(), "-T/2 with T = 2");
            assert_eq!(pairwise, vec![-Rat::one(), -Rat::one(), -Rat::one()]);
        }
        other => panic!("this configuration balances: {other:?}"),
    }
}

#[test]
fn an_unbalanced_or_unequal_film_junction_returns_its_own_verdict() {
    let unbalanced = vec![vector(&[1, 1, 0]), vector(&[-1, 0, 1]), vector(&[0, 1, -1])];
    match plateau_line_balance(&unbalanced).expect("reads") {
        PlateauVerdict::Unbalanced { residual } => assert_eq!(residual, vector(&[0, 2, 0])),
        other => panic!("these do not sum to zero: {other:?}"),
    }
    let unequal = vec![vector(&[1, 0, 0]), vector(&[0, 2, 0]), vector(&[-1, -2, 0])];
    assert!(matches!(
        plateau_line_balance(&unequal).expect("reads"),
        PlateauVerdict::UnequalTension { .. }
    ));
    assert!(matches!(
        plateau_line_balance(&[vector(&[1, 0])]),
        Err(JunctionRefusal::ConormalCount { expected: 3, .. })
    ));
}

/// Lean: `four_conormals_balance_of_pairwise` and `four_conormals_pairwise_sum`.
#[test]
fn the_tetrahedral_vertex_balances_and_the_balance_alone_does_not_force_that_angle() {
    let tetrahedral = vec![
        vector(&[1, 1, 1]),
        vector(&[1, -1, -1]),
        vector(&[-1, 1, -1]),
        vector(&[-1, -1, 1]),
    ];
    match plateau_vertex_balance(&tetrahedral).expect("reads") {
        PlateauVerdict::Balanced {
            tension_squared,
            pairwise,
            required,
        } => {
            assert_eq!(tension_squared, integer(3));
            assert_eq!(required, -Rat::one(), "-T/3 with T = 3");
            assert!(pairwise.iter().all(|value| *value == -Rat::one()));
        }
        other => panic!("the tetrahedral vertex balances: {other:?}"),
    }

    // The balance alone does not force it: this configuration balances at equal tension and its
    // pairwise products are not all -T/3. The 120-degree law at a junction *line* is forced; the
    // tetrahedral law at a *vertex* is an extra declaration.
    let degenerate = vec![
        vector(&[1, 0, 0]),
        vector(&[-1, 0, 0]),
        vector(&[0, 1, 0]),
        vector(&[0, -1, 0]),
    ];
    match plateau_vertex_balance(&degenerate).expect("reads") {
        PlateauVerdict::Balanced {
            pairwise, required, ..
        } => {
            assert_eq!(required, rat(-1, 3));
            assert!(
                pairwise.iter().any(|value| *value != required),
                "balanced, equal tension, and not tetrahedral"
            );
            let total = pairwise.iter().fold(Rat::zero(), |sum, value| sum + value);
            assert_eq!(total, integer(-2), "the six products sum to -2T with T = 1");
        }
        other => panic!("it balances: {other:?}"),
    }
}

// ---------------------------------------------------------------------------------------------
// 8. surfaces
// ---------------------------------------------------------------------------------------------

#[test]
fn the_pair_of_pants_is_orientable_with_three_boundary_circles_and_euler_characteristic_minus_one()
{
    let reading = pair_of_pants()
        .expect("the declaration stands")
        .reading()
        .expect("the reading returns");
    assert!(reading.certificate.is_surface, "{:?}", reading.certificate);
    assert_eq!(reading.euler_characteristic, -1);
    assert_eq!(
        reading.homology_euler_characteristic, -1,
        "the cell count and the Betti numbers agree"
    );
    assert_eq!(reading.boundary_circles, 3);
    assert_eq!(reading.orientation, OrientationBit::Preserving);
    assert_eq!(reading.integral_betti, vec![1, 2, 0]);
    assert!(reading.torsion.is_empty());
    assert_eq!(reading.mod_two_betti, vec![1, 2, 0]);
    assert!(!reading.fields_part(), "no torsion, so the fields agree");
}

#[test]
fn the_mobius_shorts_is_non_orientable_with_one_boundary_circle_and_euler_characteristic_minus_one()
{
    let reading = mobius_shorts()
        .expect("the declaration stands")
        .reading()
        .expect("the reading returns");
    assert!(reading.certificate.is_surface, "{:?}", reading.certificate);
    assert_eq!(reading.euler_characteristic, -1);
    assert_eq!(reading.boundary_circles, 1);
    match &reading.orientation {
        OrientationBit::Reversing { witness } => {
            assert!(!witness.is_empty(), "the seams are exhibited, not counted");
        }
        other => panic!("the Klein bottle minus a disc is non-orientable: {other:?}"),
    }
    assert_eq!(reading.integral_betti, vec![1, 2, 0]);
    assert!(
        reading.torsion.is_empty(),
        "a surface with boundary is homotopy equivalent to a wedge of circles, so it is \
         torsion-free whatever its orientability"
    );
    assert_eq!(reading.mod_two_betti, vec![1, 2, 0]);
}

#[test]
fn the_klein_bottle_separates_the_integral_reading_from_the_field_two_reading() {
    let reading = klein_bottle()
        .expect("the declaration stands")
        .reading()
        .expect("the reading returns");
    assert!(reading.certificate.is_surface, "{:?}", reading.certificate);
    assert_eq!(reading.euler_characteristic, 0);
    assert_eq!(reading.boundary_circles, 0, "closed");
    assert!(reading.orientation.reverses());
    assert_eq!(reading.integral_betti, vec![1, 1, 0]);
    assert_eq!(reading.torsion, vec![BigInt::from(2)]);
    assert_eq!(reading.mod_two_betti, vec![1, 2, 1]);
    assert!(
        reading.fields_part(),
        "the mod-two and rational readings part exactly where the torsion at two lives, which is \
         what exhibits non-orientability on a closed surface"
    );
}

#[test]
fn the_mobius_band_is_the_minimal_non_orientable_surface_with_boundary() {
    let reading = mobius_band()
        .expect("the declaration stands")
        .reading()
        .expect("the reading returns");
    assert!(reading.certificate.is_surface, "{:?}", reading.certificate);
    assert_eq!(reading.f_vector, (5, 10, 5));
    assert_eq!(reading.euler_characteristic, 0);
    assert_eq!(reading.boundary_circles, 1);
    assert!(reading.orientation.reverses());
}

#[test]
fn the_annulus_is_the_serial_join_thickened() {
    let reading = annulus()
        .expect("the declaration stands")
        .reading()
        .expect("the reading returns");
    assert!(reading.certificate.is_surface, "{:?}", reading.certificate);
    assert_eq!(reading.euler_characteristic, 0);
    assert_eq!(reading.boundary_circles, 2);
    assert_eq!(reading.orientation, OrientationBit::Preserving);
}

/// Lean: `chi_glue_along_zero` and `each_junction_costs_one_euler`.
#[test]
fn each_junction_costs_one_unit_of_euler_characteristic() {
    let pants = pair_of_pants()
        .expect("declares")
        .reading()
        .expect("reads")
        .euler_characteristic;
    let shorts = mobius_shorts()
        .expect("declares")
        .reading()
        .expect("reads")
        .euler_characteristic;
    assert_eq!(pants, -1);
    assert_eq!(shorts, -1);
    for count in 1..=6usize {
        let pieces = vec![pants; count];
        assert_eq!(
            assemble_euler(&pieces).expect("assembles"),
            -(count as i64),
            "n junctions cost n"
        );
    }
    // Gluing a pants to a Möbius shorts along a circle costs two, whatever their orientability.
    assert_eq!(assemble_euler(&[pants, shorts]).expect("assembles"), -2);
    // And an annulus — the serial join — costs nothing.
    let annulus_chi = annulus()
        .expect("declares")
        .reading()
        .expect("reads")
        .euler_characteristic;
    assert_eq!(annulus_chi, 0);
    assert_eq!(assemble_euler(&[pants, annulus_chi]).expect("assembles"), -1);
}

#[test]
fn the_pants_and_the_shorts_agree_on_every_homology_reading_and_two_receivers_separate_them() {
    let pants = pair_of_pants().expect("declares").reading().expect("reads");
    let shorts = mobius_shorts().expect("declares").reading().expect("reads");
    let comparison = compare_surfaces(&pants, &shorts);
    assert_eq!(
        comparison.homological_rung,
        Rung::ReceiverEqual,
        "a surface with boundary is a wedge of circles whatever its orientability"
    );
    assert_eq!(comparison.rung, Rung::NoRelation);
    assert_eq!(comparison.separators.len(), 2, "{:?}", comparison.separators);
    assert!(comparison.agreeing.contains(&"euler-characteristic".to_owned()));
    assert!(comparison.agreeing.contains(&"integral-betti".to_owned()));
    assert!(comparison.agreeing.contains(&"mod-two-betti".to_owned()));
    assert!(comparison.agreeing.contains(&"torsion".to_owned()));
    assert!(!comparison.agreeing.contains(&"orientation".to_owned()));
    assert!(!comparison.agreeing.contains(&"boundary-circles".to_owned()));

    // A surface compared with itself keeps the receiver-equal rung and returns no separator.
    let same = compare_surfaces(&pants, &pants);
    assert_eq!(same.rung, Rung::ReceiverEqual);
    assert!(same.separators.is_empty());
}

/// **The sharp case: the orientation bit is the only separator left.**
#[test]
fn the_one_holed_torus_and_the_mobius_shorts_are_separated_only_by_the_orientation_bit() {
    let orientable = one_holed_torus()
        .expect("declares")
        .reading()
        .expect("reads");
    let shorts = mobius_shorts().expect("declares").reading().expect("reads");
    assert!(orientable.certificate.is_surface, "{:?}", orientable.certificate);
    assert_eq!(orientable.euler_characteristic, -1);
    assert_eq!(orientable.boundary_circles, 1);
    assert_eq!(orientable.orientation, OrientationBit::Preserving);
    assert_eq!(orientable.integral_betti, shorts.integral_betti);
    assert_eq!(orientable.mod_two_betti, shorts.mod_two_betti);
    assert_eq!(orientable.torsion, shorts.torsion);

    let comparison = compare_surfaces(&orientable, &shorts);
    assert_eq!(comparison.homological_rung, Rung::ReceiverEqual);
    assert_eq!(comparison.rung, Rung::NoRelation);
    assert_eq!(
        comparison.separators,
        vec![
            "orientation: one carries a reversing dual circuit and the other does not".to_owned()
        ],
        "the Euler characteristic and every homology reading agree; orientability is the extra Z/2"
    );
    assert!(comparison.agreeing.contains(&"boundary-circles".to_owned()));
}

/// The torus and the Klein bottle are the closed pair the two identifications differ by.
#[test]
fn the_torus_and_the_klein_bottle_differ_only_by_the_half_twist_in_the_identification() {
    let torus_reading = torus().expect("declares").reading().expect("reads");
    let klein = klein_bottle().expect("declares").reading().expect("reads");
    assert!(torus_reading.certificate.is_surface, "{:?}", torus_reading.certificate);
    assert_eq!(torus_reading.f_vector, klein.f_vector, "the same cell counts");
    assert_eq!(torus_reading.euler_characteristic, 0);
    assert_eq!(klein.euler_characteristic, 0);
    assert_eq!(torus_reading.orientation, OrientationBit::Preserving);
    assert!(klein.orientation.reverses());
    assert_eq!(torus_reading.integral_betti, vec![1, 2, 1]);
    assert!(torus_reading.torsion.is_empty());
    assert_eq!(klein.integral_betti, vec![1, 1, 0]);
    assert_eq!(klein.torsion, vec![BigInt::from(2)]);
    let comparison = compare_surfaces(&torus_reading, &klein);
    assert_eq!(
        comparison.homological_rung,
        Rung::NoRelation,
        "closed surfaces are separated by homology; only the bordered ones need the bit"
    );
}

/// Lean: `reflection_circuit_determinant`, `orientation_reversing_iff_odd`.
#[test]
fn a_circuit_of_k_reflections_has_determinant_minus_one_to_the_k() {
    for reflections in 0..8u32 {
        let determinant = reflection_circuit_determinant(reflections);
        assert_eq!(determinant, if reflections.is_multiple_of(2) { 1 } else { -1 });
        assert_eq!(
            determinant == -1,
            !reflections.is_multiple_of(2),
            "odd is orientation-reversing, which is w_1"
        );
    }
}

#[test]
fn a_degenerate_or_repeated_triangulation_is_refused_and_a_branching_edge_is_reported() {
    assert!(matches!(
        Triangulation::declare("test|repeat", vec![["a".into(), "a".into(), "b".into()]]),
        Err(JunctionRefusal::DegenerateTriangulation { .. })
    ));
    assert!(matches!(
        Triangulation::declare(
            "test|twice",
            vec![
                ["a".into(), "b".into(), "c".into()],
                ["b".into(), "a".into(), "c".into()],
            ],
        ),
        Err(JunctionRefusal::DegenerateTriangulation { .. })
    ));
    assert!(matches!(
        Triangulation::declare("test|none", Vec::new()),
        Err(JunctionRefusal::DegenerateTriangulation { .. })
    ));
    // Three triangles on one edge: not a surface there, and the certificate says which edge.
    let branching = Triangulation::declare(
        "test|branching",
        vec![
            ["a".into(), "b".into(), "c".into()],
            ["a".into(), "b".into(), "d".into()],
            ["a".into(), "b".into(), "e".into()],
        ],
    )
    .expect("declares");
    let certificate = branching.certificate();
    assert!(!certificate.is_surface);
    // The reading is a surface's, so a failed certificate is its refusal and never a confident χ.
    assert!(matches!(
        branching.reading(),
        Err(JunctionRefusal::NotASurface { branching: 1, .. })
    ));
    assert_eq!(
        certificate.branching_edges,
        vec![("a".to_owned(), "b".to_owned())]
    );
}

#[test]
fn a_declared_grid_beyond_the_ceiling_is_refused_before_anything_is_sized_by_it() {
    assert!(matches!(
        grid_triangulation("test|huge", usize::MAX, 2, GridIdentification::Open, &[]),
        Err(JunctionRefusal::ExtentBeyondCeiling { .. })
    ));
    assert!(matches!(
        grid_triangulation("test|empty", 0, 2, GridIdentification::Open, &[]),
        Err(JunctionRefusal::ExtentBeyondCeiling { .. })
    ));
    assert!(matches!(
        grid_triangulation("test|outside", 2, 2, GridIdentification::Open, &[(5, 5)]),
        Err(JunctionRefusal::DegenerateTriangulation { .. })
    ));
}

// ---------------------------------------------------------------------------------------------
// 9. the exactness discipline
// ---------------------------------------------------------------------------------------------

#[test]
fn no_float_carries_or_decides_anything_in_this_owner() {
    // Comment lines are excluded deliberately: this owner's own header *names* `f32` and `f64` in
    // the sentence that forbids them, and a word in prose carries no value. Every other line is
    // scanned, and the scan is not vacuous — the line count it covers is asserted below.
    // The forbidden tokens are assembled at run time so that this test's own source does not
    // contain them.
    let banned: Vec<String> = [32u8, 64u8]
        .iter()
        .map(|width| format!("{}{width}", 'f'))
        .collect();
    assert_eq!(banned.len(), 2);
    for (name, source) in [
        ("junction_law.rs", include_str!("../junction_law.rs")),
        ("junction_law/tests.rs", include_str!("tests.rs")),
    ] {
        let mut scanned = 0usize;
        for line in source.lines() {
            let trimmed = line.trim_start();
            if trimmed.starts_with("//") {
                continue;
            }
            scanned += 1;
            for forbidden in &banned {
                assert!(
                    !line.contains(forbidden.as_str()),
                    "{name} line `{line}` names `{forbidden}`; no float may carry or decide a \
                     junction reading"
                );
            }
        }
        assert!(
            scanned > 200,
            "only {scanned} non-comment lines of {name} were scanned"
        );
    }
}

#[test]
fn every_declared_unit_carries_its_product_law() {
    for units in [
        JointUnits::electrical().expect("declares"),
        JointUnits::electrostatic().expect("declares"),
        JointUnits::newtonian_sheet().expect("declares"),
    ] {
        let product = units
            .potential()
            .product(units.flux())
            .expect("the product law");
        assert_eq!(&product, units.power());
        let power = units.power_quantity(Rat::one());
        assert!(
            power.rational().is_err(),
            "a power reading is not a bare number"
        );
        assert!(!units.lineage().is_empty());
        assert!(units.base().arity() >= 2);
        assert_eq!(units.source().base(), units.base());
    }
}
