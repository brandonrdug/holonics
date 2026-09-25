//! One test per law and one per counterexample of the information instance.

use num_traits::{One, Zero};

use super::*;
use crate::aeon::{AeonError, AxisRate, ClockAxis, PositiveLaw, join_axes};
use crate::geometry::{RatMat3, RatVec3};
use crate::physics::fluid::cells::GridCell;
use crate::physics::fluid::control_volume::{AffineFlow, ControlVolume, NewtonianMaterial};
use crate::physics::spacetime::{ConstitutedState, source_map};
use crate::physics::thermal::ThermalCell;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::surprisal::SymbolicSurprisal;
use crate::ratio::{ExactOrdering, GaussianRat, LogRatio, Presentation, Rat, integer, rat};

fn log2(ratio: &Rat) -> SymbolicSurprisal {
    SymbolicSurprisal::log2_of_ratio(ratio).unwrap()
}

fn law(masses: &[Rat]) -> PositiveLaw {
    PositiveLaw::new(masses.to_vec()).unwrap()
}

fn g(re: i64, im: i64) -> GaussianRat {
    GaussianRat::from_i64(re, im)
}

/// The bath: a K3 cell of capacity `2` and energy `6`, temperature `3`.
fn bath() -> ThermalCell {
    ThermalCell::new(integer(2), integer(6)).unwrap()
}

/// The levels `Eᵢ = S(qᵢ)` of a reference, canonical in the gauge `log Z = 0`.
fn levels_of(reference: &PositiveLaw) -> Vec<SymbolicSurprisal> {
    reference
        .masses()
        .iter()
        .map(|mass| SymbolicSurprisal::of_probability(mass).unwrap())
        .collect()
}

/// The port of reference `q = (1/2, 1/2)` and the population `p = (1/10, 9/10)`; the covector is the
/// owner's lift of `log(ψ_T/ψ_H)` at each level: `R = 2 + i` (`|R|² = 5 = q₀/p₀`) with one winding,
/// and `R = (2 + i)/3` (`|R|² = 5/9 = q₁/p₁`), the matched covector.
fn port_and_covector() -> (ThermalPort, PositiveLaw, Vec<LevelCovector>) {
    let reference = law(&[rat(1, 2), rat(1, 2)]);
    let port = ThermalPort::new(bath(), levels_of(&reference), reference).unwrap();
    let covector = vec![
        LevelCovector::of_lift(LogRatio::new(g(2, 1), g(1, 0), 1).unwrap()).unwrap(),
        LevelCovector::of_lift(LogRatio::new(g(2, 1), g(3, 0), 0).unwrap()).unwrap(),
    ];
    (port, law(&[rat(1, 10), rat(9, 10)]), covector)
}

/// `D₂(p‖q)` for the fixture: `(1/10) log₂(1/5) + (9/10) log₂(9/5)`.
fn fixture_relative_entropy() -> SymbolicSurprisal {
    log2(&rat(1, 5))
        .scaled(&rat(1, 10))
        .plus(&log2(&rat(9, 5)).scaled(&rat(9, 10)))
}

/// Lean `PortWork.canonicalState_canonical`, `canonicalState_eq`: the port's constitution is its
/// levels; the canonical state computed from them is the reference, and a reference that is not
/// canonical for the levels is refused.
#[test]
fn the_port_is_constituted_by_its_levels() {
    let levels = vec![
        SymbolicSurprisal::term(2, integer(1)).unwrap(),
        SymbolicSurprisal::term(2, integer(2)).unwrap(),
        SymbolicSurprisal::term(2, integer(2)).unwrap(),
    ];
    let port = ThermalPort::of_levels(bath(), levels.clone()).unwrap();
    assert_eq!(
        port.reference().masses(),
        &[rat(1, 2), rat(1, 4), rat(1, 4)]
    );
    assert_eq!(
        ThermalPort::new(bath(), levels, law(&[rat(1, 3), rat(1, 3), rat(1, 3)])),
        Err(InformationError::NotCanonical { level: 1 })
    );
}

/// Lean `PortWork.quenchWork_eq`, `matched_relaxed`, `reversible_production_zero`,
/// `matched_restoreWork`, `restore_production_zero`, `extracted_work`, `free_relaxation_production`,
/// `work_or_production`: the matched covector reaches the port; the population relaxes to itself,
/// the protocol produces nothing, the quench work is `−D`, the free-energy drop is `D`, free
/// relaxation would produce `D`, the restoration returns the reference, and the phase face is
/// retained.
#[test]
fn the_matched_covector_at_the_port_is_reversible() {
    let (port, population, covector) = port_and_covector();
    let returned = apply(&port, &population, &covector).unwrap();
    let relative = fixture_relative_entropy();
    assert_eq!(returned.relaxed, population);
    assert!(returned.production.is_zero());
    assert!(returned.relaxation_divergence.is_zero());
    assert!(returned.restore_work.is_zero());
    assert_eq!(returned.relative_entropy, relative);
    assert_eq!(returned.quench_work, relative.scaled(&-Rat::one()));
    assert_eq!(returned.free_energy_drop, relative);
    assert_eq!(returned.free_production, relative);
    assert_eq!(&returned.after, port.reference());
    assert!(returned.balances());
    assert_eq!(returned.retained_phase[0].as_ref().unwrap().winding, 1);
    assert!(
        !returned.heat().is_zero(),
        "the populations differ in entropy"
    );
}

/// Lean `quenched_canonical`: after the matched quench the population is canonical for the shifted
/// levels, `E′ᵢ = −log₂ pᵢ`.
#[test]
fn the_matched_quench_makes_the_population_canonical() {
    let (port, population, covector) = port_and_covector();
    let returned = apply(&port, &population, &covector).unwrap();
    for (level, mass) in returned.shifted_levels.iter().zip(population.masses()) {
        assert_eq!(level, &SymbolicSurprisal::of_probability(mass).unwrap());
    }
}

/// [counterexample] Lean `protocol_production`, `extracted_work_general`, `extracted_work_le`: a
/// covector comparing another reference with this population is admitted as a level shift, but it
/// relaxes the population to `q′ = (1/3, 2/3)` and produces `D₂(p‖q′) > 0`, so the work extracted
/// falls short of the free-energy drop by exactly that production.
#[test]
fn an_unmatched_covector_produces_entropy_and_extracts_less() {
    let (port, population, _) = port_and_covector();
    let foreign = vec![
        LevelCovector::of_intensities(&rat(1, 2), &rat(1, 3)).unwrap(),
        LevelCovector::of_intensities(&rat(1, 2), &rat(2, 3)).unwrap(),
    ];
    let returned = apply(&port, &population, &foreign).unwrap();
    assert_eq!(returned.relaxed.masses(), &[rat(1, 3), rat(2, 3)]);
    assert!(returned.balances());
    assert_eq!(
        returned.production.compare(&SymbolicSurprisal::zero()),
        Ok(ExactOrdering::Greater)
    );
    let extracted = returned.work().scaled(&-Rat::one());
    assert_eq!(
        extracted.compare(&returned.free_energy_drop),
        Ok(ExactOrdering::Less)
    );
    assert!(returned.restore_production.is_zero());
}

/// Lean `restore_production_zero`; `Physics/Thermal/Exchange.cell_entropy_enclosure`;
/// `Physics/Spacetime/StressEnergy.sourceMap`: with a dyadic population the heat is a rational
/// number of bits, `Q = 1/4`; it returns to the K3 bath at `T = 3` as `−3/4`, and through the bath's
/// internal energy to the stress–energy source's `T⁰⁰`.
#[test]
fn the_port_heat_returns_to_the_bath_and_the_source() {
    let reference = law(&[rat(1, 4), rat(1, 4), rat(1, 4), rat(1, 4)]);
    let port = ThermalPort::new(bath(), levels_of(&reference), reference.clone()).unwrap();
    let population = law(&[rat(1, 2), rat(1, 4), rat(1, 8), rat(1, 8)]);
    let covector: Vec<LevelCovector> = reference
        .masses()
        .iter()
        .zip(population.masses())
        .map(|(q, p)| LevelCovector::of_intensities(q, p).unwrap())
        .collect();
    let returned = apply(&port, &population, &covector).unwrap();
    assert!(returned.balances());
    assert_eq!(
        returned.heat(),
        SymbolicSurprisal::term(2, rat(1, 4)).unwrap()
    );
    let after = returned.bath_after(&port).unwrap();
    assert_eq!(after.energy(), &rat(21, 4));
    assert!(returned.bath_entropy(&port).unwrap().lower < Rat::zero());
    let volume = ControlVolume::new(GridCell::unit_cube(3).unwrap()).unwrap();
    let flow = AffineFlow {
        velocity: RatVec3::zero(),
        gradient: RatMat3::from_i64([[0, 0, 0], [0, 0, 0], [0, 0, 0]]),
    };
    let source = |cell: &ThermalCell| {
        source_map(&ConstitutedState::of_cells(
            &volume,
            integer(1),
            cell,
            Rat::zero(),
            NewtonianMaterial::new(Rat::zero(), Rat::zero()),
            &flow,
            RatVec3::zero(),
        ))
    };
    assert_eq!(
        source(&after).at(0, 0) - source(port.bath()).at(0, 0),
        rat(-3, 4)
    );
}

/// [counterexample] The fixture's heat `H₂(q) − H₂(p)` is irrational in bits: the bath's rational
/// first law cannot receive it, and it is refused rather than rounded.
#[test]
fn an_irrational_heat_is_refused_by_the_bath() {
    let (port, population, covector) = port_and_covector();
    let returned = apply(&port, &population, &covector).unwrap();
    assert!(matches!(
        returned.bath_after(&port),
        Err(InformationError::IrrationalHeat { .. })
    ));
}

/// [counterexample] Lean `equal_face_different_effort`: the populations `(1/3, 2/3)` and `(2/3, 1/3)`
/// return one cross-entropy face against the uniform reference, but their efforts at the uniform
/// port differ.
#[test]
fn equal_cross_entropy_conceals_different_efforts() {
    let uniform = law(&[rat(1, 2), rat(1, 2)]);
    let (left, right) = (law(&[rat(1, 3), rat(2, 3)]), law(&[rat(2, 3), rat(1, 3)]));
    assert_eq!(
        uniform.cross_entropy(&left).unwrap(),
        uniform.cross_entropy(&right).unwrap()
    );
    let port = ThermalPort::new(bath(), levels_of(&uniform), uniform.clone()).unwrap();
    let covector = |population: &PositiveLaw| -> Vec<LevelCovector> {
        uniform
            .masses()
            .iter()
            .zip(population.masses())
            .map(|(q, p)| LevelCovector::of_intensities(q, p).unwrap())
            .collect()
    };
    let left_return = apply(&port, &left, &covector(&left)).unwrap();
    let right_return = apply(&port, &right, &covector(&right)).unwrap();
    assert_ne!(left_return.effort, right_return.effort);
}

/// Lean `Aeon/Production/FirstLaw.hasDerivAt_crossEntropy`: both motions enter the rate. A population moving
/// at `(1, −1)` against `(1/4, 3/4)` gives `ln 2 · log₂ 3 = ln 3`; the reference's motion enters as the
/// exact rational `−Σ p q̇/q`.
#[test]
fn the_cross_entropy_rate_carries_both_motions() {
    let rate = cross_entropy_rate(
        &law(&[rat(1, 2), rat(1, 2)]),
        &[integer(1), integer(-1)],
        &law(&[rat(1, 4), rat(3, 4)]),
        &[rat(1, 8), rat(-1, 8)],
    )
    .unwrap();
    assert_eq!(rate.log2_part, log2(&integer(3)));
    assert_eq!(
        rate.rational_part,
        -(rat(1, 2) * rat(1, 8) / rat(1, 4)) + rat(1, 2) * rat(1, 8) / rat(3, 4)
    );
}

/// [counterexample] Lean `moving_reference_rate`: a fixed population against a moving reference
/// changes its cross-entropy at `2/3` while the population term is zero.
#[test]
fn the_reference_motion_is_load_bearing() {
    let population = law(&[rat(1, 3), rat(2, 3)]);
    let reference = law(&[rat(1, 2), rat(1, 2)]);
    let with_motion = cross_entropy_rate(
        &population,
        &[Rat::zero(), Rat::zero()],
        &reference,
        &[integer(1), integer(-1)],
    )
    .unwrap();
    let population_only = cross_entropy_rate(
        &population,
        &[Rat::zero(), Rat::zero()],
        &reference,
        &[Rat::zero(), Rat::zero()],
    )
    .unwrap();
    assert_eq!(with_motion.rational_part, rat(2, 3));
    assert!(with_motion.log2_part.is_zero());
    assert!(population_only.is_zero());
}

/// [counterexample] Lean `sum_rate_eq_zero`: a rate that changes the total mass is a moving support,
/// refused.
#[test]
fn a_moving_support_is_refused() {
    let half = law(&[rat(1, 2), rat(1, 2)]);
    let refused = cross_entropy_rate(
        &half,
        &[integer(1), Rat::zero()],
        &half,
        &[Rat::zero(), Rat::zero()],
    );
    assert!(matches!(
        refused,
        Err(InformationError::MovingSupport { .. })
    ));
}

/// Lean `hasDerivAt_crossEntropy_clocks`: on plural clocks each dot is converted through the join of
/// the axes, `dτ_axis/dτ_common`.
#[test]
fn the_rate_on_plural_clocks_converts_each_dot_through_the_join() {
    let rates = [
        AxisRate::new(
            ClockAxis::Source,
            ClockAxis::Observation,
            Presentation::new(integer(3), integer(1)),
        )
        .unwrap(),
        AxisRate::new(
            ClockAxis::Receiving,
            ClockAxis::Observation,
            Presentation::new(integer(1), integer(2)),
        )
        .unwrap(),
    ];
    let join = join_axes(&rates).unwrap();
    let (population, population_rate) = (law(&[rat(1, 2), rat(1, 2)]), [integer(1), integer(-1)]);
    let (reference, reference_rate) = (law(&[rat(1, 4), rat(3, 4)]), [rat(1, 8), rat(-1, 8)]);
    let clocked = cross_entropy_rate_on_clocks(
        Clocked {
            law: &population,
            rate: &population_rate,
            axis: ClockAxis::Source,
        },
        Clocked {
            law: &reference,
            rate: &reference_rate,
            axis: ClockAxis::Receiving,
        },
        &join,
        ClockAxis::Observation,
    )
    .unwrap();
    let still = [Rat::zero(), Rat::zero()];
    let population_term =
        cross_entropy_rate(&population, &population_rate, &reference, &still).unwrap();
    let reference_term =
        cross_entropy_rate(&population, &still, &reference, &reference_rate).unwrap();
    assert_eq!(
        clocked,
        population_term
            .scaled(&integer(3))
            .plus(&reference_term.scaled(&rat(1, 2)))
    );
}

/// [counterexample] Lean `triangle_defect`: when the declared rates do not close around a cycle, the
/// rate on plural clocks is refused with the join's defect.
#[test]
fn a_clock_defect_refuses_the_rate() {
    let rates = [
        AxisRate::new(
            ClockAxis::Source,
            ClockAxis::Receiving,
            Presentation::new(integer(2), integer(1)),
        )
        .unwrap(),
        AxisRate::new(
            ClockAxis::Receiving,
            ClockAxis::Fluid,
            Presentation::new(integer(3), integer(1)),
        )
        .unwrap(),
        AxisRate::new(
            ClockAxis::Fluid,
            ClockAxis::Source,
            Presentation::new(integer(1), integer(5)),
        )
        .unwrap(),
    ];
    let join = join_axes(&rates).unwrap();
    let population = law(&[rat(1, 2), rat(1, 2)]);
    let still = [Rat::zero(), Rat::zero()];
    let refused = cross_entropy_rate_on_clocks(
        Clocked {
            law: &population,
            rate: &still,
            axis: ClockAxis::Source,
        },
        Clocked {
            law: &population,
            rate: &still,
            axis: ClockAxis::Receiving,
        },
        &join,
        ClockAxis::Fluid,
    );
    assert!(matches!(
        refused,
        Err(InformationError::Aeon(error)) if matches!(*error, AeonError::AxesDefect { .. })
    ));
}

/// Lean `hasDerivAt_kl` at a fixed reference: the free energy's rate is the ratio covector paired with
/// the produced velocity, `Σ ṗ log₂(p/q)`; at the reference it vanishes.
#[test]
fn the_free_energy_rate_pairs_the_covector_with_the_velocity() {
    let rate = free_energy_rate(
        &law(&[rat(1, 3), rat(2, 3)]),
        &[integer(1), integer(-1)],
        &law(&[rat(2, 3), rat(1, 3)]),
    )
    .unwrap();
    assert_eq!(rate, log2(&rat(1, 2)).minus(&log2(&integer(2))));
    let at_rest = free_energy_rate(
        &law(&[rat(2, 3), rat(1, 3)]),
        &[integer(1), integer(-1)],
        &law(&[rat(2, 3), rat(1, 3)]),
    )
    .unwrap();
    assert!(at_rest.is_zero());
}

fn fluid_step() -> ExactRatMatrix {
    ExactRatMatrix::new(vec![
        vec![integer(1), rat(1, 2)],
        vec![Rat::zero(), rat(1, 2)],
    ])
    .unwrap()
}

fn thermal_step() -> ExactRatMatrix {
    ExactRatMatrix::new(vec![
        vec![rat(1, 2), Rat::zero()],
        vec![rat(1, 2), integer(1)],
    ])
    .unwrap()
}

/// Lean `commuting_square_reads_alike`: a commuting square returns one population and one
/// cross-entropy.
#[test]
fn a_commuting_flow_square_returns_one_cross_entropy() {
    let squared = fluid_step().multiply(&fluid_step()).unwrap();
    let square = flow_square(
        &fluid_step(),
        &squared,
        &law(&[rat(1, 2), rat(1, 2)]),
        &law(&[rat(1, 3), rat(2, 3)]),
    )
    .unwrap();
    assert!(matches!(
        square,
        FlowSquare::ClosesOnState {
            matrices_commute: true,
            ..
        }
    ));
}

/// [counterexample] Agreement on one state is not commutation: the two swaps `(0 1)` and `(1 2)` do
/// not commute, yet both fix the uniform law, so the square closes on it; and a step that does not
/// keep a population a population is refused.
#[test]
fn a_square_can_close_on_a_state_without_commuting() {
    let permutation = |image: [usize; 3]| {
        ExactRatMatrix::new(
            (0..3)
                .map(|row| {
                    (0..3)
                        .map(|column| {
                            if image[column] == row {
                                Rat::one()
                            } else {
                                Rat::zero()
                            }
                        })
                        .collect()
                })
                .collect(),
        )
        .unwrap()
    };
    let uniform = law(&[rat(1, 3), rat(1, 3), rat(1, 3)]);
    let square = flow_square(
        &permutation([1, 0, 2]),
        &permutation([0, 2, 1]),
        &uniform,
        &uniform,
    )
    .unwrap();
    assert!(matches!(
        square,
        FlowSquare::ClosesOnState {
            matrices_commute: false,
            ..
        }
    ));
    let scaling = ExactRatMatrix::from_diagonal(vec![integer(1), integer(2)]).unwrap();
    assert_eq!(
        flow_square(
            &scaling,
            &fluid_step(),
            &law(&[rat(1, 2), rat(1, 2)]),
            &law(&[rat(1, 2), rat(1, 2)]),
        ),
        Err(InformationError::NotAStep {
            what: "the first step",
            column: 1
        })
    );
}

/// [counterexample] Lean `flow_square_orders`, `square_defect`, `flow_square_crossEntropy_differs`:
/// the fluid and thermal steps do not commute; the orders return `(3/8, 5/8)` and `(5/8, 3/8)`, the
/// commutator on the state is their difference, and their cross-entropies against `(1/3, 2/3)` differ
/// by exactly `−1/4` bit.
#[test]
fn a_noncommuting_flow_square_changes_the_cross_entropy() {
    let square = flow_square(
        &fluid_step(),
        &thermal_step(),
        &law(&[rat(1, 2), rat(1, 2)]),
        &law(&[rat(1, 3), rat(2, 3)]),
    )
    .unwrap();
    let FlowSquare::Defect {
        first_then_second,
        second_then_first,
        commutator_on_state,
        cross_entropy_difference,
    } = square
    else {
        panic!("the steps do not commute");
    };
    assert_eq!(first_then_second, vec![rat(3, 8), rat(5, 8)]);
    assert_eq!(second_then_first, vec![rat(5, 8), rat(3, 8)]);
    assert_eq!(commutator_on_state, vec![rat(-1, 4), rat(1, 4)]);
    assert_eq!(
        cross_entropy_difference,
        log2(&integer(2)).scaled(&rat(-1, 4))
    );
}
