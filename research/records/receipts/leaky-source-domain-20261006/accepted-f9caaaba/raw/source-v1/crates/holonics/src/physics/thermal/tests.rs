//! One test per law and one per counterexample of the thermal instance.

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::*;
use crate::aeon::{MarkovChain, epochs};
use crate::geometry::{RatMat3, RatVec3};
use crate::holon::HolonState;
use crate::holon::conformance::check_exact_advance;
use crate::holon::law::{HolonLaw, ReferenceHolon, Scheme};
use crate::physics::fluid::cells::GridCell;
use crate::physics::fluid::control_volume::{AffineFlow, ControlVolume, NewtonianMaterial};
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::surprisal::SymbolicSurprisal;
use crate::ratio::{Rat, integer, rat};

fn log2(ratio: &Rat) -> SymbolicSurprisal {
    SymbolicSurprisal::log2_of_ratio(ratio).unwrap()
}

fn cell(capacity: Rat, energy: Rat) -> ThermalCell {
    ThermalCell::new(capacity, energy).unwrap()
}

fn chain(rows: Vec<Vec<Rat>>) -> MarkovChain {
    MarkovChain::new(ExactRatMatrix::new(rows).unwrap()).unwrap()
}

/// The biased rotation of three cells, `2/3` forward and `1/3` back (Lean
/// `PathReversal.Rotation`).
fn rotation() -> MarkovChain {
    let (f, b, z) = (rat(2, 3), rat(1, 3), Rat::zero());
    chain(vec![
        vec![z.clone(), f.clone(), b.clone()],
        vec![b.clone(), z.clone(), f.clone()],
        vec![f, b, z],
    ])
}

/// A lazy ring of four cells with unequal forward and backward rates.
fn lazy_ring() -> MarkovChain {
    let z = Rat::zero();
    chain(vec![
        vec![rat(1, 4), rat(1, 2), z.clone(), rat(1, 4)],
        vec![rat(1, 3), rat(1, 6), rat(1, 2), z.clone()],
        vec![z.clone(), rat(1, 5), rat(1, 5), rat(3, 5)],
        vec![rat(1, 2), z, rat(1, 4), rat(1, 4)],
    ])
}

/// A lazy open chain of four cells (birth and death).
fn birth_death() -> MarkovChain {
    let z = Rat::zero();
    chain(vec![
        vec![rat(1, 2), rat(1, 2), z.clone(), z.clone()],
        vec![rat(1, 4), rat(1, 4), rat(1, 2), z.clone()],
        vec![z.clone(), rat(1, 3), rat(1, 3), rat(1, 3)],
        vec![z.clone(), z, rat(2, 3), rat(1, 3)],
    ])
}

// ---------------------------------------------------------------------------------------------
// Exchange and the viscous port
// ---------------------------------------------------------------------------------------------

/// `Physics/Thermal/Exchange.first_law`, `productionRate_eq`: the stored energy changes by the
/// port work (read from the cells before and after, not from the returned residual), and the
/// production rate is `κ(T₀ − T₁)²/(T₀T₁) + W₀/T₀ + W₁/T₁`, the Clausius product of the heat
/// current and the inverse-temperature drop.
#[test]
fn two_cells_keep_the_first_law_and_an_exact_production_rate() {
    let cells = [cell(integer(2), integer(6)), cell(integer(3), integer(3))];
    let contact = Contact::new(rat(1, 2)).unwrap();
    let work = [ViscousWork::new(rat(1, 3)).unwrap(), ViscousWork::none()];
    let tick = rat(1, 4);
    let step = exchange(&cells, &contact, &tick, &work).unwrap();
    assert_eq!(step.heat, rat(1, 4));
    assert_eq!(
        step.next[0].energy() + step.next[1].energy(),
        integer(6) + integer(3) + &tick * rat(1, 3)
    );
    assert_eq!(
        step.next[0].energy(),
        &(integer(6) - rat(1, 4) + rat(1, 12))
    );
    assert!(step.first_law_residual.is_zero());
    let (t0, t1) = (integer(3), integer(1));
    let clausius = rat(1, 2) * (&t0 - &t1) * (t1.recip() - t0.recip());
    assert_eq!(step.production_rate, clausius + rat(1, 3) / &t0);
    assert_eq!(step.production_rate, rat(2, 3) + rat(1, 9));
}

/// `Physics/Thermal/Exchange.productionRate_eq_zero_iff`: at equal temperatures no heat moves and
/// nothing is produced.
#[test]
fn equal_temperatures_produce_nothing() {
    let cells = [cell(integer(2), integer(4)), cell(integer(5), integer(10))];
    let none = [ViscousWork::none(), ViscousWork::none()];
    let step = exchange(
        &cells,
        &Contact::new(integer(3)).unwrap(),
        &rat(1, 10),
        &none,
    )
    .unwrap();
    assert!(step.heat.is_zero());
    assert!(step.production_rate.is_zero());
    assert!(step.entropy().lower.is_zero() && step.entropy().upper.is_zero());
}

/// `Physics/Thermal/Exchange.exchange_entropy_enclosure`, `lower_reading_eq`,
/// `exchange_entropy_nonneg`: under the tick condition the contact's lower Clausius reading is
/// `hκ(T₀ − T₁)²(1 − hκ(1/C₀ + 1/C₁))/(T₀'T₁') ≥ 0`, and the enclosure is ordered.
#[test]
fn the_tick_condition_certifies_the_sign_of_the_entropy() {
    let cells = [cell(integer(2), integer(10)), cell(integer(1), integer(1))];
    let (kappa, h) = (integer(1), rat(1, 2));
    let none = [ViscousWork::none(), ViscousWork::none()];
    let step = exchange(&cells, &Contact::new(kappa.clone()).unwrap(), &h, &none).unwrap();
    let factor = &h * &kappa * (rat(1, 2) + integer(1));
    assert_eq!(factor, rat(3, 4));
    let (t0, t1) = (cells[0].temperature(), cells[1].temperature());
    let (n0, n1) = (step.next[0].temperature(), step.next[1].temperature());
    let exact = &h * &kappa * (&t0 - &t1) * (&t0 - &t1) * (Rat::one() - factor) / (n0 * n1);
    assert_eq!(step.contact_entropy.lower, exact);
    assert!(step.contact_entropy.is_certified_nonnegative());
    assert!(step.contact_entropy.lower <= step.contact_entropy.upper);
}

/// `Physics/Thermal/Exchange.overshoot_destroys_entropy`: at `hκ(1/C₀ + 1/C₁) = 5/2` the tick is
/// refused; carried out, it would reach `1/2` and `7/2`, and with unit capacities the entropy of
/// the tick is the log of the ratio product `(1/2)/3 · (7/2)/1 = 7/12 < 1`.
#[test]
fn an_overshooting_tick_is_refused_because_it_destroys_entropy() {
    let cells = [cell(integer(1), integer(3)), cell(integer(1), integer(1))];
    let none = [ViscousWork::none(), ViscousWork::none()];
    let refused = exchange(
        &cells,
        &Contact::new(rat(5, 4)).unwrap(),
        &integer(1),
        &none,
    );
    assert_eq!(refused, Err(ThermalError::Overshoot { factor: rat(5, 2) }));
    let heat = rat(5, 4) * (integer(3) - integer(1));
    let (u0, u1) = (integer(3) - &heat, integer(1) + &heat);
    assert_eq!((u0.clone(), u1.clone()), (rat(1, 2), rat(7, 2)));
    let ratio_product = u0 / integer(3) * (u1 / integer(1));
    assert_eq!(ratio_product, rat(7, 12));
    assert!(ratio_product < Rat::one());
}

/// `Physics/Thermal/ViscousPort.port_production_eq_zero_iff`, `port_entropy_enclosure`: admitted
/// work enters internal energy, with production `W/T` and the tick's entropy enclosed between
/// `hW C/U'` and `hW C/U`.
#[test]
fn viscous_work_enters_heat_with_its_entropy_enclosed() {
    let body = cell(integer(1), integer(1));
    let work = ViscousWork::new(integer(2)).unwrap();
    let port = work.receive(&body, &rat(1, 2)).unwrap();
    assert_eq!(port.next.energy(), &integer(2));
    assert_eq!(port.internal_gain, integer(1));
    assert_eq!(work.production_rate(&body), integer(2));
    assert!(ViscousWork::none().production_rate(&body).is_zero());
    // ΔS = log 2 ∈ [1/2, 1].
    assert_eq!(port.entropy.lower, rat(1, 2));
    assert_eq!(port.entropy.upper, integer(1));
}

/// A dissipative Newtonian cell under an affine shear-and-dilation flow.
fn fluid_cell() -> crate::physics::fluid::control_volume::CellReturn {
    let volume = ControlVolume::new(
        GridCell::new(
            RatVec3::new(integer(1), rat(-1, 2), integer(0)),
            vec![0, 1, 2],
        )
        .unwrap(),
    )
    .unwrap();
    let flow = AffineFlow {
        velocity: RatVec3::new(integer(1), rat(1, 3), integer(-2)),
        gradient: RatMat3::new([
            [rat(1, 2), integer(1), integer(0)],
            [integer(0), rat(-1, 4), rat(2, 3)],
            [integer(1), integer(0), integer(0)],
        ]),
    };
    volume.cell_return(
        &rat(3, 2),
        &flow,
        &integer(2),
        &NewtonianMaterial::new(rat(1, 2), rat(1, 5)),
    )
}

/// **Fluid → heat, end to end** (Lean `ViscousPort.cell_port_join`, `ViscousWork.ofFluid`,
/// `Fluid/ControlVolume.cell_heat_port`): a control volume's return hands its viscous heat to the
/// thermal port, the exchange carries it into the pair, and the internal energy the pair gains over
/// the tick is `h` times the fluid cell's mechanical deficit, traction power minus pressure work,
/// read from the face tractions. The fluid's own kinetic-energy change needs the time advance
/// (#62).
#[test]
fn fluid_viscous_heat_enters_the_thermal_exchange_and_closes_the_joined_first_law() {
    let fluid = fluid_cell();
    assert!(fluid.mechanical_deficit() > Rat::zero());
    let work = ViscousWork::received(&fluid.heat).unwrap();
    let cells = [cell(integer(2), integer(9)), cell(integer(4), integer(4))];
    let tick = rat(1, 8);
    let step = exchange(
        &cells,
        &Contact::new(rat(1, 3)).unwrap(),
        &tick,
        &[work.clone(), ViscousWork::none()],
    )
    .unwrap();
    let gained =
        (step.next[0].energy() - cells[0].energy()) + (step.next[1].energy() - cells[1].energy());
    assert_eq!(gained, &tick * fluid.mechanical_deficit());
    let port = work
        .receive(&cells[0].at(cells[0].energy() - &step.heat).unwrap(), &tick)
        .unwrap();
    assert!(port.energy_residual(&fluid, &tick).is_zero());
    assert_eq!(port.next, step.next[0]);
    // A port fed a different cell's heat does not close this cell's first law.
    let other = ViscousWork::new(fluid.mechanical_deficit() + integer(1)).unwrap();
    let wrong = other.receive(&cells[0], &tick).unwrap();
    assert!(!wrong.energy_residual(&fluid, &tick).is_zero());
}

/// `Holon/Conformance.mediumHolon`, `diffusion_dissipates`, `Holon/Element.backwardEuler_balance`:
/// the contact is a Holon, the diffusion medium on the internal energies with storage `diag(1/C)`
/// and resistance `κ` times the Laplacian. Its midpoint advance balances exactly and keeps the
/// first law `ΣU` (plus the port work); its backward-Euler advance carries the retired diffusion
/// receipt's balance, with the defect `−½⟨ΔU, QΔU⟩`; the exchange tick is the explicit step of the
/// same medium, `U⁺ = U + h(−M T + W)`.
#[test]
fn the_contact_is_a_diffusion_holon_and_the_exchange_its_explicit_step() {
    let cells = [cell(integer(2), integer(10)), cell(integer(3), integer(3))];
    let contact = Contact::new(rat(1, 2)).unwrap();
    let holon = contact.holon(&cells).unwrap();
    let tick = rat(1, 4);
    let work = [rat(1, 3), Rat::zero()];
    let law = ReferenceHolon::new(holon.clone(), tick.clone(), Scheme::Midpoint).unwrap();
    let state = HolonState::new(vec![integer(10), integer(3)]);
    let advance = check_exact_advance(&law, &state, &work).unwrap();
    let reached = &advance.state.configuration;
    assert_eq!(
        &reached[0] + &reached[1],
        integer(13) + &tick * rat(1, 3),
        "the medium keeps the first law"
    );
    assert!(advance.balance.dissipated > Rat::zero());
    assert_eq!(law.holon(), &holon);
    // Backward Euler: the retired diffusion receipt's balance, source work, conductive
    // dissipation and the step defect, exact.
    let implicit = ReferenceHolon::new(holon.clone(), tick.clone(), Scheme::BackwardEuler).unwrap();
    let step_back = check_exact_advance(&implicit, &state, &work).unwrap();
    let change: Vec<Rat> = step_back
        .state
        .configuration
        .iter()
        .zip(&state.configuration)
        .map(|(after, before)| after - before)
        .collect();
    let defect = -(&change[0] * &change[0] / cells[0].capacity()
        + &change[1] * &change[1] / cells[1].capacity())
        / integer(2);
    assert!(!defect.is_zero());
    assert_eq!(step_back.balance.discretization_defect, defect);
    assert_eq!(
        &step_back.state.configuration[0] + &step_back.state.configuration[1],
        integer(13) + &tick * rat(1, 3)
    );
    // The exchange is the explicit step of the same medium.
    let step = exchange(
        &cells,
        &contact,
        &tick,
        &[
            ViscousWork::new(work[0].clone()).unwrap(),
            ViscousWork::none(),
        ],
    )
    .unwrap();
    let temperature = vec![cells[0].temperature(), cells[1].temperature()];
    let resistive = holon
        .port_holon()
        .resistance()
        .resistance()
        .apply(&temperature)
        .unwrap();
    for side in 0..2 {
        assert_eq!(
            step.next[side].energy(),
            &(cells[side].energy() + &tick * (&work[side] - &resistive[side]))
        );
    }
}

/// `Physics/Thermal/ViscousPort.withdrawn_work_lowers_entropy`: a port that withdraws work is not
/// viscous heating and is refused.
#[test]
fn withdrawn_work_is_refused() {
    assert_eq!(
        ViscousWork::new(integer(-1)),
        Err(ThermalError::WithdrawnWork { power: integer(-1) })
    );
}

// ---------------------------------------------------------------------------------------------
// The neck
// ---------------------------------------------------------------------------------------------

/// `Physics/Thermal/Schnakenberg.neckProduction_eq_zero_iff`, `term_pos_iff_certificate_pos`: the
/// neck produces exactly when its rational certificate is positive, and is balanced exactly when
/// its production form vanishes.
#[test]
fn a_neck_produces_exactly_when_it_is_unbalanced() {
    let flow = |f: i64, b: i64| JunctionFlow::new(integer(f), integer(b)).unwrap();
    let unbalanced = NeckProduction::across(vec![flow(3, 1), flow(2, 2), flow(1, 4)]).unwrap();
    assert_eq!(unbalanced.certificate(), integer(4) + rat(9, 4));
    assert!(!unbalanced.is_balanced());
    assert!(!unbalanced.production().is_zero());
    let balanced = NeckProduction::across(vec![flow(2, 2), flow(5, 5)]).unwrap();
    assert!(balanced.is_balanced());
    assert!(balanced.production().is_zero());
    assert!(balanced.certificate().is_zero());
}

/// `Physics/Thermal/Schnakenberg.twoCell_is_neck`: the two-cell production
/// `κ(a − b)(log a − log b)` is the neck of flows `κa`, `κb`: flux times the log-ratio drop.
#[test]
fn the_two_cell_exchange_is_a_one_junction_neck() {
    let (kappa, a, b) = (integer(3), integer(2), integer(5));
    let neck =
        NeckProduction::across(vec![JunctionFlow::new(&kappa * &a, &kappa * &b).unwrap()]).unwrap();
    let two_cell = log2(&a).minus(&log2(&b)).scaled(&(&kappa * (&a - &b)));
    assert_eq!(neck.production(), &two_cell);
}

/// `Physics/Thermal/Schnakenberg.epochProduction_eq_cut_add_interior`,
/// `cutProduction_le_epochProduction`: the rotation's cut at `{0}` produces `2/9` bits of its
/// `1/3`; the remaining `1/9` is the junction inside the other side.
#[test]
fn a_cut_carries_at_most_the_epoch_production() {
    let rotation = rotation();
    let law = vec![rat(1, 3); 3];
    let cut = cut_production(&rotation, &law, &[0]).unwrap();
    let epoch = rotation.epoch_production(&law).unwrap();
    assert_eq!(cut.production(), &log2(&integer(2)).scaled(&rat(2, 9)));
    assert_eq!(&epoch, &log2(&integer(2)).scaled(&rat(1, 3)));
    let inside = cut_production(&rotation, &law, &[0, 1]).unwrap();
    assert_eq!(inside.production(), cut.production());
    // A two-cell chain has no interior: its cut is its whole production.
    let two = chain(vec![vec![rat(1, 3), rat(2, 3)], vec![rat(1, 2), rat(1, 2)]]);
    let law2 = vec![rat(1, 2), rat(1, 2)];
    assert_eq!(
        cut_production(&two, &law2, &[0]).unwrap().production(),
        &two.epoch_production(&law2).unwrap()
    );
}

/// A section is a set of states: a repeated state would count its junctions twice, and a state
/// outside the chain would be silently dropped; both are refused.
#[test]
fn a_cut_refuses_a_repeated_or_outside_state() {
    let rotation = rotation();
    let law = vec![rat(1, 3); 3];
    assert_eq!(
        cut_production(&rotation, &law, &[0, 0]),
        Err(ThermalError::RepeatedCell { cell: 0 })
    );
    assert_eq!(
        cut_production(&rotation, &law, &[0, 99]),
        Err(ThermalError::Shape {
            what: "section state below the chain's state count",
            expected: 3,
            found: 99,
        })
    );
    // Order does not matter: the section is its set.
    assert_eq!(
        cut_production(&rotation, &law, &[1, 0])
            .unwrap()
            .production(),
        cut_production(&rotation, &law, &[0, 1])
            .unwrap()
            .production()
    );
}

// ---------------------------------------------------------------------------------------------
// The time and entropy axes (#5)
// ---------------------------------------------------------------------------------------------

/// `Physics/Thermal/ChainAxes.path_detailedBalance`, `path_no_arrow`: the stationary law of an
/// open chain is reversible, carries no current and produces nothing, although its entropy
/// coordinate is not flat.
#[test]
fn an_open_chain_has_no_stationary_arrow() {
    let open = OrientedChain::open(birth_death(), 1).unwrap();
    let law = open.chain().stationary_law().unwrap();
    assert_eq!(law, open.chain().reversible_law().unwrap());
    assert!(open.current(&law).unwrap().is_zero());
    assert!(open.production(&law).unwrap().is_zero());
    assert!(open.cycle_production(&law).unwrap().is_zero());
    assert!(open.chain().epoch_production(&law).unwrap().is_zero());
    assert_eq!(open.turn().unwrap(), Rat::one());
    assert_ne!(open.coordinate(3).unwrap(), Rat::one());
    // A chain that skips a cell is not an open chain.
    assert_eq!(
        OrientedChain::open(rotation(), 0),
        Err(ThermalError::NotNearestNeighbour { from: 0, to: 2 })
    );
}

/// Review probe P1: on the open chain `[[1/2, 1/2, 0], [1/4, 1/4, 1/2], [0, 2/3, 1/3]]` the law
/// `(8/19, 8/19, 3/19)` carries the equal junction nets `2/19` but is not stationary (the end cells
/// gain and lose). The current is refused there, and the production is Schnakenberg's across the
/// junctions, the chain's epoch production, which is not zero.
#[test]
fn a_producing_open_chain_is_not_read_as_stationary() {
    let open = OrientedChain::open(
        chain(vec![
            vec![rat(1, 2), rat(1, 2), Rat::zero()],
            vec![rat(1, 4), rat(1, 4), rat(1, 2)],
            vec![Rat::zero(), rat(2, 3), rat(1, 3)],
        ]),
        0,
    )
    .unwrap();
    let law = vec![rat(8, 19), rat(8, 19), rat(3, 19)];
    for flow in open.junction_flows(&law).unwrap() {
        assert_eq!(flow.net(), rat(2, 19));
    }
    assert_eq!(
        open.current(&law),
        Err(ThermalError::NotStationary { cell: 0 })
    );
    let production = open.production(&law).unwrap();
    assert!(!production.is_zero());
    assert_eq!(production, open.chain().epoch_production(&law).unwrap());
    assert_eq!(
        &production,
        NeckProduction::across(open.junction_flows(&law).unwrap())
            .unwrap()
            .production()
    );
    // At the stationary law the same chain is balanced.
    let stationary = open.chain().stationary_law().unwrap();
    assert!(open.production(&stationary).unwrap().is_zero());
}

/// `Physics/Thermal/ChainAxes.ring_one_current`, `stationary_ringProduction_eq`,
/// `neckProduction_ring_eq`, `cycleAffinity_law_free`, `current_affinity_sign`: at the stationary
/// law a ring carries one current `J`, and its Schnakenberg production is `J · log turn`, the
/// epoch production of `PathReversal`; `J` and the turn's log have one sign.
#[test]
fn a_ring_produces_its_current_times_its_cycle_affinity() {
    for ring in [rotation(), lazy_ring()] {
        let oriented = OrientedChain::ring(ring).unwrap();
        let law = oriented.chain().stationary_law().unwrap();
        let current = oriented.current(&law).unwrap();
        let turn = oriented.turn().unwrap();
        assert!(current > Rat::zero() && turn > Rat::one());
        assert_eq!(
            oriented.production(&law).unwrap(),
            oriented.chain().epoch_production(&law).unwrap()
        );
        assert_eq!(
            oriented.cycle_production(&law).unwrap(),
            oriented.production(&law).unwrap()
        );
        // The turn is the law-free product of the medium's affinities.
        let mut product = Rat::one();
        for flow in oriented.junction_flows(&law).unwrap() {
            product *= flow.ratio();
        }
        assert_eq!(product, turn);
    }
}

/// `Physics/Thermal/ChainAxes.current_lt_forward`, `production_le_junction`, `neckFlow`,
/// `production_le_neck`: every junction's forward flow bounds the current, and the neck, the
/// junction of least forward flow, gives the sharpest bound; it need not be the carry section.
#[test]
fn the_neck_bounds_the_current() {
    let oriented = OrientedChain::ring(lazy_ring()).unwrap();
    let law = oriented.chain().stationary_law().unwrap();
    let current = oriented.current(&law).unwrap();
    let flows = oriented.junction_flows(&law).unwrap();
    for flow in &flows {
        assert!(current < *flow.forward());
    }
    let neck = flows
        .iter()
        .map(|flow| flow.forward().clone())
        .min()
        .expect("a ring has junctions");
    assert!(current < neck);
}

/// `Physics/Thermal/ChainAxes.ring_reversal`: reflecting the ring's orientation inverts the turn
/// and negates the current; the production is unchanged.
#[test]
fn reversing_the_orientation_negates_both_axes_and_keeps_the_production() {
    let ring = lazy_ring();
    let n = ring.states();
    let reflect = |i: usize| n - 1 - i;
    let reflected = chain(
        (0..n)
            .map(|i| {
                (0..n)
                    .map(|j| ring.probability(reflect(i), reflect(j)))
                    .collect()
            })
            .collect(),
    );
    let forward = OrientedChain::ring(ring).unwrap();
    let backward = OrientedChain::ring(reflected).unwrap();
    let law = forward.chain().stationary_law().unwrap();
    let reflected_law: Vec<Rat> = (0..n).map(|i| law[reflect(i)].clone()).collect();
    assert_eq!(backward.turn().unwrap(), forward.turn().unwrap().recip());
    assert_eq!(
        backward.current(&reflected_law).unwrap(),
        -forward.current(&law).unwrap()
    );
    assert_eq!(
        backward.production(&reflected_law).unwrap(),
        forward.production(&law).unwrap()
    );
}

/// `Physics/Thermal/ChainAxes.entropy_reading`, `cycle_reading`: along every aeon the heat is the
/// entropy coordinate's change times the turn to the power of the signed epochs at the carry
/// junction.
#[test]
fn the_time_and_entropy_axes_cross_at_the_carry_section() {
    let oriented = OrientedChain::ring(lazy_ring()).unwrap();
    let walks: [&[usize]; 4] = [
        &[0, 1, 2, 3, 0, 1, 2, 3, 0, 1],
        &[2, 1, 1, 0, 3, 3, 2, 3, 0],
        &[3, 0, 3, 0, 1, 0, 3, 2],
        &[1, 2, 3, 0, 1],
    ];
    for walk in walks {
        let aeon = oriented.chain().walk(walk).unwrap();
        let reading = oriented.axes(&aeon).unwrap();
        assert!(reading.crosses(), "walk {walk:?}");
    }
    // A cycle that winds twice reads exactly the turn squared.
    let twice = oriented.chain().walk(&[0, 1, 2, 3, 0, 1, 2, 3, 0]).unwrap();
    let reading = oriented.axes(&twice).unwrap();
    assert_eq!(reading.longitudinal, BigInt::from(2));
    assert_eq!(reading.state, Rat::one());
    assert_eq!(
        reading.entropy,
        oriented.turn().unwrap() * oriented.turn().unwrap()
    );
    // On an open chain the turn is one: the entropy is the coordinate's change alone.
    let open = OrientedChain::open(birth_death(), 1).unwrap();
    let aeon = open.chain().walk(&[0, 1, 2, 1, 2, 3, 2]).unwrap();
    let reading = open.axes(&aeon).unwrap();
    assert!(reading.crosses());
    assert_eq!(reading.entropy, reading.state);
}

/// The longitudinal rate is the current: over one epoch from the stationary law, the mean signed
/// crossing of the carry section is `J₊ − J₋ = J` there.
#[test]
fn the_mean_signed_epoch_at_the_carry_section_is_the_current() {
    let oriented = OrientedChain::ring(lazy_ring()).unwrap();
    let law = oriented.chain().stationary_law().unwrap();
    let neck = oriented.carry_section();
    let mut mean = Rat::zero();
    for from in 0..oriented.cells() {
        for to in 0..oriented.cells() {
            if oriented.chain().probability(from, to).is_zero() {
                continue;
            }
            let aeon = oriented.chain().walk(&[from, to]).unwrap();
            let forward = epochs(&aeon, |step| *step == neck).flux();
            let backward =
                epochs(&aeon, |step| step.from == neck.to && step.to == neck.from).flux();
            let signed = Rat::from_integer(forward - backward);
            mean += oriented.chain().path_law(&law, &aeon).unwrap() * signed;
        }
    }
    assert_eq!(mean, oriented.current(&law).unwrap());
}

/// `Physics/Thermal/ChainAxes.backward_step_reads_negative`: one step against the current reads a
/// heat ratio below one; the entropy of a single aeon is not monotone.
#[test]
fn one_aeon_can_read_negative_entropy() {
    let oriented = OrientedChain::ring(rotation()).unwrap();
    let back = oriented.chain().walk(&[1, 0]).unwrap();
    let reading = oriented.axes(&back).unwrap();
    assert_eq!(reading.entropy, rat(1, 2));
    assert!(reading.entropy < Rat::one());
    assert!(reading.crosses());
}
