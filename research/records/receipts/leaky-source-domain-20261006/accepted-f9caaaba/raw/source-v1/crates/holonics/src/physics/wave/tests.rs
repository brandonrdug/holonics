//! One test per law and one per counterexample of the wave instance.

use num_traits::{One, Zero};

use super::*;
use crate::holon::parametron::Carrier;
use crate::ratio::{GaussianRat, Rat, integer, rat};

fn amplitude(re: i64, im: i64) -> GaussianRat {
    GaussianRat::from_i64(re, im)
}

/// A uniform open chain of `nodes` nodes.
fn open_chain(nodes: usize, c: Rat, g: Rat, l: Rat, h: Rat) -> WaveChain {
    let incidence = Incidence::open_chain(nodes).unwrap();
    let material = WaveMaterial::uniform(&incidence, &c, &g, &l).unwrap();
    WaveChain::new(incidence, material, h).unwrap()
}

/// The unit impulse at node `at`, no current.
fn impulse(chain: &WaveChain, at: usize) -> WaveState {
    let mut state = WaveState::rest(chain.incidence());
    let mut voltage = state.voltage().to_vec();
    voltage[at] = Rat::one();
    state = WaveState::new(voltage, state.current().to_vec());
    state
}

/// The nodes and junctions of a state that are not zero.
fn support(state: &WaveState) -> (Vec<usize>, Vec<usize>) {
    let nodes = (0..state.voltage().len())
        .filter(|i| !state.voltage()[*i].is_zero())
        .collect();
    let junctions = (0..state.current().len())
        .filter(|e| !state.current()[*e].is_zero())
        .collect();
    (nodes, junctions)
}

// ---------------------------------------------------------------------------------------------
// Interference
// ---------------------------------------------------------------------------------------------

/// `Physics/Wave/Interference.intensity_eq`: `|Σu|² = Σ|u|² + 2 Re Σ_(j<k) ū_j u_k`.
#[test]
fn the_coherent_intensity_is_the_incoherent_reading_plus_the_cross_terms() {
    let paths = [
        amplitude(1, 2),
        GaussianRat::new(rat(-3, 2), rat(1, 3)),
        amplitude(0, -1),
    ];
    let joined = interfere(&paths);
    assert_eq!(joined.intensity, &joined.incoherent + &joined.cross);
    assert_eq!(joined.coherent, GaussianRat::new(rat(-1, 2), rat(4, 3)));
    assert_eq!(joined.intensity, rat(1, 4) + rat(16, 9));
}

/// `Physics/Wave/Interference.opposite_amplitudes_cancel`: `1 + (−1) = 0` must not become
/// `|1|² + |−1|² = 2`.
#[test]
fn opposite_amplitudes_cancel_before_the_intensity_is_read() {
    let joined = interfere(&[amplitude(1, 0), amplitude(-1, 0)]);
    assert!(joined.intensity.is_zero());
    assert_eq!(joined.incoherent, integer(2));
    assert_eq!(joined.cross, integer(-2));
}

/// `Physics/Wave/Interference.coherent_not_a_function_of_incoherent`: one incoherent reading,
/// two coherent intensities.
#[test]
fn the_coherent_intensity_is_not_a_function_of_the_incoherent_reading() {
    let reinforce = interfere(&[amplitude(1, 0), amplitude(1, 0)]);
    let cancel = interfere(&[amplitude(1, 0), amplitude(-1, 0)]);
    assert_eq!(reinforce.incoherent, cancel.incoherent);
    assert_eq!(reinforce.intensity, integer(4));
    assert!(cancel.intensity.is_zero());
}

/// `Physics/Wave/Interference.common_phase_invariant`, `incoherent_phase_blind` and
/// `relative_phase_moves_intensity`: only relative phase is read, and only by the coherent
/// receiver.
#[test]
fn only_the_coherent_receiver_reads_relative_phase() {
    let paths = [amplitude(2, 1), amplitude(-1, 3)];
    let turn = Carrier::at(&rat(1, 3));
    let common: Vec<GaussianRat> = paths.iter().map(|u| u.mul(&turn.as_gaussian())).collect();
    assert_eq!(interfere(&common).intensity, interfere(&paths).intensity);

    let equal = [amplitude(1, 0), amplitude(1, 0)];
    let half_turned = [
        equal[0].clone(),
        equal[1].mul(&Carrier::sheet(true).as_gaussian()),
    ];
    assert_eq!(
        interfere(&equal).incoherent,
        interfere(&half_turned).incoherent
    );
    assert_eq!(interfere(&equal).intensity, integer(4));
    assert!(interfere(&half_turned).intensity.is_zero());
}

// ---------------------------------------------------------------------------------------------
// Propagation
// ---------------------------------------------------------------------------------------------

/// `Physics/Wave/Telegrapher.step_is_the_telegrapher`: the tick is the discretized law, flow
/// inertia on the junctions and storage with midpoint leakage and source on the nodes.
#[test]
fn a_tick_is_the_discretized_telegrapher_law() {
    let incidence = Incidence::ring(4).unwrap();
    let material = WaveMaterial::new(
        vec![integer(2), rat(3, 2), integer(1), rat(5, 4)],
        vec![rat(1, 2), Rat::zero(), rat(1, 3), integer(1)],
        vec![integer(1), rat(2, 3), integer(3), rat(1, 2)],
    )
    .unwrap();
    let chain = WaveChain::new(incidence, material, rat(1, 3)).unwrap();
    let state = WaveState::new(
        vec![integer(1), rat(-1, 2), integer(2), rat(1, 5)],
        vec![rat(1, 4), integer(-1), Rat::zero(), rat(2, 3)],
    );
    let source = vec![integer(1), Rat::zero(), rat(-1, 2), Rat::zero()];
    let next = chain.propagate(&state, &source).unwrap().next;
    let h = chain.tick().clone();
    let drop = chain.incidence().grad(state.voltage()).unwrap();
    for (e, drop) in drop.iter().enumerate() {
        assert_eq!(
            &chain.material().inductance()[e] * (&next.current()[e] - &state.current()[e]),
            -&h * drop
        );
    }
    let inflow = chain.incidence().div(next.current()).unwrap();
    for i in 0..4 {
        let c = &chain.material().capacitance()[i];
        let g = &chain.material().leakage()[i];
        assert_eq!(
            c * (&next.voltage()[i] - &state.voltage()[i]),
            &h * &inflow[i] - &h * g * (&next.voltage()[i] + &state.voltage()[i]) / integer(2)
                + &h * &source[i]
        );
    }
}

/// `Physics/Wave/Energy.energy_balance`: the staggered energy changes by the source power minus
/// the leakage heat, with no residual, over many ticks on an open chain and a ring.
#[test]
fn every_tick_balances_its_energy_exactly() {
    for incidence in [
        Incidence::open_chain(5).unwrap(),
        Incidence::ring(5).unwrap(),
    ] {
        let junctions = incidence.junctions().len();
        let material = WaveMaterial::new(
            vec![integer(1), integer(2), rat(3, 2), integer(1), rat(1, 2)],
            vec![rat(1, 3), Rat::zero(), rat(1, 2), rat(1, 5), Rat::zero()],
            (0..junctions).map(|e| rat(2 + e as i64, 3)).collect(),
        )
        .unwrap();
        let chain = WaveChain::new(incidence, material, rat(1, 2)).unwrap();
        let mut state = WaveState::new(
            vec![integer(1), rat(-2, 3), Rat::zero(), rat(1, 2), integer(-1)],
            (0..junctions).map(|e| rat(e as i64 - 1, 4)).collect(),
        );
        for tick in 0..6 {
            let source: Vec<Rat> = (0..5).map(|i| rat((i + tick) as i64 % 3 - 1, 2)).collect();
            let step = chain.propagate(&state, &source).unwrap();
            assert!(
                step.balance.is_exact(),
                "residual {}",
                step.balance.residual
            );
            state = step.next;
        }
    }
}

/// `Physics/Wave/Energy.energy_nonincreasing`, `energy_strictly_decreasing`: without a source,
/// leakage only removes energy, strictly while a leaking node carries voltage.
#[test]
fn leakage_only_removes_energy() {
    let chain = open_chain(4, integer(1), rat(1, 2), integer(1), rat(1, 2));
    let mut state = impulse(&chain, 1);
    for _ in 0..5 {
        let before = chain.energy(&state).unwrap();
        let step = chain.propagate(&state, &vec![Rat::zero(); 4]).unwrap();
        assert!(step.balance.dissipated > Rat::zero());
        assert!(chain.energy(&step.next).unwrap() < before);
        state = step.next;
    }
}

/// `Physics/Wave/Telegrapher.change_moves_one_cell_per_tick`: two states that differ at one node
/// differ only within `n` nodes of it after `n` ticks, whatever the material.
#[test]
fn a_change_moves_at_most_one_cell_per_tick() {
    let incidence = Incidence::open_chain(21).unwrap();
    let material = WaveMaterial::new(
        (0..21).map(|i| rat(1 + i % 3, 2)).collect(),
        (0..21).map(|i| rat(i % 2, 3)).collect(),
        (0..20).map(|e| rat(2 + e % 4, 3)).collect(),
    )
    .unwrap();
    let chain = WaveChain::new(incidence, material, rat(1, 4)).unwrap();
    let base = WaveState::new(
        (0..21).map(|i| rat(i - 10, 7)).collect(),
        (0..20).map(|e| rat(e % 5, 3)).collect(),
    );
    let mut voltage = base.voltage().to_vec();
    voltage[10] += Rat::one();
    let changed = WaveState::new(voltage, base.current().to_vec());
    for n in 0..=9 {
        let difference = chain
            .run(&changed, n)
            .unwrap()
            .difference(&chain.run(&base, n).unwrap());
        let (nodes, junctions) = support(&difference);
        assert!(nodes.iter().all(|i| 10 - n <= *i && *i <= 10 + n));
        assert!(junctions.iter().all(|e| 10 - n <= *e && *e < 10 + n));
        // The cone is attained: the change reaches both edges.
        assert!(nodes.contains(&(10 - n)) && nodes.contains(&(10 + n)));
    }
}

/// `Physics/Wave/Telegrapher.impulse_front_damped`: the leakage multiplies the lossless front by
/// `2C/(2C + hG)` per tick, never zero, on the same cone.
#[test]
fn loss_damps_the_front_but_never_speeds_it() {
    let (c, l, h) = (integer(2), integer(1), rat(1, 2));
    let g = integer(3);
    let lossy = open_chain(21, c.clone(), g.clone(), l.clone(), h.clone());
    let lossless = open_chain(21, c.clone(), Rat::zero(), l, h.clone());
    let ratio = damping(&c, &g, &h);
    assert_eq!(ratio, rat(8, 11));
    assert_eq!(damping(&c, &Rat::zero(), &h), Rat::one());
    for n in 1..=8 {
        let a = lossy.run(&impulse(&lossy, 10), n).unwrap();
        let b = lossless.run(&impulse(&lossless, 10), n).unwrap();
        assert_eq!(support(&a).0.first(), support(&b).0.first());
        assert_eq!(support(&a).0.last(), support(&b).0.last());
        let front = &a.voltage()[10 + n];
        assert!(!front.is_zero());
        assert_eq!(
            *front,
            num_traits::pow(ratio.clone(), n) * &b.voltage()[10 + n]
        );
        assert_eq!(
            *front,
            num_traits::pow(lossy.front_factor(10, 11).unwrap(), n)
        );
    }
}

/// `Physics/Wave/Energy.chain_energy_lower_bound`, `operator_bound_of_rows`, `energy_lower_bound`:
/// the uniform open chain's Courant bound is `4/(LC)`, and under `h² ≤ LC` the staggered energy
/// sits above its floor.
#[test]
fn the_courant_condition_bounds_the_staggered_energy_below() {
    let chain = open_chain(6, integer(2), rat(1, 4), integer(3), integer(2));
    assert_eq!(chain.courant_bound(), rat(4, 6));
    assert!(chain.satisfies_courant());
    let state = WaveState::new(
        vec![
            integer(1),
            integer(-1),
            integer(2),
            rat(1, 2),
            Rat::zero(),
            integer(-3),
        ],
        vec![integer(2), integer(-1), rat(1, 3), integer(1), rat(-5, 2)],
    );
    let floor = chain.energy_floor(&state).unwrap();
    assert!(floor >= Rat::zero());
    assert!(chain.energy(&state).unwrap() >= floor);
}

/// `Physics/Wave/Energy.energy_lower_bound`, `energy_definite`: under the strict Courant
/// condition the floor keeps the current's square, so a state with no voltage and a nonzero current
/// has positive energy, and the staggered energy is a norm on `(V, I)`.
#[test]
fn the_strict_courant_condition_makes_the_staggered_energy_a_norm() {
    let chain = open_chain(4, integer(2), Rat::zero(), integer(3), integer(1));
    assert!(square(chain.tick()) * chain.courant_bound() < integer(4));
    let current_only = WaveState::new(
        vec![Rat::zero(); 4],
        vec![integer(1), Rat::zero(), rat(-1, 2)],
    );
    let floor = chain.energy_floor(&current_only).unwrap();
    assert!(floor > Rat::zero());
    assert_eq!(chain.energy(&current_only).unwrap(), floor);
    let mixed = WaveState::new(
        vec![integer(1), rat(-2, 3), Rat::zero(), integer(2)],
        vec![rat(1, 3), integer(-1), integer(2)],
    );
    let floor = chain.energy_floor(&mixed).unwrap();
    assert!(floor > Rat::zero() && chain.energy(&mixed).unwrap() >= floor);
    assert!(
        chain
            .energy_floor(&WaveState::rest(chain.incidence()))
            .unwrap()
            .is_zero()
    );
}

/// `Holon/Conformance.medium_rate_agrees`: the field is a Holon, the telegrapher medium on the
/// charges and fluxes. Its midpoint advance balances exactly in the storage energy
/// `½ΣCV² + ½ΣLI²`; the staggered tick is a different integrator, whose exact balance is the
/// staggered energy and which does not conserve the storage energy of a lossless field.
#[test]
fn the_field_is_a_telegrapher_holon_and_the_staggered_tick_a_different_integrator() {
    use crate::holon::HolonState;
    use crate::holon::conformance::check_exact_advance;
    use crate::holon::law::{ReferenceHolon, Scheme};

    let incidence = Incidence::ring(4).unwrap();
    let material = WaveMaterial::new(
        vec![integer(2), integer(1), rat(3, 2), integer(1)],
        vec![rat(1, 4), Rat::zero(), rat(1, 2), Rat::zero()],
        vec![integer(1), integer(2), integer(1), rat(1, 2)],
    )
    .unwrap();
    let chain = WaveChain::new(incidence, material, rat(1, 3)).unwrap();
    let holon = chain.holon().unwrap();
    let state = WaveState::new(
        vec![integer(1), rat(-1, 2), Rat::zero(), integer(2)],
        vec![rat(1, 3), integer(-1), Rat::zero(), integer(1)],
    );
    let configuration = chain.configuration(&state).unwrap();
    let storage_energy = |state: &WaveState| {
        let stored: Rat = state
            .voltage()
            .iter()
            .zip(chain.material().capacitance())
            .map(|(v, c)| c * square(v))
            .sum();
        let flowing: Rat = state
            .current()
            .iter()
            .zip(chain.material().inductance())
            .map(|(i, l)| l * square(i))
            .sum();
        half() * (stored + flowing)
    };
    assert_eq!(
        holon.port_holon().storage_energy(&configuration).unwrap(),
        storage_energy(&state)
    );
    let law = ReferenceHolon::new(holon, chain.tick().clone(), Scheme::Midpoint).unwrap();
    let source = vec![integer(1), Rat::zero(), rat(-1, 2), Rat::zero()];
    let advance = check_exact_advance(&law, &HolonState::new(configuration), &source).unwrap();
    assert!(advance.balance.dissipated > Rat::zero());
    // Lossless and unforced: the midpoint keeps the storage energy, the staggered tick keeps the
    // staggered energy, and the two are different quantities.
    let lossless = WaveChain::new(
        Incidence::ring(4).unwrap(),
        WaveMaterial::new(
            vec![integer(2), integer(1), rat(3, 2), integer(1)],
            vec![Rat::zero(); 4],
            vec![integer(1), integer(2), integer(1), rat(1, 2)],
        )
        .unwrap(),
        rat(1, 3),
    )
    .unwrap();
    let silent = vec![Rat::zero(); 4];
    let midpoint =
        ReferenceHolon::new(lossless.holon().unwrap(), rat(1, 3), Scheme::Midpoint).unwrap();
    let kept = check_exact_advance(
        &midpoint,
        &HolonState::new(lossless.configuration(&state).unwrap()),
        &silent,
    )
    .unwrap();
    assert!(kept.balance.stored_change.is_zero());
    let staggered = lossless.propagate(&state, &silent).unwrap();
    assert!(staggered.balance.stored_change.is_zero());
    assert_ne!(storage_energy(&staggered.next), storage_energy(&state));
}

/// `Physics/Wave/Energy.energy_negative_beyond_courant`: at `h = 2` on two unit nodes the
/// staggered energy of a nonzero state is `−1`.
#[test]
fn beyond_the_courant_bound_the_staggered_energy_is_not_a_norm() {
    let chain = open_chain(2, integer(1), Rat::zero(), integer(1), integer(2));
    assert_eq!(chain.courant_bound(), integer(2));
    assert!(!chain.satisfies_courant());
    let state = WaveState::new(vec![integer(1), integer(-1)], vec![integer(-2)]);
    assert_eq!(chain.energy(&state).unwrap(), integer(-1));
}

// ---------------------------------------------------------------------------------------------
// Radiation
// ---------------------------------------------------------------------------------------------

/// `Physics/Wave/Radiation.uniform_current_stationary`, `stationary_emits_nothing`: a uniform
/// circulating current with no voltage, the charge in uniform motion, is returned at every tick.
#[test]
fn uniform_motion_radiates_nothing() {
    let incidence = Incidence::ring(5).unwrap();
    let material = WaveMaterial::new(
        vec![integer(1), integer(2), rat(1, 2), integer(3), integer(1)],
        vec![rat(1, 2), Rat::zero(), integer(1), rat(1, 3), Rat::zero()],
        vec![integer(1), rat(3, 2), integer(2), rat(1, 2), integer(1)],
    )
    .unwrap();
    let chain = WaveChain::new(incidence, material, rat(1, 3)).unwrap();
    let moving = WaveState::new(vec![Rat::zero(); 5], vec![rat(7, 3); 5]);
    let silent = vec![Rat::zero(); 5];
    assert!(chain.is_stationary(&moving, &silent).unwrap());
    assert_eq!(chain.run(&moving, 12).unwrap(), moving);
}

/// `Physics/Wave/Radiation.radiation_is_the_change`, `receiver_reads_the_change`: the deviation
/// from a stationary configuration is the propagated change of the source; a receiver `w` nodes
/// away reads nothing through tick `w` and reads the change at tick `w + 1`.
#[test]
fn only_the_change_of_the_source_propagates() {
    let incidence = Incidence::ring(24).unwrap();
    let material = WaveMaterial::uniform(&incidence, &integer(1), &rat(1, 5), &integer(2)).unwrap();
    let chain = WaveChain::new(incidence, material, rat(1, 2)).unwrap();
    let stationary = WaveState::new(vec![Rat::zero(); 24], vec![rat(-3, 2); 24]);
    let silent = vec![Rat::zero(); 24];
    assert!(chain.is_stationary(&stationary, &silent).unwrap());
    let mut switched = silent.clone();
    switched[0] = rat(1, 3);
    let mut driven = stationary.clone();
    let mut response = WaveState::rest(chain.incidence());
    for tick in 1..=8 {
        driven = chain.propagate(&driven, &switched).unwrap().next;
        response = chain.propagate(&response, &switched).unwrap().next;
        let radiated = driven.difference(&stationary);
        assert_eq!(radiated, response);
        for w in 1..=8usize {
            let reading = &radiated.voltage()[w];
            if tick <= w {
                assert!(reading.is_zero(), "receiver {w} read before the front");
            } else if tick == w + 1 {
                assert!(!reading.is_zero(), "receiver {w} missed the front");
            }
        }
    }
}
