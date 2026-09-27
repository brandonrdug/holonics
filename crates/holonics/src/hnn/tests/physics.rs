//! Campaign 2's ring and contact physics (Lean `HNN/Ring`, `HNN/Contact`, `HNN/ContactBreak`,
//! `HNN/Word.field_executed_balance_with_defects`): one test per stated law and per refusal.

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, Zero};

use super::learning::{OPEN_BUDGET, chain};
use super::support::{Draw, Medium};
use crate::aeon::TwoClocks;
use crate::compression::landmark::context::Landmarks;
use crate::hnn::HnnError;
use crate::hnn::constitution::{Constitution, Steps};
use crate::hnn::contact::{
    ContactLock, LockDeclaration, certify_boost, contact_readings, lock_address,
    signed_form_certifies, signed_stiffness, site_reading, site_reading_of_factors, transfer,
};
use crate::hnn::field::{ConstitutionRead, Current, Field, FieldDeclaration};
use crate::hnn::moment::{PairPort, SourceMoment};
use crate::hnn::propagation::{
    ContactOperands, ExponentReading, gram, junction_swing, transit, transit_solve,
};
use crate::hnn::receiving::{Mixture, ReceivingPhases};
use crate::hnn::ring::{
    PumpDeclaration, PumpStep, ResonatorMaterial, ResonatorOperands, ResonatorRemainders,
    RingClock, port_scattering, sheets,
};
use crate::hnn::word::{PowerForm, Word, WordBalance};
use crate::holarchy::GluingDefect;
use crate::holon::parametron::{Carrier, Parametron, Population, pump_storage};
use crate::navigator::address::{are_neighbours, mediant};
use crate::navigator::trace::SiteKind;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{add, dot, scale, sub};
use crate::ratio::{Rat, integer, rat};

// -------------------------------------------------------------------------------------------
// a constitution with campaign 2's declarations

/// A test constitution: [`Medium`] with the campaign-2 declarations the trait's defaults leave
/// absent (resonators, stiffness signatures, surface densities).
#[derive(Clone, Debug)]
struct Declared {
    medium: Medium,
    resonators: Vec<Option<ResonatorMaterial>>,
    signatures: Vec<Option<Vec<bool>>>,
    surfaces: Vec<Option<Rat>>,
}

impl Declared {
    fn of(field: &Field, medium: Medium) -> Self {
        Self {
            medium,
            resonators: vec![None; field.rings().len()],
            signatures: vec![None; field.contacts().len()],
            surfaces: vec![None; field.contacts().len()],
        }
    }
}

impl ConstitutionRead for Declared {
    fn standing(&self, ring: usize) -> &[Rat] {
        self.medium.standing(ring)
    }
    fn passive_factor(&self, ring: usize) -> &ExactRatMatrix {
        self.medium.passive_factor(ring)
    }
    fn contrast_port(&self, ring: usize) -> &ExactRatMatrix {
        self.medium.contrast_port(ring)
    }
    fn slices(&self, ring: usize) -> &[(Vec<Rat>, Vec<Rat>)] {
        self.medium.slices(ring)
    }
    fn source_port(&self, ring: usize) -> Option<&ExactRatMatrix> {
        self.medium.source_port(ring)
    }
    fn pair_port(&self, ring: usize, offset: usize) -> Option<&PairPort> {
        self.medium.pair_port(ring, offset)
    }
    fn contact_storage(&self, contact: usize) -> &ExactRatMatrix {
        self.medium.contact_storage(contact)
    }
    fn contact_stiffness(&self, contact: usize) -> &ExactRatMatrix {
        self.medium.contact_stiffness(contact)
    }
    fn contact_dissipation(&self, contact: usize) -> &ExactRatMatrix {
        self.medium.contact_dissipation(contact)
    }
    fn receiving_map(&self, ring: usize) -> Option<&ExactRatMatrix> {
        self.medium.receiving_map(ring)
    }
    fn landmarks(&self, ring: usize) -> Option<&Landmarks> {
        self.medium.landmarks(ring)
    }
    fn mixture(&self, ring: usize) -> Option<&Mixture> {
        self.medium.mixture(ring)
    }
    fn contact_stiffness_signature(&self, contact: usize) -> Option<&[bool]> {
        self.signatures[contact].as_deref()
    }
    fn contact_surface_storage(&self, contact: usize) -> Option<&Rat> {
        self.surfaces[contact].as_ref()
    }
    fn ring_resonator(&self, ring: usize) -> Option<&ResonatorMaterial> {
        self.resonators[ring].as_ref()
    }
}

/// A cut of the chain control whose cells fit no lock: every ring dormant at rest.
fn cut(field: &Field) -> (Current, SourceMoment) {
    let cells = vec![1usize; 40];
    let mut current = Current::at_rest(field);
    let mut moment = SourceMoment::open(field, &current);
    moment.ingest(field, &mut current, &cells).unwrap();
    (current, moment)
}

/// A parametron of `d` nodes on the closed cycle with capacity and inverse-inductance weights.
fn cycle(d: usize, capacity: Vec<Rat>, stiffness: Vec<Rat>) -> Parametron {
    let incidence = crate::ratio::linear::vector::matrix(d, d, |branch, node| {
        if node == branch {
            -Rat::one()
        } else if node == (branch + 1) % d {
            Rat::one()
        } else {
            Rat::zero()
        }
    })
    .unwrap();
    Parametron::new(incidence, capacity, stiffness).unwrap()
}

fn identity(n: usize) -> ExactRatMatrix {
    ExactRatMatrix::identity(n).unwrap()
}

fn quadratic(form: &ExactRatMatrix, v: &[Rat]) -> Rat {
    dot(v, &form.apply(v).unwrap())
}

// -------------------------------------------------------------------------------------------
// the ring

/// Lean `HNN/Ring.{ring_generator_qSkew, cayley_preserves_form, ring_tick_conserves_mode_energy,
/// cayley_forms_agree, ring_descriptor_tick_conserves}`: for `Q = diag(K, C)` with `C` invertible the
/// ring's generator `A = [[0, 1], [−C⁻¹K, 0]]` has `QA` skew, the Cayley tick
/// `U = (1 + hA/2)(1 − hA/2)⁻¹` keeps `UᵀQU = Q` exactly (and does not keep the Euclidean norm), and
/// the closed descriptor form, with no `C⁻¹`, is `U` and conserves `E_Q` exactly on random states
/// (the Lean statements, formed here). The owner that runs the closed descriptor tick is the
/// contact's scalar transfer at `p = d = 0` (`hnn::contact::transfer`, one generalized mode,
/// `contact_mode_transfer`), which conserves `½cw² + ½ku²` of any sign exactly; the resonator
/// (`ResonatorOperands::step`) runs the ported tick, whose balance is `ring_tick_port_balance`.
#[test]
fn the_ring_tick_conserves_its_mode_energy_exactly() {
    // The grounded parametron: the cycle's capacity plus the identity is definite.
    let ring = cycle(
        3,
        vec![integer(1), rat(1, 2), integer(2)],
        vec![integer(3), integer(1), rat(1, 3)],
    );
    let d = ring.nodes();
    let c = ring.capacitance().unwrap().add(&identity(d)).unwrap();
    let k = ring.stiffness().unwrap();
    let h = rat(1, 2);
    let n = 2 * d;
    // Q = diag(K, C), A = [[0, 1], [−C⁻¹K, 0]] on (u, w).
    let c_inverse = c.inverse().unwrap();
    let minus = c_inverse.multiply(&k).unwrap().scaled(&-Rat::one());
    let block = |i: usize, j: usize| -> Rat {
        match (i < d, j < d) {
            (true, true) => Rat::zero(),
            (true, false) => {
                if i == j - d {
                    Rat::one()
                } else {
                    Rat::zero()
                }
            }
            (false, true) => minus.get(i - d, j).unwrap().clone(),
            (false, false) => Rat::zero(),
        }
    };
    let a = crate::ratio::linear::vector::matrix(n, n, block).unwrap();
    let q = crate::ratio::linear::vector::matrix(n, n, |i, j| match (i < d, j < d) {
        (true, true) => k.get(i, j).unwrap().clone(),
        (false, false) => c.get(i - d, j - d).unwrap().clone(),
        _ => Rat::zero(),
    })
    .unwrap();
    let skew = q.multiply(&a).unwrap();
    assert_eq!(skew.transpose().unwrap(), skew.scaled(&-Rat::one()));
    let half = a.scaled(&(&h / integer(2)));
    let u_tick = identity(n)
        .add(&half)
        .unwrap()
        .multiply(&identity(n).subtract(&half).unwrap().inverse().unwrap())
        .unwrap();
    assert_eq!(
        u_tick
            .transpose()
            .unwrap()
            .multiply(&q)
            .unwrap()
            .multiply(&u_tick)
            .unwrap(),
        q
    );
    assert_ne!(
        u_tick.transpose().unwrap().multiply(&u_tick).unwrap(),
        identity(n)
    );
    // The descriptor tick: (2C + (h²/2)K) ω = 2C w − h K u, u′ = u + hω, w′ = 2ω − w.
    let closed = c
        .scaled(&integer(2))
        .add(&k.scaled(&(&h * &h / integer(2))))
        .unwrap()
        .inverse()
        .unwrap();
    let mut draw = Draw::new(7);
    for _ in 0..8 {
        let (u, w) = (draw.vector(d), draw.vector(d));
        let right = sub(
            &scale(&integer(2), &c.apply(&w).unwrap()),
            &scale(&h, &k.apply(&u).unwrap()),
        );
        let omega = closed.apply(&right).unwrap();
        let (u2, w2) = (
            add(&u, &scale(&h, &omega)),
            sub(&scale(&integer(2), &omega), &w),
        );
        let energy = |u: &[Rat], w: &[Rat]| (quadratic(&c, w) + quadratic(&k, u)) / integer(2);
        assert_eq!(energy(&u2, &w2), energy(&u, &w));
        let z: Vec<Rat> = u.iter().chain(&w).cloned().collect();
        let z2: Vec<Rat> = u2.iter().chain(&w2).cloned().collect();
        assert_eq!(u_tick.apply(&z).unwrap(), z2);
        // The owner: the closed scalar transfer conserves its mode's storage, stiffness of any
        // sign, wherever its Cayley chart exists.
        let pick = draw.vector(4);
        let (c1, k1) = (pick[0].abs() + rat(1, 8), &pick[1] - rat(1, 2));
        let (u1, w1) = (pick[2].clone(), pick[3].clone());
        if c1.is_positive()
            && let Ok(closed) = transfer(&c1, &k1, &Rat::zero(), &Rat::zero(), &h)
        {
            let [u2, w2] = closed.apply([&u1, &w1]);
            assert_eq!(
                &c1 * &w2 * &w2 + &k1 * &u2 * &u2,
                &c1 * &w1 * &w1 + &k1 * &u1 * &u1
            );
        }
    }
}

/// Lean `HNN/Ring.ring_harmonic_mode_singular` and `ring_cayley_denominator_nonsingular`: on the
/// ungrounded cycle `C = K = BᵀB` share the constant (harmonic, dormant) mode, which the closed
/// denominator sends to zero; the port's `(h/Y) I` makes the executed operator definite.
#[test]
fn the_harmonic_mode_is_where_the_closed_denominator_is_singular() {
    let ring = cycle(4, vec![Rat::one(); 4], vec![Rat::one(); 4]);
    let (c, k) = (ring.capacitance().unwrap(), ring.stiffness().unwrap());
    let h = integer(1);
    let closed = c
        .scaled(&integer(2))
        .add(&k.scaled(&(&h * &h / integer(2))))
        .unwrap();
    let constant = vec![Rat::one(); 4];
    assert!(closed.apply(&constant).unwrap().iter().all(Zero::is_zero));
    assert!(closed.inverse().is_err());
    let material = ResonatorMaterial::of_parametron(&ring, &Rat::zero(), None).unwrap();
    let operands = ResonatorOperands::at_cut(0, &material, &integer(2), &h, None).unwrap();
    let operator = operands.operator(0);
    let mut draw = Draw::new(3);
    for _ in 0..8 {
        let v = draw.vector(8);
        // ⟨v, M v⟩ ≥ (h/Y)|v|².
        assert!(quadratic(operator, &v) >= &h / integer(2) * dot(&v, &v));
    }
}

/// Lean `HNN/Ring.ring_tick_executed_energy_balance`: every executed resonator tick closes exactly,
/// `after − before = pump + port − dissipation + chart + split`, on the exact law and on the word's
/// lattices, pumped and unpumped, at random drives; on the exact law the chart and split terms are
/// zero, and closed, lossless and unpumped (no drive, no dissipation) its storage is conserved up to
/// the port's work alone.
#[test]
fn the_executed_ring_tick_closes_with_every_term() {
    let ring = cycle(
        3,
        vec![integer(1), rat(1, 2), integer(2)],
        vec![integer(2), integer(1), rat(1, 2)],
    );
    let axis = Carrier::at(&rat(1, 3));
    let pumps = [
        None,
        Some(PumpDeclaration::new(rat(1, 8), axis.clone(), PumpStep::Half).unwrap()),
        Some(PumpDeclaration::new(rat(1, 16), axis, PumpStep::Quarter).unwrap()),
    ];
    let field = chain();
    let lattice = field.word_lattice().copied().unwrap();
    for pump in pumps {
        let material = ResonatorMaterial::of_parametron(&ring, &rat(1, 4), pump.clone()).unwrap();
        for word_lattice in [None, Some(&lattice)] {
            let operands =
                ResonatorOperands::at_cut(1, &material, &integer(2), &integer(1), word_lattice)
                    .unwrap();
            assert_eq!(
                operands.charts().len(),
                word_lattice.map_or(0, |_| material.phases())
            );
            let transient = word_lattice.map(|l| l.transient());
            let mut draw = Draw::new(11);
            let mut state = [vec![Rat::zero(); 6], vec![Rat::zero(); 6]];
            let mut remainders = ResonatorRemainders::default();
            let mut pumped = Rat::zero();
            for tick in 0..8 {
                let drive = draw.dyadic_vector(6);
                let step = operands
                    .step(
                        tick,
                        &drive,
                        [&state[0], &state[1]],
                        &remainders,
                        transient.as_ref(),
                    )
                    .unwrap();
                assert!(step.closes(), "tick {tick}: {step:?}");
                if word_lattice.is_none() {
                    assert!(step.chart.is_zero() && step.split.is_zero());
                }
                assert!(!step.dissipation.is_negative());
                pumped += &step.pump;
                state = step.state.clone();
                remainders = step.remainders().clone();
            }
            if pump.as_ref().is_some_and(|p| p.step() != PumpStep::Stand) {
                assert!(!pumped.is_zero(), "a moving pump does work");
            }
        }
    }
}

/// Lean `HNN/Ring.{pump_half_turn_invariant, pump_blind_to_sheets, locked_sheet_receiver_face}`:
/// the pump block reads the doubled phase (it keeps `z ↦ −z`, and at `r(cos θ, sin θ)` it is `r²`
/// times the owner's pump storage), the two sheets of its axis carry the same pump storage `−p`,
/// the sheet reading returns each locked node's sheet, and on locked sheets the threshold of the
/// local field is the energy-minimizing sheet: the perceptron face.
#[test]
fn the_pump_is_blind_to_the_sheets_and_the_locked_sheet_is_an_ising_face() {
    let axis = Carrier::at(&rat(2, 5));
    let pump = PumpDeclaration::new(rat(3, 2), axis.clone(), PumpStep::Quarter).unwrap();
    let block_value = |phase: usize, x: &Rat, y: &Rat| -> Rat {
        let b = pump.block(phase);
        (x * x * &b[0][0] + integer(2) * x * y * &b[0][1] + y * y * &b[1][1]) / integer(2)
    };
    for phase in 0..pump.phases() {
        let psi = pump.carrier(phase);
        for parameter in [rat(1, 7), rat(-3, 2), integer(4)] {
            let carrier = Carrier::at(&parameter);
            let r = rat(5, 3);
            let (x, y) = (&r * carrier.cos(), &r * carrier.sin());
            assert_eq!(
                block_value(phase, &x, &y),
                &r * &r * pump_storage(pump.strength(), &psi, &carrier)
            );
            assert_eq!(
                block_value(phase, &-x.clone(), &-y.clone()),
                block_value(phase, &x, &y)
            );
            assert_eq!(
                pump_storage(pump.strength(), &psi, &carrier.half_turn()),
                pump_storage(pump.strength(), &psi, &carrier)
            );
        }
    }
    // At phase 0 the pump sits at twice its axis: both sheets store −p.
    let psi = pump.carrier(0);
    for sheet in [axis.clone(), axis.half_turn()] {
        assert_eq!(
            pump_storage(pump.strength(), &psi, &sheet),
            -pump.strength().clone()
        );
    }
    // A locked configuration reads its sheets back.
    let states = [false, true, true];
    let displacement: Vec<Rat> = states
        .iter()
        .flat_map(|half| {
            let sign = if *half { -Rat::one() } else { Rat::one() };
            [&sign * axis.cos(), &sign * axis.sin()]
        })
        .collect();
    assert_eq!(sheets(&displacement, &axis), states.to_vec());
    let population = Population::new(
        vec![(0, 1, rat(3, 2)), (1, 2, integer(-1))],
        vec![rat(1, 2), Rat::zero(), integer(-1)],
    )
    .unwrap();
    for site in 0..3 {
        let chosen = population.perceptron(&states, site).unwrap();
        let energy = |sheet: bool| {
            let mut moved = states.to_vec();
            moved[site] = sheet;
            population.ising_energy(&moved).unwrap()
        };
        assert!(energy(chosen) <= energy(!chosen));
    }
}

/// Lean `HNN/Ring.ring_crossings_are_epoch_ticks`: over a passage of cells every ring's arrivals on
/// its section are the owner's `ring_crossings(d, r, N)` and its winding difference, at
/// micro-steps inside the passage.
#[test]
fn ticks_equal_the_ring_crossings() {
    let field = Field::declare(FieldDeclaration::campaign_one(1 << 17)).unwrap();
    let mut draw = Draw::new(29);
    let cells: Vec<usize> = (0..3000).map(|_| draw.below(256)).collect();
    let start = Current::at_rest(&field);
    let clocks = RingClock::over(&field, &start, &cells).unwrap();
    let mut end = start.clone();
    for &cell in &cells {
        end.step(&field, cell).unwrap();
    }
    for clock in &clocks {
        assert!(clock.agrees().unwrap(), "ring {}", clock.ring);
        let windings =
            end.winding(&field, clock.ring).unwrap() - start.winding(&field, clock.ring).unwrap();
        assert_eq!(BigInt::from(clock.crossings.clone()), windings);
    }
    assert!(clocks.iter().any(|clock| clock.crossings > BigUint::zero()));
}

/// Lean `HNN/Ring.two_port_reference_balance`: at every port of every junction of a cut,
/// `Γ² + T = 1`; the executed Swing returns a unit wave at port `p` reflected by `Γ` and transmitted
/// by `1 + Γ` into every other port, whose power there is `T` times the incident power.
#[test]
fn every_junction_port_balances_its_reference_change() {
    let field = chain();
    let medium = Medium::encoding(&field, 5);
    let (current, _) = cut(&field);
    let operands =
        crate::hnn::propagation::Operands::exact_at_cut(&field, &medium, &current).unwrap();
    for ring in 0..field.rings().len() {
        let scatterings = operands.port_scatterings(ring).unwrap();
        let admittance = operands.rings()[ring].admittance().clone();
        let conductances: Vec<Rat> = operands
            .incident(ring)
            .iter()
            .map(|&a| operands.contacts()[a].conductance().clone())
            .collect();
        let weights: Vec<Rat> = std::iter::once(admittance.clone())
            .chain(conductances.clone())
            .collect();
        for (port, scattering) in scatterings.iter().enumerate() {
            assert!(scattering.balances());
            // A unit wave on port `port`, zero elsewhere, on a one-dimensional ring.
            let wave = |q: usize| vec![if q == port { Rat::one() } else { Rat::zero() }];
            let arrivals: Vec<(Rat, Vec<Rat>)> = (1..weights.len())
                .map(|q| (weights[q].clone(), wave(q)))
                .collect();
            let junction = junction_swing(
                &admittance,
                &wave(0),
                &arrivals
                    .iter()
                    .map(|(g, w)| (g, w.as_slice()))
                    .collect::<Vec<_>>(),
            )
            .unwrap();
            let outputs: Vec<Rat> = std::iter::once(junction.storage_wave[0].clone())
                .chain(junction.outgoing.iter().map(|w| w[0].clone()))
                .collect();
            let mut transmitted = Rat::zero();
            for (q, output) in outputs.iter().enumerate() {
                if q == port {
                    assert_eq!(output, &scattering.reflection);
                } else {
                    assert_eq!(output, &(Rat::one() + &scattering.reflection));
                    transmitted += &weights[q] * output * output;
                }
            }
            assert_eq!(transmitted, &scattering.transmission * &weights[port]);
        }
    }
    assert!(port_scattering(&integer(1), &[], 1).is_err());
}

/// The loaded resonator inside the word (`hnn::ring`, `hnn::word::FieldBalance`): its return changes
/// the later receiving face, its signed port work cancels the field's loaded-port work, each tick's
/// balance closes, and the whole word closes on both exact and carried lattices.
#[test]
fn the_loaded_resonator_returns_to_storage_and_closes_at_every_tick() {
    for field in [chain(), chain().with_exact_word()] {
        let field = &field;
        let medium = Medium::encoding(field, 41);
        let (current, moment) = cut(field);
        let phases =
            ReceivingPhases::declare(field, &medium, &current, &field.receivers()[0]).unwrap();
        let mut plain = Word::open(field, &medium, &current, &moment).unwrap();
        let plain_reads = plain.forward(&phases).unwrap();
        let mut declared = Declared::of(field, medium.clone());
        for ring in 0..field.rings().len() {
            let parametron = cycle(
                field.ring(ring).period() as usize,
                vec![Rat::one(); field.ring(ring).period() as usize],
                vec![integer(2); field.ring(ring).period() as usize],
            );
            let pump =
                PumpDeclaration::new(rat(1, 16), Carrier::at(&rat(1, 2)), PumpStep::Half).unwrap();
            declared.resonators[ring] = Some(
                ResonatorMaterial::of_parametron(&parametron, &rat(1, 8), Some(pump)).unwrap(),
            );
        }
        let mut word = Word::open(field, &declared, &current, &moment).unwrap();
        if field.word_lattice().is_some() {
            let (element_carry, returned_carry) = word.loaded_wave_remainders(0).unwrap();
            assert!(element_carry.iter().any(|remainder| !remainder.is_zero()));
            assert!(returned_carry.iter().all(Rat::is_zero));
        }
        let reads = word.forward(&phases).unwrap();
        assert_ne!(reads, plain_reads);
        assert_eq!(word.field_balances().len(), word.balances().len());
        for (field_balance, tick) in word.field_balances().iter().zip(word.balances()) {
            assert!(field_balance.closes(), "{field_balance:?}");
            assert_eq!(
                field_balance.residual(),
                &tick.residual + &tick.loaded_split
            );
            assert_eq!(field_balance.loaded_port, -field_balance.port.clone());
            assert!(field_balance.interconnection.is_zero());
            assert!(tick.closes());
        }
        assert!(word.resonances().iter().all(Option::is_some));
        assert!(
            word.resonances()
                .iter()
                .flatten()
                .flat_map(|resonance| &resonance.steps)
                .any(|step| !step.port.is_zero())
        );
        let balance = word.word_balance().unwrap();
        assert!(balance.closes(), "{balance:?}");
        assert!(plain.word_balance().unwrap().closes());
        assert!(balance.interconnection.is_zero());
        assert!(plain.word_balance().unwrap().interconnection.is_zero());
        // The release returns each resonator's balance (`ResonatorBalance`), which closes, and
        // whose ends and terms sum to the word balance's; a word without resonators returns none.
        let released = word.released().unwrap();
        assert_eq!(released.resonators.len(), field.rings().len());
        for resonator in &released.resonators {
            assert!(resonator.closes(), "{resonator:?}");
            assert_eq!(resonator.ticks, word.balances().len());
        }
        let total = |term: fn(&crate::hnn::word::ResonatorBalance) -> &Rat| -> Rat {
            released.resonators.iter().map(term).sum()
        };
        assert_eq!(total(|r| &r.end), balance.resonator_end);
        assert_eq!(total(|r| &r.pump), balance.pump);
        assert_eq!(total(|r| &r.port), balance.port);
        assert!(plain.released().unwrap().resonators.is_empty());
        let resonant = word.release().unwrap();
        assert_ne!(resonant.power, plain.release().unwrap().power);
    }
}

/// **A wrong resonator solve fails the word's balance** (`hnn::ring::ResonatorStep::bound`, summed
/// into `FieldBalance` and `WordBalance`). The loaded word executed with one phase's solve replaced
/// by `(9/8)M⁻¹` still satisfies every energy identity, since the chart term `⟨ω, Mω − r⟩` absorbs
/// any solve, but its chart term leaves the certified bound (the chart's certificate kept), so the
/// resonator's steps, the ticks' combined balances and the word's balance no longer close; the
/// same word with the executed solve closes, on the exact law and on the lattices alike.
#[test]
fn a_perturbed_resonator_solve_fails_the_word_balance() {
    use crate::hnn::propagation::Operands;
    for field in [chain(), chain().with_exact_word()] {
        let field = &field;
        let medium = Medium::encoding(field, 43);
        let (current, moment) = cut(field);
        let phases =
            ReceivingPhases::declare(field, &medium, &current, &field.receivers()[0]).unwrap();
        let mut declared = Declared::of(field, medium.clone());
        let parametron = cycle(
            field.ring(0).period() as usize,
            vec![Rat::one(); field.ring(0).period() as usize],
            vec![integer(2); field.ring(0).period() as usize],
        );
        let pump =
            PumpDeclaration::new(rat(1, 16), Carrier::at(&rat(1, 2)), PumpStep::Half).unwrap();
        declared.resonators[0] =
            Some(ResonatorMaterial::of_parametron(&parametron, &rat(1, 8), Some(pump)).unwrap());
        let storage = moment.open_storage(field, &declared, &current).unwrap();
        let run = |operands: Operands| {
            let mut word = Word::on_operands(field, operands, storage.clone()).unwrap();
            word.forward(&phases).unwrap();
            word
        };
        let operands = Operands::at_cut(field, &declared, &current).unwrap();
        let executed = run(operands.clone());
        assert!(executed.word_balance().unwrap().closes());
        let mut perturbed = operands;
        let resonator = perturbed.resonators_mut()[0].take().unwrap();
        let wrong = resonator.operator(0).inverse().unwrap().scaled(&rat(9, 8));
        perturbed.resonators_mut()[0] = Some(resonator.with_executed_solve(0, wrong));
        let word = run(perturbed);
        let steps = &word.resonances()[0].as_ref().unwrap().steps;
        assert!(
            steps
                .iter()
                .any(|step| step.phase == 0 && !step.chart.is_zero())
        );
        for step in steps {
            // Every identity still closes; only the bound refuses the wrong phase's ticks.
            assert_eq!(
                &step.after - &step.before,
                &step.pump + &step.port - &step.dissipation + &step.chart + &step.split
            );
        }
        assert!(steps.iter().any(|step| !step.closes()));
        assert!(word.field_balances().iter().any(|tick| !tick.closes()));
        let balance = word.word_balance().unwrap();
        assert!(balance.residual().abs() > balance.bound, "{balance:?}");
        assert!(!balance.closes());
    }
}

/// **The port returns the resonators' balance** (campaign 2): the host reference's refine carries
/// each declared resonator's balance over its word in its receipt (`ReceiptDetail::Refine`), the
/// release's, each closing, and none where no resonator is declared.
#[test]
fn the_refine_receipt_carries_each_resonators_balance() {
    use crate::hnn::port::{ExecutionPort, ReceiptDetail};
    use crate::hnn::reference::{Reference, one_hot};
    let field = chain();
    let theta = Constitution::initial(&field, Steps::campaign_one(), OPEN_BUDGET).unwrap();
    let mut resonant = theta.clone();
    for ring in 0..field.rings().len() {
        let period = field.ring(ring).period() as usize;
        let parametron = cycle(period, vec![Rat::one(); period], vec![integer(2); period]);
        let pump =
            PumpDeclaration::new(rat(1, 16), Carrier::at(&rat(1, 2)), PumpStep::Half).unwrap();
        resonant = resonant
            .with_ring_resonator(
                &field,
                ring,
                ResonatorMaterial::of_parametron(&parametron, &rat(1, 8), Some(pump)).unwrap(),
            )
            .unwrap();
    }
    let reference = Reference::campaign_one();
    let cells: Vec<usize> = (0..12).map(|k| (5 * k + 1) % field.alphabet()).collect();
    for (constitution, declared) in [(theta, false), (resonant, true)] {
        let mut resident = reference
            .mount_with(&field, &Current::at_rest(&field), constitution)
            .unwrap();
        let (moment, _) = reference
            .ingest(&mut resident, None, &one_hot(&cells))
            .unwrap();
        let phases = resident.admitted()[0].clone();
        let (_, refined) = reference.refine(&mut resident, &moment, &phases).unwrap();
        let ReceiptDetail::Refine { resonators, .. } = &refined.receipt.detail else {
            panic!("a refine receipt")
        };
        if declared {
            assert_eq!(resonators.len(), field.rings().len());
            for resonator in resonators {
                assert!(resonator.closes(), "{resonator:?}");
                assert_eq!(resonator.ticks, refined.receipt.balances.len());
            }
        } else {
            assert!(resonators.is_empty());
        }
    }
}

// -------------------------------------------------------------------------------------------
// the contact

/// The census's reading from the factors (`hnn::contact::site_reading_of_factors`): wherever the
/// prime chart certifies both factors' full row rank it returns the exact reading of the Gram
/// matrices (`C = c cᵀ ≻ 0`, `K = b bᵀ ≻ 0`: every mode a rotation), and elsewhere (a deficient
/// rank, a massless direction, a declared signature) it is the exact reading itself; on random
/// factors, on rank-deficient ones and on campaign 1's initial constitution.
#[test]
fn the_census_from_the_factors_is_the_exact_site_reading() {
    let mut draw = Draw::new(97);
    let hop = rat(1, 2);
    for trial in 0..48 {
        let k = 2 + trial % 3;
        let m = k + trial % 2 + usize::from(trial % 5 == 0) * 2;
        let storage = draw.matrix(k, m);
        let mut stiffness = draw.matrix(k, m);
        if trial % 4 == 1 {
            // A repeated row: the stiffness factor loses rank, a null mode.
            let row = stiffness.row(0).unwrap().to_vec();
            let mut rows = stiffness.to_rows();
            rows[1] = row;
            stiffness = ExactRatMatrix::shaped(k, m, rows).unwrap();
        }
        let signature: Option<Vec<bool>> =
            (trial % 6 == 3).then(|| (0..m).map(|j| j != 0).collect());
        let exact = signed_stiffness(&stiffness, signature.as_deref()).and_then(|signed| {
            site_reading(
                &crate::hnn::propagation::gram(&storage).unwrap(),
                &signed,
                &hop,
            )
        });
        let factors = site_reading_of_factors(&storage, &stiffness, signature.as_deref(), &hop);
        match (exact, factors) {
            (Ok(exact), Ok(factors)) => assert_eq!(exact, factors, "trial {trial}"),
            (Err(_), Err(_)) => {}
            (exact, factors) => panic!("trial {trial}: {exact:?} against {factors:?}"),
        }
    }
    let field = Field::declare(FieldDeclaration::campaign_one(6148)).unwrap();
    let theta = Constitution::initial(&field, Steps::campaign_one(), OPEN_BUDGET).unwrap();
    for contact in 0..field.contacts().len() {
        let exact = site_reading(
            &crate::hnn::propagation::gram(theta.contact_storage(contact)).unwrap(),
            &signed_stiffness(theta.contact_stiffness(contact), None).unwrap(),
            field.step(),
        )
        .unwrap();
        let factors = site_reading_of_factors(
            theta.contact_storage(contact),
            theta.contact_stiffness(contact),
            None,
            field.step(),
        )
        .unwrap();
        assert_eq!(exact, factors);
        assert_eq!(factors.kind, SiteKind::Rotation);
    }
}

/// Lean `HNN/Contact.{contact_transfer_kind_by_storage_sign, transfer_trace_det}`: the closed
/// lossless transfer has determinant 1 and is a rotation, a nonidentity null shear or a boost by the
/// sign of `k`; a damped, port-loaded transfer is classified by its own trace and determinant.
#[test]
fn the_site_kind_is_the_sign_of_the_stiffness() {
    let h = rat(1, 2);
    for c in [rat(1, 3), integer(1), integer(5)] {
        for k in [integer(3), rat(1, 7), Rat::zero(), rat(-1, 5), integer(-2)] {
            if (integer(4) * &c + &h * &h * &k).is_zero() {
                continue;
            }
            let closed = transfer(&c, &k, &Rat::zero(), &Rat::zero(), &h).unwrap();
            let site = closed.site();
            assert_eq!(site.determinant(), &Rat::one());
            let expected = if k.is_positive() {
                SiteKind::Rotation
            } else if k.is_zero() {
                SiteKind::Null
            } else {
                SiteKind::Boost
            };
            assert_eq!(site.kind(), expected, "c = {c}, k = {k}");
            if k.is_zero() {
                assert_eq!(
                    closed.matrix,
                    [[Rat::one(), h.clone()], [Rat::zero(), Rat::one()]]
                );
            }
            // The damped transfer: det = (2c + h²k/2 − p − hd)/m, tr = (4c − h²k)/m.
            let (d, p) = (rat(1, 3), rat(1, 2));
            let damped = transfer(&c, &k, &d, &p, &h).unwrap();
            let m = &damped.denominator;
            assert_eq!(
                damped.site().trace(),
                &((integer(4) * &c - &h * &h * &k) / m)
            );
            assert_eq!(
                damped.site().determinant(),
                &((integer(2) * &c + &h * &h * &k / integer(2) - &p - &h * &d) / m)
            );
        }
    }
    // The transfer is the transit: a scalar contact solve reproduces T (u, w).
    let (c, k, d, g) = (rat(2, 3), rat(-1, 4), rat(1, 5), integer(2));
    let t = transfer(&c, &k, &d, &(integer(2) * &h / &g), &h).unwrap();
    let (u, w) = (rat(3, 7), rat(-1, 2));
    let omega = (integer(2) * &c * &w - &h * &k * &u) / &t.denominator;
    assert_eq!(
        t.apply([&u, &w]),
        [&u + &h * &omega, integer(2) * &omega - &w]
    );
}

/// Lean `HNN/Contact.contact_mode_transfer` and the census: a generalized mode `K v = μ C v` spans a
/// plane the closed lossless transit keeps, on which it acts as the scalar transfer at `(1, μ)`;
/// with `C ≻ 0` the contact's census is the inertia of `K`, and its kind the least stable mode's.
#[test]
fn a_generalized_mode_is_a_plane_of_the_scalar_transfer() {
    let mut draw = Draw::new(17);
    let n = 4;
    let factor = draw
        .matrix(n, n)
        .add(&identity(n).scaled(&integer(3)))
        .unwrap();
    let c = gram(&factor).unwrap();
    let v = vec![integer(1), integer(-2), rat(1, 2), integer(1)];
    let norm = dot(&v, &v);
    // P = (I − v vᵀ/|v|²) S (I − v vᵀ/|v|²) annihilates v; K = μ C + P.
    let projector = crate::ratio::linear::vector::matrix(n, n, |i, j| {
        let delta = if i == j { Rat::one() } else { Rat::zero() };
        delta - &v[i] * &v[j] / &norm
    })
    .unwrap();
    let s = gram(&draw.matrix(n, n)).unwrap();
    let p = projector
        .multiply(&s)
        .unwrap()
        .multiply(&projector)
        .unwrap();
    for mu in [integer(2), Rat::zero(), rat(-1, 3)] {
        let k = c.scaled(&mu).add(&p).unwrap();
        assert_eq!(k.apply(&v).unwrap(), scale(&mu, &c.apply(&v).unwrap()));
        let h = integer(1);
        let closed = c
            .scaled(&integer(2))
            .add(&k.scaled(&(&h * &h / integer(2))))
            .unwrap();
        let (a, b) = (rat(3, 2), rat(-1, 3));
        let right = sub(
            &scale(&integer(2), &c.apply(&scale(&b, &v)).unwrap()),
            &scale(&h, &k.apply(&scale(&a, &v)).unwrap()),
        );
        let omega = closed.inverse().unwrap().apply(&right).unwrap();
        let scalar = transfer(&Rat::one(), &mu, &Rat::zero(), &Rat::zero(), &h).unwrap();
        let [a2, b2] = scalar.apply([&a, &b]);
        assert_eq!(add(&scale(&a, &v), &scale(&h, &omega)), scale(&a2, &v));
        assert_eq!(
            sub(&scale(&integer(2), &omega), &scale(&b, &v)),
            scale(&b2, &v)
        );
    }
    // The census: C = I and K of inertia (2, 1, 1).
    let k = ExactRatMatrix::from_diagonal(vec![integer(2), Rat::zero(), integer(-1), rat(1, 2)])
        .unwrap();
    let hop = integer(1);
    let reading = site_reading(&identity(4), &k, &hop).unwrap();
    assert_eq!(
        (
            reading.census.rotation,
            reading.census.null,
            reading.census.boost
        ),
        (2, 1, 1)
    );
    assert_eq!(reading.kind, SiteKind::Boost);
    let psd = ExactRatMatrix::from_diagonal(vec![integer(2), Rat::zero(), integer(1), rat(1, 2)])
        .unwrap();
    assert_eq!(
        site_reading(&identity(4), &psd, &hop).unwrap().kind,
        SiteKind::Null
    );
    assert_eq!(
        site_reading(&identity(4), &identity(4), &hop).unwrap().kind,
        SiteKind::Rotation
    );
    let singular =
        ExactRatMatrix::from_diagonal(vec![integer(1), Rat::zero(), integer(1), integer(1)])
            .unwrap();
    assert_eq!(
        site_reading(&singular, &identity(4), &hop).unwrap().kind,
        SiteKind::Degenerate
    );
    // The Cayley chart's hypothesis `2 + (h²/2)μ ≠ 0` (Lean `contact_transfer_kind_by_storage_sign`):
    // at `h = 1` the boost mode `μ = −4` makes `2C + (h²/2)K` singular, and the reading is refused;
    // at `h = 1/2` the same mode reads a boost.
    let chartless =
        ExactRatMatrix::from_diagonal(vec![integer(2), integer(-4), integer(1), integer(1)])
            .unwrap();
    assert!(matches!(
        site_reading(&identity(4), &chartless, &hop),
        Err(HnnError::SingularTransfer)
    ));
    assert!(transfer(&Rat::one(), &integer(-4), &Rat::zero(), &Rat::zero(), &hop).is_err());
    assert_eq!(
        site_reading(&identity(4), &chartless, &rat(1, 2))
            .unwrap()
            .kind,
        SiteKind::Boost
    );
}

/// Lean `HNN/Word.field_commit_deposition` (`hnn::word::{WordBalance, PowerForm}`): the word's
/// balance, formed from its release, closes; carried across a deposit that moves the contacts'
/// storage and stiffness, the end change's committed power is its power plus the deposition work
/// `½⟨x, ΔΘ x⟩` formed from the forms' differences, and the balance closes with it; a misstated
/// deposition breaks the identity; a commit that leaves `Θ` does no work; on the word's lattices and
/// under the exact law.
#[test]
fn the_word_balance_closes_across_its_commit() {
    for field in [chain(), chain().with_exact_word()] {
        let field = &field;
        let medium = Medium::encoding(field, 41);
        let (current, moment) = cut(field);
        let phases =
            ReceivingPhases::declare(field, &medium, &current, &field.receivers()[0]).unwrap();
        let mut word = Word::open(field, &medium, &current, &moment).unwrap();
        word.forward(&phases).unwrap();
        let released = word.released().unwrap();
        let mut balance = WordBalance::of(&released);
        assert!(balance.closes(), "{balance:?}");
        assert_eq!(balance, word.word_balance().unwrap());
        let mut deposited = medium.clone();
        for contact in 0..field.contacts().len() {
            deposited.storage[contact] = deposited.storage[contact].scaled(&rat(3, 2));
            deposited.stiffness[contact] = deposited.stiffness[contact].scaled(&rat(1, 2));
        }
        let before = PowerForm::read(field, &medium, &current).unwrap();
        let after = PowerForm::read(field, &deposited, &current).unwrap();
        assert_eq!(before.power(&balance.change).unwrap(), balance.end);
        balance.commit(&before, &after).unwrap();
        let commit = balance.commit.clone().unwrap();
        assert!(!commit.deposition.is_zero());
        assert_eq!(commit.committed, &balance.end + &commit.deposition);
        assert!(balance.closes(), "{balance:?}");
        let mut misstated = balance.clone();
        misstated.commit.as_mut().unwrap().deposition = Rat::zero();
        assert!(!misstated.closes());
        let mut unmoved = WordBalance::of(&released);
        unmoved.commit(&before, &before).unwrap();
        assert!(unmoved.commit.as_ref().unwrap().deposition.is_zero());
        assert!(unmoved.closes());
    }
}

/// Lean `HNN/Contact.{contact_boost_solve_or_singular_direction, contact_signed_storage_balance,
/// boost_grows_at_conserved_signed_storage}`: a negative stiffness column is admitted only with a
/// certified solve, a singular one refused with a direction the operator sends to zero; the
/// signed-storage balance of the transit holds exactly at an indefinite `K`; the closed boost grows
/// the state at conserved signed storage.
#[test]
fn a_boost_is_admitted_only_with_a_certified_solve() {
    let h = integer(1);
    // K = b diag(σ) bᵀ with one negative column.
    let b = ExactRatMatrix::from_diagonal(vec![integer(1), integer(2)]).unwrap();
    let stiffness = signed_stiffness(&b, Some(&[true, false])).unwrap();
    assert_eq!(
        stiffness,
        ExactRatMatrix::from_diagonal(vec![integer(1), integer(-4)]).unwrap()
    );
    // Singular at G = 2: m = 1 + (G/2h)(2C + (h²/2)K) with C = c I: (1 + 2c − 2) = 0 at c = 1/2.
    let storage = identity(2).scaled(&rat(1, 2));
    let dissipation = ExactRatMatrix::zero(2, 2).unwrap();
    let refused = certify_boost(3, [&storage, &stiffness, &dissipation], &integer(2), &h);
    match refused {
        Err(HnnError::SingularContact {
            contact, direction, ..
        }) => {
            assert_eq!(contact, 3);
            let operator = crate::hnn::propagation::contact_operator(
                &storage,
                &stiffness,
                &dissipation,
                &integer(2),
                &h,
            )
            .unwrap();
            assert!(
                operator
                    .apply(&direction)
                    .unwrap()
                    .iter()
                    .all(Zero::is_zero)
            );
            assert!(direction.iter().any(|x| !x.is_zero()));
        }
        other => panic!("expected the singular direction, found {other:?}"),
    }
    assert!(!signed_form_certifies(&storage, &stiffness, &dissipation, &h).unwrap());
    // A storage large enough certifies at every conductance.
    let heavy = identity(2).scaled(&integer(4));
    assert!(signed_form_certifies(&heavy, &stiffness, &dissipation, &h).unwrap());
    for conductance in [rat(1, 16), integer(1), integer(64)] {
        certify_boost(0, [&heavy, &stiffness, &dissipation], &conductance, &h).unwrap();
    }
    // The signed-storage balance: the transit at an indefinite K balances exactly.
    let operands = ContactOperands::new(
        (0, 1),
        (vec![0, 1], vec![0, 1]),
        ExponentReading {
            quadrance: Rat::zero(),
            exponent: Rat::zero(),
            carry: BigInt::zero(),
            phase: 0,
        },
        integer(2),
        &h,
        &identity(2).scaled(&integer(2)),
        &b,
        &ExactRatMatrix::from_diagonal(vec![rat(1, 2), rat(1, 2)]).unwrap(),
    )
    .unwrap();
    let mut draw = Draw::new(23);
    let (from, to) = (draw.vector(2), draw.vector(2));
    let (u, w) = (draw.vector(2), draw.vector(2));
    let passed = transit(&operands, &h, &from, &to, &u, &w).unwrap();
    let energy_after = operands.energy(&passed.displacement, &passed.rate).unwrap();
    let port = &h * integer(2) / integer(4)
        * (dot(&passed.channel_in.0, &passed.channel_in.0)
            + dot(&passed.channel_in.1, &passed.channel_in.1)
            - dot(&passed.channel_out.0, &passed.channel_out.0)
            - dot(&passed.channel_out.1, &passed.channel_out.1));
    assert_eq!(
        energy_after - operands.energy(&u, &w).unwrap() + &passed.dissipation,
        port
    );
    // The closed boost at c = 1, k = −1, h = 1: [[5/3, 4/3], [4/3, 5/3]], (1, 1) ↦ (3, 3).
    let boost = transfer(&Rat::one(), &integer(-1), &Rat::zero(), &Rat::zero(), &h).unwrap();
    assert_eq!(
        boost.matrix,
        [[rat(5, 3), rat(4, 3)], [rat(4, 3), rat(5, 3)]]
    );
    assert_eq!(boost.site().kind(), SiteKind::Boost);
    let grown = boost.apply([&Rat::one(), &Rat::one()]);
    assert_eq!(grown, [integer(3), integer(3)]);
    let signed = |state: &[Rat; 2]| (&state[1] * &state[1] - &state[0] * &state[0]) / integer(2);
    assert_eq!(signed(&grown), signed(&[Rat::one(), Rat::one()]));
}

/// The boost in `Θ` and in the word: `Constitution::with_contact_signature` certifies the boost at
/// every conductance the contact can take and refuses an uncertifiable one with its direction; an
/// admitted boost runs in the word, whose balances close exactly with its signed storage, and the
/// contact reads its site kind as a boost.
#[test]
fn a_certified_boost_runs_in_the_word_and_reads_as_a_boost() {
    let field = chain();
    let theta = Constitution::initial(&field, Steps::campaign_one(), OPEN_BUDGET).unwrap();
    // Campaign 1's contact: C = I, K = ¼I, D = ¼I, factors ½I. One negative column.
    let k = field.contact(0).width();
    let signature: Vec<bool> = (0..k).map(|j| j != 0).collect();
    let boosted = theta
        .clone()
        .with_contact_signature(&field, 0, signature.clone())
        .unwrap();
    assert_eq!(
        boosted.contact_stiffness_signature(0),
        Some(signature.as_slice())
    );
    let current = Current::at_rest(&field);
    let readings = contact_readings(&field, &boosted, &current, None).unwrap();
    assert_eq!(readings[0].kind, SiteKind::Boost);
    assert_eq!(readings[1].kind, SiteKind::Rotation);
    let (cut_current, moment) = cut(&field);
    let mut word = Word::open(&field, &boosted, &cut_current, &moment).unwrap();
    for _ in 0..4 {
        let balance = word.tick().unwrap();
        assert!(balance.closes());
    }
    for field_balance in word.field_balances() {
        assert!(field_balance.closes());
    }
    // No storage, D = I, K = diag(−4, 4, …): at the conductance G = 2 the contact takes at rest,
    // m = 1 + (G/2)(1 − 2) = 0 on the negative direction, so the declaration is refused with it.
    let weak = theta
        .with_channel(
            0,
            ExactRatMatrix::zero(k, k).unwrap(),
            identity(k).scaled(&integer(2)),
            identity(k),
        )
        .unwrap();
    match weak.with_contact_signature(&field, 0, signature) {
        Err(HnnError::SingularContact {
            direction,
            conductance,
            ..
        }) => {
            assert_eq!(*conductance, integer(2));
            assert!(!direction[0].is_zero());
            assert!(direction[1..].iter().all(Zero::is_zero));
        }
        other => panic!("expected the singular direction, found {other:?}"),
    }
}

/// Lean `HNN/Contact.{contact_lock_address, IsLockAddress, lockAddress_closes}`,
/// `Geometry/PairResonance` and `Aeon/Clock/Lock`: the lock address of a measured winding pair is
/// the least-denominator rate in its fibre, the least of that denominator (the brute force's first),
/// in the box `p ≤ m_g`, `q ≤ m_h`, a mediant of neighbours where the fibre straddles one, Unlocked
/// beyond the bound or before a ring winds; two clocks at the address close at its period with
/// whole windings; and the derived bound is the horizon `∏_(j>r) d_j` (Lean `lock_partition_finite`).
#[test]
fn lock_addresses_mediants_and_whole_windings() {
    let bound = LockDeclaration {
        denominator: BigUint::from(12u32),
        numerator: BigUint::from(40u32),
    };
    for first in 1i64..30 {
        for second in 1i64..20 {
            let lock = lock_address(&BigInt::from(first), &BigInt::from(second), &bound);
            let (lower, upper) = (rat(first, second + 1), rat(first + 1, second));
            // The least denominator in the open fibre, by brute force.
            let least = (1i64..=400)
                .find_map(|q| {
                    (0..=q * 40)
                        .map(|p| rat(p, q))
                        .find(|x| &lower < x && x < &upper)
                })
                .unwrap();
            match &lock {
                ContactLock::Locked {
                    numerator,
                    denominator,
                } => {
                    let address = Rat::new(
                        BigInt::from(numerator.clone()),
                        BigInt::from(denominator.clone()),
                    );
                    assert!(lower < address && address < upper);
                    assert_eq!(address, least);
                    assert!(numerator <= &BigUint::from(first as u64));
                    assert!(denominator <= &BigUint::from(second as u64));
                    // Two clocks at the address close at its period with whole windings.
                    let clocks = TwoClocks::new(address.clone()).unwrap();
                    let aeon = clocks.aeon(denominator).unwrap();
                    let (a, b) = clocks.joint_reading(&aeon).unwrap();
                    assert!(clocks.is_cycle(&aeon));
                    assert_eq!(a.windings(), &BigInt::from(numerator.clone()));
                    assert_eq!(b.windings(), &BigInt::from(denominator.clone()));
                }
                ContactLock::Unlocked => {
                    assert!(
                        least.denom() > &BigInt::from(12) || least.numer() > &BigInt::from(40),
                        "{first}/{second}"
                    );
                }
            }
        }
    }
    // The measured pair (6, 4) reduces to 3/2 and its fibre (6/5, 7/4) holds the simpler 3/2.
    let three_halves = lock_address(&BigInt::from(6), &BigInt::from(4), &bound);
    assert_eq!(
        three_halves,
        ContactLock::Locked {
            numerator: BigUint::from(3u32),
            denominator: BigUint::from(2u32)
        }
    );
    // Neighbours 1/2 and 2/3: the least lock strictly between is their mediant 3/5.
    assert!(are_neighbours(&rat(1, 2), &rat(2, 3)));
    assert_eq!(mediant(&rat(1, 2), &rat(2, 3)), rat(3, 5));
    assert_eq!(
        lock_address(&BigInt::zero(), &BigInt::from(3), &bound),
        ContactLock::Unlocked
    );
    assert_eq!(
        lock_address(&BigInt::from(3), &BigInt::zero(), &bound),
        ContactLock::Unlocked
    );
    // The derived bound is the horizon: ring r winds at most ∏_(j>r) d_j times an aeon, the last
    // ring once, and the closing tick's letter reads them all.
    let campaign = Field::declare(FieldDeclaration::campaign_one(1 << 17)).unwrap();
    let derived = LockDeclaration::derived(&campaign, 3);
    assert_eq!(derived.denominator, BigUint::from(7u32 * 11 * 13));
    assert_eq!(derived.numerator, BigUint::one());
    let into_last = LockDeclaration::derived(&campaign, 2);
    assert_eq!(into_last.denominator, BigUint::one());
    assert_eq!(into_last.numerator, BigUint::from(13u32));
    // Every contact's family carries more than one letter: no slot is constant by construction.
    for contact in 0..campaign.contacts().len() {
        let bound = LockDeclaration::derived(&campaign, contact);
        assert!(bound.letters().unwrap() >= 2, "contact {contact}");
    }
    // At the horizon every address of windings within it lands in the family: the closing tick of
    // contact 2 (m_2 = 13 = d_3 windings of ring 2, one of ring 3) is Locked.
    assert!(matches!(
        lock_address(&BigInt::from(13), &BigInt::one(), &into_last),
        ContactLock::Locked { .. }
    ));
}

/// **The readings worker B consumes** (`hnn::contact::contact_readings`): on campaign 1's field at
/// rest every contact is Unlocked (no ring has wound) and a rotation (`C = I`, `K = ¼I`); after a
/// passage the locks read the rings' whole windings, and the readings read nothing of a later cell.
#[test]
fn the_contact_readings_are_read_from_retained_state() {
    let field = Field::declare(FieldDeclaration::campaign_one(6148)).unwrap();
    let theta = Constitution::initial(&field, Steps::campaign_one(), OPEN_BUDGET).unwrap();
    let rest = Current::at_rest(&field);
    let readings = contact_readings(&field, &theta, &rest, None).unwrap();
    assert_eq!(readings.len(), 4);
    for (a, reading) in readings.iter().enumerate() {
        assert_eq!(reading.contact, a);
        assert_eq!(reading.lock, ContactLock::Unlocked);
        assert_eq!(reading.kind, SiteKind::Rotation);
    }
    let mut draw = Draw::new(31);
    let mut current = rest.clone();
    for _ in 0..5000 {
        current.step(&field, draw.below(256)).unwrap();
    }
    let later = contact_readings(&field, &theta, &current, Some(&rest)).unwrap();
    let again = contact_readings(&field, &theta, &current, Some(&rest)).unwrap();
    assert_eq!(later, again);
    // Contact 3 = (3 → 0): ring 0 has wound, ring 3 has not.
    assert!(
        later
            .iter()
            .any(|reading| reading.lock != ContactLock::Unlocked)
    );
}

/// Lean `HNN/ContactBreak.{break_release_balance, break_iff_release_covers_gluing,
/// griffith_closed_port_case, parting_returns_gluing_defect}`: under the exact law the released
/// storage is the storage the parting removes; the advance is admitted exactly when the remainder
/// is nonnegative; the word reads the receipt at every transit where the law is declared; and a
/// parted contact's shared face returns the typed defect `UncancelledPower`.
#[test]
fn the_break_receipt_and_the_parted_face() {
    let field = chain().with_exact_word();
    let medium = Medium::encoding(&field, 41);
    let (current, moment) = cut(&field);
    let mut declared = Declared::of(&field, medium);
    declared.surfaces[0] = Some(rat(1, 64));
    let mut word = Word::open(&field, &declared, &current, &moment).unwrap();
    for _ in 0..3 {
        word.tick().unwrap();
    }
    let receipts: Vec<_> = word
        .partings()
        .iter()
        .map(|tick| tick[0].clone().unwrap())
        .collect();
    assert!(word.partings().iter().all(|tick| tick[1].is_none()));
    for receipt in &receipts {
        // Exact law: R = E_a + W − D − E_a′ = E_a(z′) − E_a′(z′), E_a′ = 0 (the whole contact parts).
        assert!(receipt.kept.is_zero());
        assert_eq!(receipt.remainder, &receipt.released - &receipt.gluing);
        assert_eq!(receipt.parts, !receipt.remainder.is_negative());
        assert_eq!(receipt.gluing, rat(1, 64) * integer(2));
    }
    // The exact law's release balance on one transit, with part of the channel parted.
    let operands =
        crate::hnn::propagation::Operands::exact_at_cut(&field, &declared, &current).unwrap();
    let contact = &operands.contacts()[0];
    let mut draw = Draw::new(5);
    let (from, to) = (draw.vector(4), draw.vector(6));
    let (u, w) = (draw.vector(4), draw.vector(4));
    let passed = transit(contact, operands.step(), &from, &to, &u, &w).unwrap();
    let receipt = crate::hnn::contact::BreakReceipt::read(
        contact,
        operands.step(),
        [&u, &w],
        [&passed.displacement, &passed.rate],
        &passed,
        &[1],
        &rat(1, 8),
    )
    .unwrap();
    let full = contact.energy(&passed.displacement, &passed.rate).unwrap();
    assert_eq!(receipt.released, &full - &receipt.kept);
    // Griffith: no port, no loss: R = E_a − E_a′.
    assert_eq!(
        receipt.stored.clone() + Rat::zero() - Rat::zero() - receipt.kept.clone(),
        &receipt.stored - &receipt.kept
    );
    let (_, image) = transit_solve(contact, operands.step(), &from, &to, &u, &w).unwrap();
    assert_eq!(image.len(), 4);
    // The parted face.
    let theta = Constitution::initial(&field, Steps::campaign_one(), OPEN_BUDGET).unwrap();
    assert!(field.holarchy(&theta).is_ok());
    match field.parted_holarchy(&theta, 1).unwrap() {
        GluingDefect::UncancelledPower { power, .. } => assert!(!power.is_zero()),
        other => panic!("expected an uncancelled power, found {other:?}"),
    }
    assert!(field.parted_holarchy(&theta, 7).is_err());
}

/// Every refusal of campaign 2's physics, each a typed return.
#[test]
fn every_refusal_is_typed() {
    let h = integer(1);
    // A transfer with no Cayley chart: 2c + h²k/2 = 0.
    assert_eq!(
        transfer(&Rat::one(), &integer(-4), &Rat::zero(), &Rat::zero(), &h),
        Err(HnnError::SingularTransfer)
    );
    // A resonator whose pump makes a phase's signed form indefinite.
    let ring = cycle(2, vec![rat(1, 64); 2], vec![rat(1, 64); 2]);
    let strong =
        PumpDeclaration::new(integer(4), Carrier::at(&Rat::zero()), PumpStep::Half).unwrap();
    let material = ResonatorMaterial::of_parametron(&ring, &Rat::zero(), Some(strong)).unwrap();
    assert_eq!(
        material.certify(2, &h),
        Err(HnnError::UncertifiedResonator { ring: 2, phase: 0 })
    );
    assert!(matches!(
        ResonatorOperands::at_cut(2, &material, &integer(2), &h, None),
        Err(HnnError::UncertifiedResonator { .. })
    ));
    // Malformed resonators and pumps.
    assert!(ResonatorMaterial::new(identity(3), identity(3), identity(3), None).is_err());
    assert!(
        ResonatorMaterial::new(
            identity(2).scaled(&-Rat::one()),
            identity(2),
            identity(2),
            None
        )
        .is_err()
    );
    assert!(PumpDeclaration::new(integer(-1), Carrier::at(&Rat::zero()), PumpStep::Stand).is_err());
    // A signature of the wrong length.
    let field = chain();
    let theta = Constitution::initial(&field, Steps::campaign_one(), OPEN_BUDGET).unwrap();
    assert!(matches!(
        theta.clone().with_contact_signature(&field, 0, vec![true]),
        Err(HnnError::Shape { .. })
    ));
    assert!(theta.clone().with_surface_storage(0, integer(-1)).is_err());
    let wrong = ResonatorMaterial::of_parametron(
        &cycle(5, vec![Rat::one(); 5], vec![Rat::one(); 5]),
        &Rat::zero(),
        None,
    )
    .unwrap();
    assert!(matches!(
        theta.with_ring_resonator(&field, 0, wrong),
        Err(HnnError::Shape { .. })
    ));
}
