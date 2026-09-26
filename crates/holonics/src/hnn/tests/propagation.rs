//! The local tick's laws: the junction Swing, the ring element, the contact two-port, the global
//! power balance, the causal cone and the contact exponent.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use super::learning::chain;
use super::support::{
    Draw, Medium, Parts, chorded_field, injection, lift, ring, six_cycle, small_field,
};
use crate::hnn::HnnError;
use crate::hnn::chart::{ChartKey, WordLattice};
use crate::hnn::field::{Current, Field, FieldDeclaration};
use crate::hnn::propagation::{
    ContactOperands, ExponentReading, Operands, RingOperands, contact_exponent, element_step,
    junction_swing, path_attenuation, transit,
};
use crate::hnn::word::Word;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::{add, dot, scale, sub};
use crate::ratio::{Rat, integer, rat};

/// Lean `HNN/Propagation.{anchor_is_participation, junctionSwing_involutive,
/// junctionSwing_isometry}`: the anchor is the normalized participation (the weights `G_a/(Y + ΣG)`
/// with the storage port included), the Swing is an involution, and it keeps the `W`-weighted power
/// `Y|s|² + Σ G|a|²`.
#[test]
fn the_junction_swing_is_a_weighted_involution_about_the_participation_anchor() {
    let mut draw = Draw::new(1);
    let admittance = rat(3, 2);
    let conductances = [rat(1, 4), integer(2), rat(5, 3)];
    let storage = draw.vector(6);
    let waves: Vec<Vec<Rat>> = (0..3).map(|_| draw.vector(6)).collect();
    let arrivals: Vec<(&Rat, &[Rat])> = conductances
        .iter()
        .zip(&waves)
        .map(|(g, w)| (g, w.as_slice()))
        .collect();
    let junction = junction_swing(&admittance, &storage, &arrivals).unwrap();
    let total = &admittance + conductances.iter().sum::<Rat>();
    let mut anchor = scale(&(&admittance / &total), &storage);
    for (g, w) in conductances.iter().zip(&waves) {
        anchor = add(&anchor, &scale(&(g / &total), w));
    }
    assert_eq!(junction.anchor, anchor);
    let power = |s: &[Rat], a: &[Vec<Rat>]| {
        &admittance * dot(s, s)
            + conductances
                .iter()
                .zip(a)
                .map(|(g, w)| g * dot(w, w))
                .sum::<Rat>()
    };
    assert_eq!(
        power(&junction.storage_wave, &junction.outgoing),
        power(&storage, &waves)
    );
    let again: Vec<(&Rat, &[Rat])> = conductances
        .iter()
        .zip(&junction.outgoing)
        .map(|(g, w)| (g, w.as_slice()))
        .collect();
    let twice = junction_swing(&admittance, &junction.storage_wave, &again).unwrap();
    assert_eq!(twice.storage_wave, storage);
    assert_eq!(twice.outgoing, waves);
    assert_eq!(junction.contrast, sub(&junction.anchor, &storage));
}

fn ring_operands(draw: &mut Draw, n: usize, resist: bool, contrast: bool) -> RingOperands {
    let zero = ExactRatMatrix::zero(n, n).unwrap();
    let passive = if resist {
        draw.matrix(n, n)
    } else {
        zero.clone()
    };
    let port = if contrast { draw.matrix(n, n) } else { zero };
    let slices: Vec<(Vec<Rat>, Vec<Rat>)> =
        (0..n).map(|_| (draw.vector(n), draw.vector(n))).collect();
    RingOperands::new(integer(2), &draw.vector(n), &passive, &port, &slices).unwrap()
}

/// Lean `HNN/Word.reaction_stage_isometry`: with skew slices only (`W_s = W_c = 0`),
/// `½|s′|² = ½|b|²` exactly, at every sheet configuration.
#[test]
fn the_skew_element_is_an_isometry() {
    let mut draw = Draw::new(2);
    for _ in 0..4 {
        let ring = ring_operands(&mut draw, 6, false, false);
        let wave = draw.vector(6);
        let step = element_step(&ring, &wave, &draw.vector(6)).unwrap();
        assert_eq!(dot(&step.next, &step.next), dot(&wave, &wave));
        assert!(step.resist.is_zero() && step.drive.is_zero());
    }
}

/// Lean `HNN/Word.reaction_stage_balance` (over `Holon/Cayley.drive_balance`): with a passive part
/// and a contrast port, `½|s′|² − ½|b|² = ⟨x̄, W_s x̄⟩ + ⟨x̄, W_c c⟩` exactly, the first term `≤ 0`.
#[test]
fn the_element_balance_holds_with_passive_part_and_contrast_port() {
    let mut draw = Draw::new(3);
    for (resist, contrast) in [(true, false), (false, true), (true, true)] {
        let ring = ring_operands(&mut draw, 6, resist, contrast);
        let (wave, drive) = (draw.vector(6), draw.vector(6));
        let step = element_step(&ring, &wave, &drive).unwrap();
        let half = rat(1, 2);
        assert_eq!(
            &half * dot(&step.next, &step.next) - &half * dot(&wave, &wave),
            &step.resist + &step.drive
        );
        assert!(step.resist <= Rat::zero());
        assert_eq!(step.midpoint, scale(&half, &add(&wave, &step.next)));
    }
}

/// Lean `HNN/Word.contrastPort_active`: for `W_c c ≠ 0` some storage wave makes the contrast port's
/// power positive, so the element is passive for every input only when `W_c = 0`. The wave is
/// `b = t (I − ½K) W_c c − ½ W_c c`, whose midpoint is `t W_c c`.
#[test]
fn a_nonzero_contrast_port_supplies_positive_power_for_some_input() {
    let mut draw = Draw::new(4);
    let ring = ring_operands(&mut draw, 6, true, true);
    let contrast = draw.vector(6);
    let driven = ring.contrast().apply(&contrast).unwrap();
    assert!(driven.iter().any(|x| !x.is_zero()));
    let left = ExactRatMatrix::identity(6)
        .unwrap()
        .subtract(&ring.element().scaled(&rat(1, 2)))
        .unwrap();
    let wave = sub(
        &left.apply(&scale(&integer(3), &driven)).unwrap(),
        &scale(&rat(1, 2), &driven),
    );
    let step = element_step(&ring, &wave, &contrast).unwrap();
    assert_eq!(step.midpoint, scale(&integer(3), &driven));
    assert!(step.drive > Rat::zero());
    let negative = element_step(&ring, &scale(&-Rat::one(), &wave), &contrast).unwrap();
    assert!(negative.drive != step.drive);
}

fn contact_operands(draw: &mut Draw, k: usize, parts: Parts) -> ContactOperands {
    let zero = ExactRatMatrix::zero(k, k).unwrap();
    let factor = |on: bool, draw: &mut Draw| if on { draw.matrix(k, k) } else { zero.clone() };
    let storage = factor(parts.store, draw);
    let stiffness = factor(parts.stiff, draw);
    let dissipation = factor(parts.dissipative, draw);
    ContactOperands::new(
        (0, 1),
        ((0..k).collect(), (1..=k).collect()),
        ExponentReading {
            quadrance: Rat::zero(),
            exponent: Rat::zero(),
            carry: BigInt::zero(),
            phase: 0,
        },
        rat(3, 2),
        &integer(1),
        &storage,
        &stiffness,
        &dissipation,
    )
    .unwrap()
}

/// Lean `HNN/Propagation.transit_balance`: the contact's midpoint two-port changes its stored
/// energy and dissipates exactly what its channel waves lose,
/// `E′ − E + h ω*Dω = (hG/4)(|α|² − |α_out|²)`; off the channel each wave reflects unchanged.
#[test]
fn the_transit_balances_its_channel_power() {
    let mut draw = Draw::new(5);
    let parts = Parts {
        dissipative: true,
        stiff: true,
        store: true,
        ..Parts::default()
    };
    let contact = contact_operands(&mut draw, 2, parts);
    let (from, to) = (draw.vector(3), draw.vector(4));
    let (u, w) = (draw.vector(2), draw.vector(2));
    let passed = transit(&contact, &integer(1), &from, &to, &u, &w).unwrap();
    let energy = |u: &[Rat], w: &[Rat]| contact.energy(u, w).unwrap();
    let norm = |pair: &(Vec<Rat>, Vec<Rat>)| dot(&pair.0, &pair.0) + dot(&pair.1, &pair.1);
    assert_eq!(
        energy(&passed.displacement, &passed.rate) - energy(&u, &w) + &passed.dissipation,
        contact.conductance() / integer(4) * (norm(&passed.channel_in) - norm(&passed.channel_out))
    );
    assert!(passed.dissipation >= Rat::zero());
    assert_eq!(
        passed.arrive_from[2], from[2],
        "off the channel the wave reflects"
    );
    assert_eq!(
        passed.arrive_to[0], to[0],
        "off the channel the wave reflects"
    );
}

/// Design (a), "Reception is composed", item 1: the ring element's step is `ReferenceHolon`'s
/// implicit-midpoint advance (`Holon/Law.advance_law`) of the medium `ẋ = (Ω − R)x + W_c c` with
/// `Q = I` and `h = 1`, where `Ω = Σ σ_ρ A_ρ` is the element's skew part, `R = −W_s = f fᵀ` its
/// resistance and the contrast `c` the external effort on the input `W_c`: at the same operands it
/// reaches the same storage, its dissipation is `−⟨x̄, W_s x̄⟩` and its port power `⟨x̄, W_c c⟩`.
#[test]
fn the_element_step_is_the_reference_holons_midpoint_advance() {
    use crate::holon::law::{HolonLaw, ReferenceHolon, Scheme};
    use crate::holon::{Holon, HolonState, PortHolon};
    use crate::ratio::linear::inertia::SymmetricForm;
    let mut draw = Draw::new(12);
    let n = 4;
    let ring = ring_operands(&mut draw, n, true, true);
    let (wave, contrast) = (draw.vector(n), draw.vector(n));
    let step = element_step(&ring, &wave, &contrast).unwrap();
    let skew = ring.element().subtract(ring.passive()).unwrap();
    let resistance = ring.passive().scaled(&-Rat::one());
    let identity = (0..n)
        .map(|i| {
            (0..n)
                .map(|j| if i == j { Rat::one() } else { Rat::zero() })
                .collect()
        })
        .collect();
    let medium = PortHolon::medium(
        &skew,
        &resistance,
        SymmetricForm::from_rows(identity).unwrap(),
        ring.contrast(),
        false,
    )
    .unwrap();
    let law =
        ReferenceHolon::new(Holon::new(medium).unwrap(), integer(1), Scheme::Midpoint).unwrap();
    let advanced = law
        .advance(&HolonState::new(wave.clone()), &contrast)
        .unwrap();
    assert_eq!(advanced.state.configuration, step.next);
    assert_eq!(advanced.balance.dissipated, -&step.resist);
    assert_eq!(advanced.balance.port, step.drive);
    assert!(advanced.balance.is_exact());
}

/// Design (a), "Reception is composed", item 1, for the contact where its storage chart exists:
/// with `C_a ≻ 0` the transit is `ReferenceHolon`'s midpoint advance of the medium on
/// `(u, p = C_a w)` with storage `(K_a, C_a⁻¹)`, `u̇ = w`, `ṗ = −K_a u − (D_a + (2/G_a)I) w + α_g − α_h`
/// (the two wave sources seen through their port conductance `G_a`): at the same operands and step
/// it reaches the same displacement and rate, its port flow is the midpoint rate `ω`, and its
/// dissipation is the contact's `h ω*D ω` plus the ports' `(2h/G_a)|ω|²`. [agent-inferred] A
/// singular `C_a` (campaign 1 admits `c_a = 0`, pure transmission) has no such chart: the transit is
/// then a descriptor midpoint step with mass `C_a`, which the reference law's unit-mass step does
/// not state, so the tick keeps its own `M_a` solve.
#[test]
fn a_stored_transit_is_the_reference_holons_midpoint_advance() {
    use crate::holon::law::{HolonLaw, ReferenceHolon, Scheme};
    use crate::holon::{Holon, HolonState, PortHolon};
    use crate::ratio::linear::inertia::SymmetricForm;
    let mut draw = Draw::new(13);
    let (k, h) = (2, rat(1, 2));
    let (c, b, f) = (draw.matrix(k, k), draw.matrix(k, k), draw.matrix(k, k));
    let contact = ContactOperands::new(
        (0, 1),
        ((0..k).collect(), (1..=k).collect()),
        ExponentReading {
            quadrance: Rat::zero(),
            exponent: Rat::zero(),
            carry: BigInt::zero(),
            phase: 0,
        },
        rat(3, 2),
        &h,
        &c,
        &b,
        &f,
    )
    .unwrap();
    let (from, to) = (draw.vector(3), draw.vector(4));
    let (u, w) = (draw.vector(k), draw.vector(k));
    let passed = transit(&contact, &h, &from, &to, &u, &w).unwrap();
    let (storage, stiffness, dissipation) = contact.forms();
    let compliance = storage.inverse().unwrap();
    let g = contact.conductance().clone();
    let block = |i: usize, j: usize, value: &dyn Fn(usize, usize) -> Rat| {
        (0..2 * k)
            .map(|r| {
                (0..2 * k)
                    .map(|s| match (r / k == i, s / k == j) {
                        (true, true) => value(r % k, s % k),
                        _ => Rat::zero(),
                    })
                    .collect::<Vec<Rat>>()
            })
            .collect::<Vec<_>>()
    };
    let sum = |a: Vec<Vec<Rat>>, b: Vec<Vec<Rat>>| {
        a.into_iter()
            .zip(b)
            .map(|(x, y)| x.into_iter().zip(y).map(|(p, q)| p + q).collect())
            .collect::<Vec<Vec<Rat>>>()
    };
    let unit = |i: usize, j: usize| if i == j { Rat::one() } else { Rat::zero() };
    let omega = sum(block(0, 1, &unit), block(1, 0, &|i, j| -unit(i, j)));
    let resistance = block(1, 1, &|i, j| {
        dissipation.get(i, j).unwrap() + integer(2) / &g * unit(i, j)
    });
    let input = sum(block(1, 0, &unit), block(1, 1, &|i, j| -unit(i, j)));
    let forms = sum(
        block(0, 0, &|i, j| stiffness.get(i, j).unwrap().clone()),
        block(1, 1, &|i, j| compliance.get(i, j).unwrap().clone()),
    );
    let matrix = |rows: Vec<Vec<Rat>>| ExactRatMatrix::shaped(2 * k, 2 * k, rows).unwrap();
    let medium = PortHolon::medium(
        &matrix(omega),
        &matrix(resistance),
        SymmetricForm::from_rows(forms).unwrap(),
        &matrix(input),
        false,
    )
    .unwrap();
    let law =
        ReferenceHolon::new(Holon::new(medium).unwrap(), h.clone(), Scheme::Midpoint).unwrap();
    let momentum = storage.apply(&w).unwrap();
    let state: Vec<Rat> = u.iter().chain(&momentum).cloned().collect();
    let efforts: Vec<Rat> = passed
        .channel_in
        .0
        .iter()
        .chain(&passed.channel_in.1)
        .cloned()
        .collect();
    let advanced = law.advance(&HolonState::new(state), &efforts).unwrap();
    let reached = &advanced.state.configuration;
    assert_eq!(reached[..k], passed.displacement[..]);
    assert_eq!(reached[k..], storage.apply(&passed.rate).unwrap()[..]);
    let flows = law.kinds(&advanced).unwrap();
    assert_eq!(flows.external.flow()[..k], passed.midpoint[..]);
    assert_eq!(
        advanced.balance.dissipated,
        &passed.dissipation + &h * integer(2) / &g * dot(&passed.midpoint, &passed.midpoint)
    );
    assert!(advanced.balance.is_exact());
}

/// With no storage, stiffness or dissipation the contact is pure transmission: the wave from each
/// end arrives at the other through `U_a` and `U_aᵀ`.
#[test]
fn a_bare_contact_transmits_through_its_channel() {
    let mut draw = Draw::new(6);
    let contact = contact_operands(&mut draw, 2, Parts::default());
    let (from, to) = (draw.vector(3), draw.vector(4));
    let zero = vec![Rat::zero(); 2];
    let passed = transit(&contact, &integer(1), &from, &to, &zero, &zero).unwrap();
    assert_eq!(passed.arrive_from[..2], to[1..3]);
    assert_eq!(passed.arrive_to[1..3], from[..2]);
    assert_eq!(passed.arrive_to[0], to[0]);
}

fn run(
    field: &Field,
    parts: Parts,
    seed: u64,
    ticks: usize,
) -> Vec<crate::hnn::propagation::TickBalance> {
    let medium = Medium::generic(field, seed, parts);
    // Ring 1 at phase 1: the contacts 0–1 and 1–2 read Q = 10, so κ = 2^(−10) where β = 2.
    let current = Current::at(field, lift(&[0, 1, 0, 0, 0])).unwrap();
    let mut word = Word::open_on(field, &medium, &current, injection(field, seed + 1)).unwrap();
    (0..ticks).map(|_| word.tick().unwrap()).collect()
}

/// Lean `HNN/Word.word_tick_balance`, lossless: with lossless contacts, `W_s = 0` and `W_c = 0` the
/// exact law keeps the global power constant exactly over every tick, on a chorded field with
/// proper partial isometries and contacts that store and stiffen. The executed word on its
/// lattices (Decision 24) moves it at each tick by exactly its residual (the executed anchors,
/// charts and splits), within the bound its certificates and cells give (Lean
/// `HNN/LatticeWord.{chart_energy_identity, cayley_chart_energy, feedback_tick}`), and by a nonzero
/// residual: the chart is not the exact inverse.
#[test]
fn a_lossless_word_keeps_its_global_power_up_to_its_certified_residual() {
    let parts = Parts {
        stiff: true,
        store: true,
        standing: true,
        ..Parts::default()
    };
    let exact = run(&chorded_field().with_exact_word(), parts, 11, 6);
    let initial = exact[0].before.clone();
    assert!(!initial.is_zero());
    for balance in &exact {
        assert_eq!(balance.after, initial);
        assert!(balance.residual.is_zero() && balance.bound.is_zero());
        assert!(balance.closes());
    }
    let executed = run(&chorded_field(), parts, 11, 6);
    let mut power = executed[0].before.clone();
    for balance in &executed {
        assert!(
            balance.dissipation.is_zero() && balance.resist.is_zero() && balance.contrast.is_zero()
        );
        assert_eq!(balance.before, power);
        assert_eq!(balance.after, &balance.before + &balance.residual);
        assert!(
            balance.closes(),
            "the residual lies within its certified bound"
        );
        power = balance.after.clone();
    }
    assert!(executed.iter().any(|balance| !balance.residual.is_zero()));
}

/// Lean `HNN/LatticeWord.cayley_chart_energy_rowNorm`: the skew element executed through its
/// certified lattice chart `X̂` of `(I − ½K)⁻¹` (`‖1 − (I − ½K)X̂‖∞ ≤ δ`, at most the target) moves
/// the energy by at most `(4nδ + 4(nδ)²)|b|²`, and its balance closes exactly with the chart term
/// `⟨x̄, e⟩` inside its bound `‖x̄‖₁ δ ‖2b‖∞`; the exact law's isometry is the zero chart term.
#[test]
fn the_skew_element_on_its_chart_keeps_its_energy_within_its_certificate() {
    let mut draw = Draw::new(12);
    let lattice = WordLattice::by_rule(16, 6, 6, 4);
    let n = 6;
    let zero = ExactRatMatrix::zero(n, n).unwrap();
    for _ in 0..4 {
        let slices: Vec<(Vec<Rat>, Vec<Rat>)> = (0..n)
            .map(|_| (draw.dyadic_vector(n), draw.dyadic_vector(n)))
            .collect();
        let contrast = draw.dyadic_vector(n);
        let ring = RingOperands::charted(
            integer(2),
            &contrast,
            &zero,
            &zero,
            &slices,
            ChartKey::Ring(0),
            &lattice,
            None,
        )
        .unwrap();
        let reading = ring.chart().unwrap().clone();
        assert!(reading.certificate <= lattice.target());
        let wave = draw.dyadic_vector(n);
        let step = element_step(&ring, &wave, &draw.dyadic_vector(n)).unwrap();
        let (energy, before) = (dot(&step.next, &step.next), dot(&wave, &wave));
        let spread = integer(n as i64) * &reading.certificate;
        let bound = (integer(4) * &spread + integer(4) * &spread * &spread) * &before;
        assert!(
            (&energy - &before).abs() <= bound,
            "cayley_chart_energy_rowNorm"
        );
        let half = rat(1, 2);
        assert_eq!(
            &half * &energy - &half * &before,
            &step.resist + &step.drive + &step.defect
        );
        assert!(step.defect.abs() <= step.bound);
        assert!(!step.defect.is_zero(), "the chart is not the exact inverse");
    }
}

/// The full element on its chart (Lean `HNN/Word.reaction_stage_balance` at an executed chart, the
/// item #62 owes in Lean): with a passive part and a contrast port,
/// `½|s′|² − ½|b|² = ⟨x̄, W_s x̄⟩ + ⟨x̄, W_c c⟩ + ⟨x̄, e⟩` exactly, `e = −R(2b + W_c c)` the chart's
/// equation residual, with `|⟨x̄, e⟩| ≤ ‖x̄‖₁ δ ‖2b + W_c c‖∞`.
#[test]
fn the_element_balance_on_its_chart_closes_with_its_certified_chart_term() {
    let mut draw = Draw::new(13);
    let lattice = WordLattice::by_rule(16, 6, 6, 4);
    let n = 6;
    for _ in 0..4 {
        let slices: Vec<(Vec<Rat>, Vec<Rat>)> = (0..n)
            .map(|_| (draw.dyadic_vector(n), draw.dyadic_vector(n)))
            .collect();
        let ring = RingOperands::charted(
            integer(2),
            &draw.dyadic_vector(n),
            &draw.dyadic_matrix(n, n),
            &draw.dyadic_matrix(n, n).scaled(&rat(1, 8)),
            &slices,
            ChartKey::Ring(0),
            &lattice,
            None,
        )
        .unwrap();
        let (wave, drive) = (draw.dyadic_vector(n), draw.dyadic_vector(n));
        let step = element_step(&ring, &wave, &drive).unwrap();
        let half = rat(1, 2);
        assert_eq!(
            &half * dot(&step.next, &step.next) - &half * dot(&wave, &wave),
            &step.resist + &step.drive + &step.defect
        );
        assert!(step.resist <= Rat::zero());
        assert!(step.defect.abs() <= step.bound);
        // e = −R(2b + W_c c), R the chart's right residual.
        let left = ExactRatMatrix::identity(n)
            .unwrap()
            .subtract(&ring.element().scaled(&half))
            .unwrap();
        let residual = ExactRatMatrix::identity(n)
            .unwrap()
            .subtract(&left.multiply(&ring.solve().unwrap()).unwrap())
            .unwrap();
        let operand = add(
            &scale(&integer(2), &wave),
            &ring.contrast().apply(&drive).unwrap(),
        );
        let e = scale(&-Rat::one(), &residual.apply(&operand).unwrap());
        assert_eq!(dot(&step.midpoint, &e), step.defect);
    }
}

/// Every solve the executed word reads at a cut is a lattice chart whose certificate, read again
/// in ℚ from its exact values, `‖1 − A X̂‖∞`, is the reported one and at most the declared target;
/// the junctions' executed weights sum to one exactly, within their certificate `‖ŵ − w‖₁` of the
/// participation weights.
#[test]
fn every_solve_the_word_executes_is_certified_below_its_target() {
    let field = chorded_field();
    let lattice = *field.word_lattice().unwrap();
    let parts = Parts {
        dissipative: true,
        resist: true,
        contrast: true,
        stiff: true,
        store: true,
        standing: true,
    };
    let medium = Medium::generic(&field, 14, parts);
    let current = Current::at(&field, lift(&[0, 1, 0, 0, 0])).unwrap();
    let operands = Operands::at_cut(&field, &medium, &current).unwrap();
    let row_norm = |m: &ExactRatMatrix| {
        (0..m.rows())
            .map(|i| m.row(i).unwrap().iter().map(|x| x.abs()).sum::<Rat>())
            .max()
            .unwrap()
    };
    let certify = |operator: &ExactRatMatrix, chart: &ExactRatMatrix| {
        let n = operator.rows();
        row_norm(
            &ExactRatMatrix::identity(n)
                .unwrap()
                .subtract(&operator.multiply(chart).unwrap())
                .unwrap(),
        )
    };
    for ring in operands.rings() {
        let n = ring.width();
        let left = ExactRatMatrix::identity(n)
            .unwrap()
            .subtract(&ring.element().scaled(&rat(1, 2)))
            .unwrap();
        let reading = ring.chart().unwrap();
        assert_eq!(certify(&left, &ring.solve().unwrap()), reading.certificate);
        assert!(reading.certificate <= lattice.target());
    }
    for contact in operands.contacts() {
        let reading = contact.chart().unwrap();
        assert_eq!(
            certify(contact.operator(), &contact.solve().unwrap()),
            reading.certificate
        );
        assert!(reading.certificate <= lattice.target());
    }
    for ring in 0..field.rings().len() {
        let (executed, exact) = (operands.weights(ring), operands.exact_weights(ring));
        assert_eq!(executed.iter().sum::<Rat>(), Rat::one());
        let spread: Rat = executed.iter().zip(exact).map(|(a, b)| (a - b).abs()).sum();
        assert_eq!(&spread, operands.junction_certificate(ring));
        let unit = lattice.chart().unit();
        assert!(spread <= integer(executed.len() as i64) * unit);
    }
}

/// Lean `HNN/Word.word_tick_balance`: with dissipation, a passive element part and a contrast port
/// together, `P(t+1) = P(t) − h Σ ω*Dω + (h/2) Σ Y ⟨x̄, W_s x̄⟩ + Π_c` exactly at every tick, the
/// dissipation `≥ 0`, the passive term `≤ 0`, and `Π_c` of both signs over starting states (with
/// `W_c` at 1/8 of the other operands' scale, as in `power.py`; a dominant `W_c` pumps, since
/// `(I − ½K)⁻¹` has a positive-definite symmetric part for passive `K`).
#[test]
fn the_global_power_balance_closes_exactly_at_every_tick() {
    let field = chorded_field();
    let parts = Parts {
        dissipative: true,
        resist: true,
        contrast: true,
        stiff: true,
        store: true,
        standing: true,
    };
    let mut signs = std::collections::BTreeSet::new();
    for seed in 0..12 {
        for balance in run(&field, parts, 20 + seed, 2) {
            assert!(balance.closes());
            assert!(balance.dissipation >= Rat::zero());
            assert!(balance.resist <= Rat::zero());
            signs.insert(balance.contrast > Rat::zero());
        }
    }
    assert_eq!(signs.len(), 2, "the contrast port's power takes both signs");
}

/// Lean `HNN/Propagation.tick_causal_cone` (guard 14): an impulse at any ring is supported, after
/// `t` ticks, exactly within the ball of radius `t` contact hops, and the front reaches radius `t`.
#[test]
fn an_impulse_propagates_one_contact_per_tick_inside_its_cone() {
    let field = six_cycle();
    let medium = Medium::generic(
        &field,
        30,
        Parts {
            dissipative: true,
            stiff: true,
            store: true,
            ..Parts::default()
        },
    );
    let current = Current::at_rest(&field);
    // The operands are fixed at the cut, so one chart serves every origin; the six-cycle's diameter
    // is three hops, so three ticks carry the front across it.
    let operands = Operands::at_cut(&field, &medium, &current).unwrap();
    for origin in [0, 1, 4] {
        let mut storage: Vec<Vec<Rat>> = field
            .rings()
            .iter()
            .map(|ring| vec![Rat::zero(); ring.width()])
            .collect();
        storage[origin] = Draw::new(origin as u64).vector(6);
        let mut word = Word::on_operands(&field, operands.clone(), storage).unwrap();
        for t in 1..=3 {
            word.tick().unwrap();
            let support = word.support();
            for (ring, carried) in support.iter().enumerate() {
                let distance = field.distance(origin, ring).unwrap();
                if distance > t {
                    assert!(!carried, "ring {ring} at {distance} hops after {t} ticks");
                }
                if distance == t {
                    assert!(carried, "the front reaches ring {ring} at tick {t}");
                }
            }
        }
    }
}

/// The measured cone of the design (`bits2.py`): with bare contacts on full channels, the front of
/// an impulse at ring 1 of the six-cycle is rings `{0, 2}` after one tick, then `{0, 1, 2, 3, 5}`,
/// then all six.
#[test]
fn the_six_cycle_front_matches_the_measured_cone() {
    let field = six_cycle();
    let medium = Medium::generic(&field, 31, Parts::default());
    let current = Current::at_rest(&field);
    let mut storage = vec![vec![Rat::zero(); 6]; 6];
    storage[1] = Draw::new(2).vector(6);
    let mut word = Word::open_on(&field, &medium, &current, storage).unwrap();
    let reached = |word: &Word<'_>| -> Vec<usize> {
        word.front()
            .iter()
            .enumerate()
            .filter(|(_, carried)| **carried)
            .map(|(ring, _)| ring)
            .collect()
    };
    word.tick().unwrap();
    assert_eq!(reached(&word), vec![0, 2]);
    word.tick().unwrap();
    assert_eq!(reached(&word), vec![0, 1, 2, 3, 5]);
    word.tick().unwrap();
    assert_eq!(reached(&word), vec![0, 1, 2, 3, 4, 5]);
}

/// A path of rings placed by campaign 1's placement rule (node `k` of period `d` at the quarter
/// turn `⌊4k/d⌋`, [`FieldDeclaration::quarter_turn`]), joined `0–1–…` on their common nodes with the
/// declared exponents, source ring 0, `|A| = 2`, the receiver at the last ring with aperture 1 and
/// campaign 1's tolerance `1/16`, on the exponent lattice `L`.
fn quarter_turn_path(periods: &[u64], exponents: &[i64], grain: u64) -> FieldDeclaration {
    FieldDeclaration {
        rings: periods
            .iter()
            .map(|&period| crate::hnn::field::RingDeclaration {
                placements: (0..period)
                    .map(|node| FieldDeclaration::quarter_turn(node, period))
                    .collect(),
                ..ring(period, vec![0])
            })
            .collect(),
        contacts: exponents
            .iter()
            .enumerate()
            .map(|(from, &exponent)| {
                super::support::contact(
                    from,
                    from + 1,
                    periods[from].min(periods[from + 1]) as usize,
                    exponent,
                )
            })
            .collect(),
        loops: Vec::new(),
        sources: vec![0],
        offsets: vec![1],
        alphabet: 2,
        step: integer(1),
        exponent_grain: grain,
        receivers: vec![crate::hnn::field::ReceiverDeclaration {
            ring: periods.len() - 1,
            aperture: 1,
            tolerance: rat(1, 16),
            regions: crate::hnn::masses::Regions::PrecedingCell,
        }],
        crib: crate::hnn::field::CribDeclaration {
            window: 16,
            offset: 1,
        },
        population: 1 << 20,
        lattice: Default::default(),
    }
}

/// One exponent per contact: `s_a = −β_a Q_a / 2` from the pair quadrance, carried as `2^(n_a)` on
/// campaign 1's lattice (`L = 1`, phase class 0); with `L = 2` and `β = 1` an odd quadrance gives
/// phase class 1, which campaign 1 does not carry and refuses at the cut (on campaign 1's first
/// two rings, periods 5 and 7, by its placement rule).
#[test]
fn the_contact_exponent_is_a_carry_and_a_phase_class() {
    let field = &Field::declare(quarter_turn_path(&[5, 7], &[2], 1).by_lattice_rule()).unwrap();
    // Ring 0 at phase 3 sits at the quarter turn ⌊12/5⌋ = 2, opposite ring 1's node 0: Q = 4.
    let current = Current::at(field, lift(&[3, 0])).unwrap();
    let reading = contact_exponent(field, 0, current.lift()).unwrap();
    assert_eq!(reading.quadrance, integer(4));
    assert_eq!(reading.exponent, integer(-4));
    assert_eq!(reading.carry, BigInt::from(-4));
    assert_eq!(reading.phase, 0);
    let medium = Medium::initial(field, 1);
    let operands = Operands::at_cut(field, &medium, &current).unwrap();
    assert_eq!(
        operands.contacts()[0].conductance(),
        &(integer(2) / Rat::from_integer(BigInt::one() << 4u32))
    );
    // With L = 2, β = 1 is on the lattice ℤ; ring 1 raised to height 1 makes every quadrance
    // against ring 0 odd (its horizontal part is 2 − 2p·q, even), so s = −Q/2 has phase class 1.
    let mut declared = quarter_turn_path(&[5, 7], &[1], 2);
    for placement in &mut declared.rings[1].placements {
        placement.z = integer(1);
    }
    let fine = Field::declare(declared.by_lattice_rule()).unwrap();
    let odd = Current::at_rest(&fine);
    let reading = contact_exponent(&fine, 0, odd.lift()).unwrap();
    assert_eq!(
        (
            reading.quadrance.clone(),
            reading.carry.clone(),
            reading.phase
        ),
        (integer(1), BigInt::from(-1), 1)
    );
    let medium = Medium::initial(&fine, 1);
    assert!(matches!(
        Operands::at_cut(&fine, &medium, &odd),
        Err(HnnError::ExponentPhase {
            contact: 0,
            phase: 1,
            grain: 2
        })
    ));
}

/// Review C2: the path attenuation reads the least `Σ β_a Q_a / 2` from the source to the
/// receiver at a cut, and the path is open when `2^(−x)` is at least the receiver's grain `1/16`.
/// At rest every `Q = 0`; one contact across a diameter (`Q = 4`, `β = 2`) attenuates by exactly
/// the grain and stays open; two such contacts in series shield the receiver. (How often campaign
/// 1's declared field is open over its cut is a measurement: `hnn_lattice_growth`.)
#[test]
fn the_path_attenuation_opens_at_the_receivers_grain() {
    let field =
        &Field::declare(quarter_turn_path(&[5, 7, 11], &[2, 2], 1).by_lattice_rule()).unwrap();
    let receiver = &field.receivers()[0];
    let hops = field.first_epoch(receiver.ring).unwrap() + receiver.aperture - 1;
    let at = |phases: &[i64]| {
        path_attenuation(
            field,
            Current::at(field, lift(phases)).unwrap().lift(),
            2,
            hops,
            16,
        )
        .unwrap()
    };
    let rest = at(&[0, 0, 0]);
    assert_eq!((rest.exponent, rest.open), (Rat::zero(), true));
    // Ring 1 at phase 4 sits at the quarter turn ⌊16/7⌋ = 2, a diameter from ring 0 at rest; ring 2
    // at phase 6 sits there too (⌊24/11⌋ = 2), and at rest across the diameter again.
    let one = at(&[0, 4, 6]);
    assert_eq!((one.exponent, one.open), (integer(4), true));
    let two = at(&[0, 4, 0]);
    assert_eq!((two.exponent, two.open), (integer(8), false));
}

/// Lean `HNN/Propagation.tick_well_defined`: `M_a` is invertible for squared carriers at every
/// contact, and `I − ½K_r` for every passive element, whatever the sheet classes; the declared
/// initial constitution opens a word at rest.
#[test]
fn every_local_solve_is_well_defined_for_passive_squared_carriers() {
    let field = small_field(
        &[3, 4, 2],
        vec![
            super::support::contact(0, 1, 2, 2),
            super::support::contact(1, 2, 1, 2),
        ],
        2,
    );
    for seed in 0..6 {
        let medium = Medium::generic(
            &field,
            seed,
            Parts {
                dissipative: true,
                resist: true,
                contrast: true,
                stiff: true,
                store: true,
                standing: true,
            },
        );
        let current = Current::at(&field, lift(&[seed as i64 % 3, 1, 0])).unwrap();
        assert!(Operands::at_cut(&field, &medium, &current).is_ok());
    }
    let field = chain();
    let medium = Medium::initial(&field, 2);
    assert!(Operands::at_cut(&field, &medium, &Current::at_rest(&field)).is_ok());
}

// -------------------------------------------------------------------------------------------
// the integral chart changes no value

fn termwise_dot(a: &[Rat], b: &[Rat]) -> Rat {
    a.iter().zip(b).fold(Rat::zero(), |sum, (x, y)| sum + x * y)
}

fn termwise_product(a: &ExactRatMatrix, b: &ExactRatMatrix) -> Vec<Vec<Rat>> {
    (0..a.rows())
        .map(|i| {
            (0..b.columns())
                .map(|j| {
                    (0..a.columns()).fold(Rat::zero(), |sum, k| {
                        sum + a.get(i, k).unwrap() * b.get(k, j).unwrap()
                    })
                })
                .collect()
        })
        .collect()
}

/// The rational elimination the integral chart replaced, entry by entry: the same pivot rules
/// (first nonzero diagonal by the declared order, else the first nonzero off-diagonal pair).
fn termwise_inertia(
    form: &crate::ratio::linear::inertia::SymmetricForm,
    order: crate::ratio::linear::inertia::PivotOrder,
) -> crate::ratio::linear::inertia::InertiaSchedule {
    use crate::ratio::linear::inertia::{InertiaSchedule, PivotOrder, PivotStep};
    use num_traits::Signed;
    let n = form.extent();
    let mut a: Vec<Vec<Rat>> = (0..n)
        .map(|i| (0..n).map(|j| form.at(i, j).clone()).collect())
        .collect();
    let mut alive: Vec<usize> = (0..n).collect();
    let mut steps = Vec::new();
    let pick = |candidates: Vec<(usize, usize, Rat)>| -> Option<(usize, usize)> {
        let mut best: Option<(usize, usize, Rat)> = None;
        for (i, j, value) in candidates {
            let take = best.as_ref().is_none_or(|(bi, bj, bv)| match order {
                PivotOrder::FirstNonzero => (i, j) < (*bi, *bj),
                PivotOrder::LastNonzero => (i, j) > (*bi, *bj),
                PivotOrder::SmallestMagnitude => {
                    value.abs() < bv.abs() || (value.abs() == bv.abs() && (i, j) < (*bi, *bj))
                }
                PivotOrder::LargestMagnitude => {
                    value.abs() > bv.abs() || (value.abs() == bv.abs() && (i, j) < (*bi, *bj))
                }
            });
            if take {
                best = Some((i, j, value));
            }
        }
        best.map(|(i, j, _)| (i, j))
    };
    while !alive.is_empty() {
        let diagonal = pick(
            alive
                .iter()
                .filter(|i| !a[**i][**i].is_zero())
                .map(|i| (*i, *i, a[*i][*i].clone()))
                .collect(),
        );
        if let Some((i, _)) = diagonal {
            steps.push(PivotStep::Diagonal {
                index: i,
                negative: a[i][i].is_negative(),
            });
            let pivot = a[i][i].clone();
            let rest: Vec<usize> = alive.iter().copied().filter(|k| *k != i).collect();
            let column: Vec<Rat> = rest.iter().map(|k| a[*k][i].clone()).collect();
            for (x, j) in rest.iter().enumerate() {
                for (y, k) in rest.iter().enumerate() {
                    a[*j][*k] -= &column[x] * &column[y] / &pivot;
                }
            }
            alive = rest;
            continue;
        }
        let mut pairs = Vec::new();
        for (position, low) in alive.iter().enumerate() {
            for high in &alive[position + 1..] {
                if !a[*low][*high].is_zero() {
                    pairs.push((*low, *high, a[*low][*high].clone()));
                }
            }
        }
        if let Some((low, high)) = pick(pairs) {
            steps.push(PivotStep::ZeroDiagonalPair { low, high });
            let pivot = a[low][high].clone();
            let rest: Vec<usize> = alive
                .iter()
                .copied()
                .filter(|k| *k != low && *k != high)
                .collect();
            let (to_low, to_high): (Vec<Rat>, Vec<Rat>) = rest
                .iter()
                .map(|k| (a[*k][low].clone(), a[*k][high].clone()))
                .unzip();
            for (x, j) in rest.iter().enumerate() {
                for (y, k) in rest.iter().enumerate() {
                    a[*j][*k] -= (&to_low[x] * &to_high[y] + &to_high[x] * &to_low[y]) / &pivot;
                }
            }
            alive = rest;
            continue;
        }
        steps.push(PivotStep::ZeroRemainder {
            extent: alive.len(),
        });
        alive.clear();
    }
    InertiaSchedule { order, steps }
}

/// **The integral chart changes no value** (small fixtures, against the termwise arithmetic it
/// replaced): a reduced ratio is canonical, so dot products, matrix products and applications, the
/// inverse, the composition's rank-one sums and factor pulls, the grain reading and the encoder
/// covector equal their termwise sums exactly, and the fraction-free inertia walks the rational
/// elimination's schedule. The same equality on campaign 1's real cut is a release measurement
/// (`research/notebook/hnn_design/README.md`, `hnn_lattice_growth`).
#[test]
fn the_integral_chart_equals_the_termwise_arithmetic() {
    use crate::hnn::moment::SourceMoment;
    use crate::hnn::receiving::GrainCell;
    use crate::ratio::linear::inertia::{PivotOrder, SymmetricForm, inertia_with_schedule};
    use crate::ratio::linear::vector::{IntegralMatrix, combination, integral};
    let mut draw = Draw::new(97);
    for n in [1usize, 3, 6] {
        let (a, b, v) = (
            draw.matrix(n, n + 1),
            draw.matrix(n + 1, n),
            draw.vector(n + 1),
        );
        assert_eq!(dot(&v, &v), termwise_dot(&v, &v));
        let applied: Vec<Rat> = (0..n)
            .map(|i| termwise_dot(a.row(i).unwrap(), &v))
            .collect();
        assert_eq!(a.apply(&v).unwrap(), applied);
        assert_eq!(a.multiply(&b).unwrap().to_rows(), termwise_product(&a, &b));
        let square = ExactRatMatrix::identity(n)
            .unwrap()
            .scaled(&integer(3))
            .add(&draw.matrix(n, n))
            .unwrap();
        if let Ok(inverse) = square.inverse() {
            assert_eq!(
                termwise_product(&square, &inverse),
                ExactRatMatrix::identity(n).unwrap().to_rows()
            );
        }
        // Σ_t w_t l_t r_tᵀ, (N + Nᵀ) F and Σ_c w_c v_c.
        let terms: Vec<(Rat, Vec<Rat>, Vec<Rat>)> = (0..3)
            .map(|_| (draw.rational(), draw.vector(n), draw.vector(n)))
            .collect();
        let charts: Vec<_> = terms
            .iter()
            .map(|(_, l, r)| (integral(l), integral(r)))
            .collect();
        let sum = IntegralMatrix::outer_sum(
            n,
            n,
            terms.iter().zip(&charts).map(|((w, ..), (l, r))| (w, l, r)),
        );
        let termwise: Vec<Vec<Rat>> = (0..n)
            .map(|i| {
                (0..n)
                    .map(|j| terms.iter().map(|(w, l, r)| w * &l[i] * &r[j]).sum())
                    .collect()
            })
            .collect();
        assert_eq!(sum.to_rows(), termwise);
        let factor = draw.matrix(n, 2);
        let pulled: Vec<Vec<Rat>> = (0..n)
            .map(|i| {
                (0..2)
                    .map(|c| {
                        (0..n)
                            .map(|k| {
                                (&termwise[i][k] + &termwise[k][i]) * factor.get(k, c).unwrap()
                            })
                            .sum::<Rat>()
                    })
                    .map(|x| -x)
                    .collect()
            })
            .collect();
        assert_eq!(sum.symmetric_times(&factor, true).unwrap(), pulled);
        let weighted: Vec<(Rat, _)> = terms
            .iter()
            .zip(&charts)
            .map(|((w, ..), (l, _))| (w.clone(), l))
            .collect();
        let combined: Vec<Rat> = (0..n)
            .map(|i| terms.iter().map(|(w, l, _)| w * &l[i]).sum())
            .collect();
        assert_eq!(
            combination(n, weighted.iter().map(|(w, c)| (w, *c))),
            combined
        );
    }
    // The grain reading: floor readings of signed rationals.
    for _ in 0..24 {
        let value = draw.rational() * integer(draw.below(40) as i64 - 20) / integer(7);
        let grain = draw.below(16) as u64 + 1;
        let carry = value.floor();
        let scaled = (&value - &carry) * integer(grain as i64);
        let phase = scaled.floor();
        let cell = GrainCell::of(&value, grain);
        assert_eq!(Rat::from_integer(cell.carry.clone()), carry);
        assert_eq!(integer(cell.phase as i64), phase);
        assert_eq!(cell.fibre, (scaled - phase) / integer(grain as i64));
    }
    // The encoder covector: Σ_c (P^(c−τ) g) ⊗ M[c], termwise.
    let field = small_field(&[3, 2], vec![super::support::contact(0, 1, 1, 0)], 1);
    let mut current = Current::at_rest(&field);
    let mut moment = SourceMoment::open(&field, &current);
    let cells: Vec<usize> = (0..11).map(|_| draw.below(2)).collect();
    moment.ingest(&field, &mut current, &cells).unwrap();
    let ring = field.ring(0);
    let covector = draw.vector(ring.width());
    let chart = moment
        .encoder_covector(&field, &current, 0, &covector)
        .unwrap();
    for row in 0..ring.width() {
        for code in 0..field.alphabet() {
            let termwise: Rat = (0..ring.period() as usize)
                .map(|phase| {
                    let turned =
                        ring.rotate(&covector, &(BigInt::from(phase) - &current.lift()[0]));
                    &turned[row] * integer(moment.phase_counts(0, phase).unwrap()[code] as i64)
                })
                .sum();
            assert_eq!(chart.get(row, code).unwrap(), &termwise);
        }
    }
    // The inertia's schedule, on forms with zero diagonals and every pivot order.
    for extent in [1usize, 2, 4, 7] {
        for _ in 0..6 {
            let mut rows = vec![vec![Rat::zero(); extent]; extent];
            for i in 0..extent {
                for j in i..extent {
                    if draw.below(3) != 0 {
                        let value = draw.rational();
                        rows[i][j] = value.clone();
                        rows[j][i] = value;
                    }
                }
            }
            let form = SymmetricForm::from_rows(rows).unwrap();
            for order in [
                PivotOrder::FirstNonzero,
                PivotOrder::LastNonzero,
                PivotOrder::SmallestMagnitude,
                PivotOrder::LargestMagnitude,
            ] {
                assert_eq!(
                    inertia_with_schedule(&form, order).1,
                    termwise_inertia(&form, order)
                );
            }
        }
    }
}
