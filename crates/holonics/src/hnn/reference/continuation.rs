//! Focused consumer of the native comparison/contact return, reusing the existing tick field
//! and an uncoupled direct sum of its Floquet node material. No authored factor covector enters.
use super::*;
use crate::ratio::rat;
use crate::hnn::ring::{PumpDeclaration, PumpStep, ResonatorMaterial};
use crate::hnn::word::continuation::ContactCut;
use crate::holon::parametron::Carrier as ParametronCarrier;
use std::sync::Arc;
use crate::hnn::tests::learning;
use crate::hnn::tests::support;
// Existing tick-law field (support::small_field) and the direct sum of Floquet node materials
// (tests/floquet.rs::node). Period two is the smallest admitted ring. The contact meets one node;
// the two uncoupled pumped complex modes remove the cycle fixture's internal mixing.
fn boundary() -> Field {
    support::small_field(&[2, 2], vec![support::contact(0, 1, 1, 0)], 1)
}
fn resonant(field: &Field, theta: Constitution) -> Constitution {
    let width = field.ring(0).width();
    let identity = ExactRatMatrix::identity(width).unwrap();
    let pump = PumpDeclaration::new(
        rat(1, 16), ParametronCarrier::new(Rat::one(), Rat::zero()).unwrap(), PumpStep::Half,
    ).unwrap();
    theta.with_ring_resonator(field, 0, ResonatorMaterial::new(
        identity.clone(), identity, ExactRatMatrix::zero(width, width).unwrap(), Some(pump),
    ).unwrap()).unwrap()
}

// This finite control's channel grain is derived from its actual coarse comparison receipt.
// At unit 2^-6 and certified step 2^-6, the largest exact released factor displacement is
// 979302663067977851/11028940175733273133056; the lattice control's is 23937/268435456.
// Both lie strictly between 2^-14 and 2^-13. Seven rebase levels are therefore the least whose
// half-unit is below those responses: unit 2^-13. No caller step, covector, target or pump changes.
// Rebase publishes a new native commit before the actual comparison is recomputed.
fn resolved(field: &Field) -> Constitution {
    resonant(field, learning::generic(field, 81))
        .rebased(Locus::Channel(0), 7).unwrap()
}

fn contact_comparison(
    field: &Field, theta: &Constitution, current: &Current,
    source: &Arc<SourceMoment>, charts: &mut Charts,
) -> (ContactCut, Deposit) {
    let started = std::time::Instant::now();
    let phases = learning::phases(field, theta, current);
    let mut word = Word::open_source(field, theta, current, source.clone(), charts).unwrap();
    word.run(phases.last_epoch() + 1).unwrap();
    eprintln!("unit forward elapsed_ms={}", started.elapsed().as_millis());
    let targets: Vec<_> = (0..phases.aperture()).map(|i| (i+1)%field.alphabet()).collect();
    let (ratio, returned) = word.compare_contact_storage(0, 0, &targets).unwrap();
    assert_eq!(ratio.stations().len(), targets.len());
    let back = returned.pullback.present().unwrap();
    assert!(back.transits[0].iter().any(|tick| tick.solved.iter().any(|x| !x.is_zero())));
    let cut = returned.forward.into_present().unwrap();
    let deposit = returned.deposit.into_present().unwrap();
    assert_eq!(deposit.factors().len(), 1);
    eprintln!("unit comparison-deposit-binding elapsed_ms={}", started.elapsed().as_millis());
    (cut, deposit)
}

#[test]
fn exact_bound_comparison_storage_return_continues_one_actual_pump() {
    native_storage_continuation(true);
}

#[test]
fn lattice_bound_material_return_reports_unresolved_next_contact_response() {
    native_storage_continuation(false);
}

fn native_storage_continuation(exact: bool) {
    let started = std::time::Instant::now();
    {
        let field = if exact {
            boundary().with_exact_word()
        } else {
            boundary()
        };
        let theta = resolved(&field);
        let (current, source) = learning::moment(&field, 82, 9);
        let source = Arc::new(source);
        let mut charts = Charts::new();
        let (cut, deposit) = contact_comparison(&field, &theta, &current, &source, &mut charts);
        let change = cut.change().clone();
        let next_tick = cut.next_tick();
        let before_operands = if exact {
            Operands::exact_at_cut(&field, &theta, &current).unwrap()
        } else {
            Operands::at_cut_charted(&field, &theta, &current, &mut charts).unwrap()
        };
        let nothing: Vec<_> = change
            .storage
            .iter()
            .map(|s| vec![Rat::zero(); s.len()])
            .collect();
        let mut predecessor =
            Word::continuing(&field, before_operands, &change, &nothing, next_tick).unwrap();
        eprintln!("native storage before deposit elapsed_ms={}", started.elapsed().as_millis());
        let (successor, returned) = cut
            .continue_deposited(&field, &current, &source, &deposit, &mut charts)
            .unwrap();
        eprintln!("native storage continued-open elapsed_ms={}", started.elapsed().as_millis());
        assert_eq!(successor.commit(), theta.commit() + 1);
        let material = returned.deposit.present().unwrap();
        eprintln!("native material step={} stepped={} vanished={:?} unit={} statistic={} released={:?} carried={:?}",
            material.family_step(Locus::Channel(0), crate::hnn::constitution::Family::Factor(0)),
            material.stepped, material.vanished, theta.lattice(Locus::Channel(0)).unwrap().unit(),
            successor.contact_scales(0)[0], material.released, successor.carried_remainders());
        assert!(material.stepped > 0);
        let receipt = returned.receipt;
        assert_eq!(
            &receipt.committed - &receipt.before,
            receipt.deposition_work
        );
        assert!(!receipt.deposition_work.is_zero());
        assert_eq!(
            &receipt.opening - &receipt.committed,
            receipt.opening_difference
        );
        let mut next = returned.forward.into_present().unwrap();
        // The deposit holds each contact's canonical state `(u, π = C w)`: the opened rate, with
        // what its split left in the opening remainder, solves `C′ w′ = C w`; the displacement,
        // the waves and the storage open as the cut left them.
        let opened = next.change().unwrap();
        assert_eq!(opened.storage, change.storage);
        assert_eq!(opened.arrivals, change.arrivals);
        for (a, (state, held)) in change.states.iter().zip(&opened.states).enumerate() {
            let (storage, moved) = (
                predecessor.operands().contacts()[a].forms().0,
                next.operands().contacts()[a].forms().0,
            );
            let [displacement, rate] = &next.state_remainders()[a];
            assert!(displacement.iter().all(Rat::is_zero));
            assert_eq!(held[0], state[0]);
            let rate = crate::ratio::linear::vector::add(&held[1], rate);
            assert_eq!(moved.apply(&rate).unwrap(), storage.apply(&state[1]).unwrap());
            if exact {
                assert_ne!(held[1], state[1], "the deposit moved the contact's mass");
            }
        }
        assert_eq!(next.opened_at(), next_tick);
        assert_eq!(next.clock().ticks(), BigUint::from(next_tick));
        for (ring, state) in change.resonators.iter().enumerate() {
            if ring == 0 {
                assert!(state.is_some());
                assert_eq!(&next.resonances()[ring].as_ref().unwrap().state, state.as_ref().unwrap());
            } else {
                assert!(state.is_none());
                assert!(next.resonances()[ring].is_none());
            }
        }
        next.run(1).unwrap();
        predecessor.run(1).unwrap();
        eprintln!("native storage next tick elapsed_ms={}", started.elapsed().as_millis());
        assert_eq!(next.recorded()[0].states, opened.states);
        assert_eq!(next.recorded()[0].arrivals, change.arrivals);
        assert!(next.field_balances()[0].closes());
        assert!(
            next.resonances()
                .iter()
                .flatten()
                .all(|r| r.steps[0].closes())
        );
        if exact {
            assert_ne!(next.change().unwrap().states[0], predecessor.change().unwrap().states[0]);
        } else {
            // The material changes, but its next contact point has the same representative at
            // this declared word/chart grain. Read the chart and split terms and released
            // remainders explicitly; do not assert a resolved coordinate response here.
            assert_eq!(next.change().unwrap().states[0], predecessor.change().unwrap().states[0]);
            eprintln!("native unresolved next response transient_unit={} successor_transit_chart={} predecessor_transit_chart={} successor_transit_split={} predecessor_transit_split={} successor_remainders={:?} predecessor_remainders={:?}",
                field.word_lattice().unwrap().transient().unit(),
                next.field_balances()[0].transit_chart, predecessor.field_balances()[0].transit_chart,
                next.field_balances()[0].transit_split, predecessor.field_balances()[0].transit_split,
                next.released().unwrap().remainders, predecessor.released().unwrap().remainders);
        }
        eprintln!("native returned work={} opening_difference={} next_tick={} reached={:?} next={:?} predecessor_next={:?} field_balance_closes={}",
            receipt.deposition_work, receipt.opening_difference, next_tick,
            change.states[0], next.change().unwrap().states[0],
            predecessor.change().unwrap().states[0], next.field_balances()[0].closes());
        if !exact {
            assert!(next.operands().contacts()[0].chart().is_some());
        }
    }
}

#[test]
fn native_contact_return_refuses_another_source_and_stale_deposit_without_cache_writes() {
    let field = boundary().with_exact_word();
    let theta = resolved(&field);
    let (current, source) = learning::moment(&field, 82, 9);
    let source = Arc::new(source);
    let mut charts = Charts::new();
    let (cut, deposit) = contact_comparison(&field, &theta, &current, &source, &mut charts);
    let before = charts.clone();
    let wrong = Arc::new((*source).clone());
    assert!(
        cut.continue_deposited(&field, &current, &wrong, &deposit, &mut charts)
            .is_err()
    );
    assert_eq!(charts, before);
    let (cut, deposit) = contact_comparison(&field, &theta, &current, &source, &mut charts);
    let stale = Deposit::new(
        theta.commit() + 1,
        vec![],
        deposit.factors().to_vec(),
        deposit.loci().to_vec(),
    )
    .with_reach(deposit.reach().unwrap().clone());
    let before = charts.clone();
    assert!(matches!(
        cut.continue_deposited(&field, &current, &source, &stale, &mut charts),
        Err(HnnError::Shape { what: "the deposited contact covector is this cut's actual comparison return", .. })
    ));
    assert_eq!(charts, before);
}

// [derivation] **At held momentum a storage deposit is felt through the motion itself, and the
// lattice word opens the held momentum in the rate's remainder.** The deposit holds the contact's
// canonical state `(u, π = C w)`, so the successor opens at `C′ w′ = C w` and the transit's right
// side `h(α_g − α_h) + 2C w − hKu` is unchanged: under the exact solve `m′(ζ′ − ζ) = −(G/h)ΔC ζ =
// −ΔC(w + w⁺)`, `w⁺ = (G/h)ζ − w` the predecessor's next rate. Summed, the midpoint rates are the
// displacement's travel. On the lattice the successor's opening rate is the split of `w + δ`,
// `C′δ = −ΔC w`: while the representatives agree the solve reads them alone, so the per-tick
// response is the 2026-10-02 identity `ΔC(ŵ − ŵ⁺)`, the solve remainders differ by the accumulated
// image difference, and the rate remainders by the opening's `δ` plus the accumulated rate-image
// difference. Record
// `research/records/2026-10-02_A_STORAGE_DEPOSIT_IS_FELT_ONLY_THROUGH_THE_RATE_S_JUMP_AND_THE_WORD_HOLDS_IT_BELOW_ONE_UNIT.md`
// §9; Lean `HNN/StorageResolution` (§1–§4 at one rate), the held-momentum statements in #62.
#[test]
fn storage_deposit_at_held_momentum_is_felt_through_the_motion() {
    storage_response(true, 1);
    storage_response(false, 4096);
}

fn storage_response(exact: bool, ticks: usize) {
    use crate::ratio::linear::vector::{add, sub};
    let started = std::time::Instant::now();
    let two = Rat::from_integer(2.into());
    let scale = |c: &Rat, v: &[Rat]| v.iter().map(|x| c * x).collect::<Vec<_>>();
    let field = if exact { boundary().with_exact_word() } else { boundary() };
    let theta = resolved(&field);
    let (current, source) = learning::moment(&field, 82, 9);
    let source = Arc::new(source);
    let mut charts = Charts::new();
    let (cut, deposit) = contact_comparison(&field, &theta, &current, &source, &mut charts);
    let change = cut.change().clone();
    let next_tick = cut.next_tick();
    let before_operands = if exact {
        Operands::exact_at_cut(&field, &theta, &current).unwrap()
    } else {
        Operands::at_cut_charted(&field, &theta, &current, &mut charts).unwrap()
    };
    let nothing: Vec<_> = change.storage.iter().map(|s| vec![Rat::zero(); s.len()]).collect();
    let mut predecessor =
        Word::continuing(&field, before_operands, &change, &nothing, next_tick).unwrap();
    let (_, returned) = cut
        .continue_deposited(&field, &current, &source, &deposit, &mut charts)
        .unwrap();
    let mut successor = returned.forward.into_present().unwrap();
    let (before, after) = (&predecessor.operands().contacts()[0], &successor.operands().contacts()[0]);
    let h = predecessor.operands().step().clone();
    assert_eq!(&h, successor.operands().step());
    let g = before.conductance().clone();
    assert_eq!(&g, after.conductance());
    assert_eq!(before.forms().1, after.forms().1);
    assert_eq!(before.forms().2, after.forms().2);
    let storage = before.forms().0.clone();
    let delta = after.forms().0.subtract(&storage).unwrap();
    let operator = after.operator().clone();
    let inverse = operator.inverse().unwrap();
    let unit = if exact { Rat::zero() } else { field.word_lattice().unwrap().transient().unit() };
    eprintln!("storage response exact={exact} h={h} G={g} G/h={} unit={unit} dC={:?} m'={:?}",
        &g / &h, delta.to_rows(), operator.to_rows());
    assert_eq!(predecessor.solve_remainders(), successor.solve_remainders());
    // The opening holds the momentum: `C′(ŵ′ + ρ′) = C w`, and the jump `δ = ŵ′ + ρ′ − w`.
    let rate0 = predecessor.change().unwrap().states[0][1].clone();
    let opened = successor.change().unwrap().states[0][1].clone();
    let opening_remainder = successor.state_remainders()[0][1].clone();
    assert!(predecessor.state_remainders()[0][1].iter().all(Rat::is_zero));
    let held = add(&opened, &opening_remainder);
    assert_eq!(after.forms().0.apply(&held).unwrap(), storage.apply(&rate0).unwrap());
    let jump = sub(&held, &rate0);
    assert!(jump.iter().any(|x| !x.is_zero()), "the deposit moved the contact's mass");
    eprintln!("storage opening exact={exact} w={rate0:?} jump={jump:?} representative_moved={} remainder={opening_remainder:?}",
        opened != rate0);
    let (mut accumulated, mut material, mut rate_images, mut parted) = (
        vec![Rat::zero(); rate0.len()], vec![Rat::zero(); rate0.len()],
        vec![Rat::zero(); rate0.len()], None,
    );
    for tick in 0..ticks {
        let (pc, sc) = (predecessor.change().unwrap(), successor.change().unwrap());
        if !exact && pc != sc {
            parted = Some(tick);
            break;
        }
        assert_eq!(pc.states[0][0], sc.states[0][0], "one displacement");
        let r_before = predecessor.solve_remainders()[0].clone();
        let r_after = successor.solve_remainders()[0].clone();
        predecessor.run(1).unwrap();
        successor.run(1).unwrap();
        let (p, s) = (predecessor.recorded().last().unwrap(), successor.recorded().last().unwrap());
        let rate = &p.states[0][1];
        // ζ = ζ̂ + r_(t+1) − r_t, ζ̂ = (2h/G) ω.
        let image = |omega: &[Rat], r0: &[Rat], r1: &[Rat]| {
            add(&scale(&(&(&h * &two) / &g), omega), &sub(r1, r0))
        };
        let zeta = image(&p.rates[0], &r_before, &predecessor.solve_remainders()[0]);
        let zeta_after = image(&s.rates[0], &r_after, &successor.solve_remainders()[0]);
        let difference = sub(&zeta_after, &zeta);
        accumulated = add(&accumulated, &difference);
        if exact {
            // The right side is unchanged at held momentum; the deposit acts on the motion.
            let motion = scale(&(&g / &h), &zeta);
            assert_eq!(
                operator.apply(&difference).unwrap(),
                scale(&-Rat::one(), &delta.apply(&motion).unwrap()),
                "m'(ζ' − ζ) = −ΔC(w + w⁺) under the exact solve at held momentum"
            );
            eprintln!("storage tick={} w={rate:?} w'={:?} difference={difference:?} motion={motion:?}",
                tick + 1, s.states[0][1]);
            continue;
        }
        // On the lattice the solve reads the representatives alone: the 2026-10-02 response.
        let jump = sub(&scale(&two, rate), &scale(&(&g / &h), &zeta));
        material = add(&material, &inverse.apply(&delta.apply(&jump).unwrap()).unwrap());
        rate_images = add(&rate_images, &scale(&two, &sub(&s.rates[0], &p.rates[0])));
        let (pc, sc) = (predecessor.change().unwrap(), successor.change().unwrap());
        let equal = pc == sc;
        if equal {
            let remainders =
                sub(&successor.solve_remainders()[0], &predecessor.solve_remainders()[0]);
            assert_eq!(remainders, accumulated, "equal representatives carry the image difference");
            let rates = sub(&successor.state_remainders()[0][1], &predecessor.state_remainders()[0][1]);
            assert_eq!(rates, add(&opening_remainder, &rate_images),
                "the rate remainders carry the opening's held momentum and the rate images");
        }
        if tick < 4 || (tick + 1).is_power_of_two() || !equal {
            eprintln!("storage tick={} w={:?} accumulated={:?} material={:?} chart={:?} equal={} elapsed_ms={}",
                tick + 1, rate, accumulated, material, sub(&accumulated, &material), equal,
                started.elapsed().as_millis());
        }
        if !equal {
            parted = Some(tick + 1);
            break;
        }
    }
    eprintln!("storage response exact={exact} parted={parted:?} rate_excursion={:?} travel={:?}",
        sub(&rate0, &predecessor.change().unwrap().states[0][1]),
        sub(&predecessor.change().unwrap().states[0][0], &change.states[0][0]));
}

// [proved-derived] At an opening receiving map `R = 0` (`Constitution::initial`) the face is the
// tree's and every covector the comparison sends into the passage is `Rᵀ g = 0`: no adjoint solve
// moves, and the contact storage's pull `Σ 2 r̄ (w − ω)ᵀ` is zero, while the face's own covector
// `g` and the feature `f` that `R`'s step reads are not (Lean
// `HNN/ReceivingReach.{zero_map_reads_nothing, storage_covector_dual}`). The first comparison on
// an opening constitution can move `R` alone; `C` is reached from the second on.
#[test]
fn a_zero_receiving_map_returns_no_covector_to_the_contact() {
    let field = boundary().with_exact_word();
    let theta = resolved(&field);
    let ring = field.receivers()[0].ring;
    let map = theta.receiving_map(ring).unwrap();
    let zero = ExactRatMatrix::zero(map.rows(), map.columns()).unwrap();
    let theta = theta.with_ports(ring, None, None, Some(zero)).unwrap();
    let (current, source) = learning::moment(&field, 82, 9);
    let source = Arc::new(source);
    let mut charts = Charts::new();
    let phases = learning::phases(&field, &theta, &current);
    let mut word = Word::open_source(&field, &theta, &current, source, &mut charts).unwrap();
    word.run(phases.last_epoch() + 1).unwrap();
    let targets: Vec<_> = (0..phases.aperture()).map(|i| (i + 1) % field.alphabet()).collect();
    let (_, returned) = word.compare_contact_storage(0, 0, &targets).unwrap();
    let back = returned.pullback.present().unwrap();
    // The face's covector and the feature it pairs with are present: `R`'s step has its samples.
    assert!(back.reads.iter().any(|(f, _)| f.iter().any(|x| !x.is_zero())));
    assert!(back.reads.iter().any(|(_, g)| g.iter().any(|x| !x.is_zero())));
    // Nothing enters the passage: every adjoint solve and every opening covector is zero.
    assert!(back.transits.iter().flatten().all(|tick| tick.solved.iter().all(Rat::is_zero)));
    assert!(back.opening.iter().flatten().all(Rat::is_zero));
    // So the contact storage's pull is zero.
    let deposit = returned.deposit.present().unwrap();
    assert_eq!(deposit.factors().len(), 1);
    for step in deposit.factors() {
        let FactorGradient::Storage { gradient, .. } = &step.gradient else {
            panic!("the contact return composes contact storage alone");
        };
        assert!(gradient.entries().iter().all(Rat::is_zero));
    }
}
