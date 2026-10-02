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
        assert_eq!(next.change().unwrap(), change);
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
        assert_eq!(next.recorded()[0].states, change.states);
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
