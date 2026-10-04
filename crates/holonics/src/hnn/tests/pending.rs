//! One cut: a pending ratio is read from its anchor through its producing operands at the
//! contemporary constitution, on the opening its refine opened on. With intervening refines and no
//! deposit a delayed compare equals the immediate one exactly, and so it does across an ingest that extends the moment and steps the lift
//! point (the pending ratio holds its own copy of the moment and its anchor); after a deposit it
//! returns the residual against the emitted face.

use num_traits::Zero;

use super::learning::{chain, generic};
use super::support::Draw;
use crate::hnn::field::Current;
use crate::hnn::port::{ExecutionPort, ReceiptDetail};
use crate::hnn::reference::{Reference, one_hot};

/// A cut on the chain: a generic constitution, or the declared initial one (whose first deposit
/// keeps the constitution small).
fn cut(
    declared: bool,
) -> (
    Reference,
    crate::hnn::reference::Resident,
    crate::hnn::port::MomentId,
) {
    let field = chain();
    let reference = Reference::campaign_one();
    let mut resident = if declared {
        reference.mount(&field, &Current::at_rest(&field)).unwrap()
    } else {
        reference
            .mount_with(&field, &Current::at_rest(&field), generic(&field, 31))
            .unwrap()
    };
    let mut draw = Draw::new(32);
    let cells: Vec<usize> = (0..9).map(|_| draw.below(4)).collect();
    let (moment, _) = reference
        .ingest(&mut resident, None, &one_hot(&cells))
        .unwrap();
    (reference, resident, moment)
}

/// Lean `HNN/Retention.contemporary_read`: a pending ratio compared after intervening refines and
/// no deposit compares exactly as it did when taken at once (on the resident as it stood at its
/// refine), and has no residual. Under the carry the intervening refines run the chain's later
/// words (the reception carry §8); they move no constitution.
#[test]
fn a_delayed_compare_with_no_deposit_equals_the_immediate_one() {
    let (reference, mut resident, moment) = cut(false);
    let phases = resident.admitted()[0].clone();
    let (first, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let mut at_once = resident.clone();
    let (_, immediate) = reference
        .compare(&mut at_once, first, &one_hot(&[3, 1]))
        .unwrap();
    reference.refine(&mut resident, &moment, &phases).unwrap();
    reference.refine(&mut resident, &moment, &phases).unwrap();
    let (_, delayed) = reference
        .compare(&mut resident, first, &one_hot(&[3, 1]))
        .unwrap();
    assert_eq!(delayed.forward, immediate.forward);
    assert_eq!(delayed.pullback, immediate.pullback);
    assert_eq!(delayed.deposit, immediate.deposit);
    let ReceiptDetail::Compare { residual, .. } = &delayed.receipt.detail else {
        panic!("a compare's receipt");
    };
    assert!(residual.iter().flatten().all(Zero::is_zero));
}

/// Review §5, the case the moment copy exists for: refine, ingest five cells (the moment extends and
/// the lift point steps), then compare. It equals the compare of the same pending ratio taken before
/// the ingest (on the resident as it stood at the refine), exactly, with no residual.
#[test]
fn a_compare_across_an_ingest_equals_one_taken_before_it() {
    let (reference, mut resident, moment) = cut(false);
    // Close the aeon at the joint clock's next carry-out, so the last ring opens on its section and
    // five cells that step ring 0 at most once cannot carry it out again.
    while !resident.awaiting_boundary() {
        reference
            .ingest(&mut resident, Some(&moment), &one_hot(&[2]))
            .unwrap();
    }
    let admitted = resident.admitted().to_vec();
    reference.close_aeon(&mut resident, &admitted).unwrap();
    let phases = resident.admitted()[0].clone();
    let (pending, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let mut before = resident.clone();
    let (_, immediate) = reference
        .compare(&mut before, pending, &one_hot(&[3, 1]))
        .unwrap();
    let lift = resident.current().lift().to_vec();
    let cells = resident.moment(&moment).unwrap().cells();
    let (_, ingested) = reference
        .ingest(&mut resident, Some(&moment), &one_hot(&[1, 2, 1, 1, 2]))
        .unwrap();
    let ingested = ingested.forward.into_present().unwrap();
    assert_eq!((ingested.cells, ingested.carry_out), (5, false));
    assert_eq!(resident.moment(&moment).unwrap().cells(), cells + 5);
    assert_ne!(resident.current().lift(), lift.as_slice());
    let (_, delayed) = reference
        .compare(&mut resident, pending, &one_hot(&[3, 1]))
        .unwrap();
    assert_eq!(delayed.forward, immediate.forward);
    assert_eq!(delayed.pullback, immediate.pullback);
    assert_eq!(delayed.deposit, immediate.deposit);
    let ReceiptDetail::Compare { residual, .. } = &delayed.receipt.detail else {
        panic!("a compare's receipt");
    };
    assert!(residual.iter().flatten().all(Zero::is_zero));
}

/// After a deposit the delayed compare reads the contemporary constitution: its faces are its own
/// word read again at the successor, on the opening it opened on, with the successor's tree at the
/// targets' addresses (the landmark tree), and it returns the wave's residual against the face it
/// emitted.
#[test]
fn after_a_deposit_the_compare_returns_the_residual_against_the_emitted_face() {
    let (reference, mut resident, moment) = cut(true);
    let field = chain();
    let phases = resident.admitted()[0].clone();
    // The first word of the mount opens at rest; its ratio is produced at its refine's cut.
    assert!(resident.carried().is_none());
    let ratio = crate::hnn::PendingRatio::produce(
        resident.current(),
        resident.moment(&moment).unwrap(),
        resident.address(),
        &phases,
        resident.constitution().commit(),
    )
    .unwrap();
    let (first, emitted) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let emitted = emitted.forward.into_present().unwrap();
    let (second, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let (staged, _) = reference
        .compare(&mut resident, second, &one_hot(&[2, 0]))
        .unwrap();
    reference.deposit(&mut resident, staged).unwrap();
    let (_, contemporary) = ratio
        .read_on(
            &field,
            resident.constitution(),
            &mut crate::hnn::Charts::new(),
            &crate::hnn::WordOpening::Rest,
        )
        .unwrap();
    let (_, delayed) = reference
        .compare(&mut resident, first, &one_hot(&[2, 0]))
        .unwrap();
    let ratio = delayed.forward.present().unwrap();
    let address = resident.address().truncated(phases.depth()).unwrap();
    let trees = phases
        .tree_faces(resident.constitution(), &address, &[2, 0])
        .unwrap();
    assert_eq!(
        ratio.faces(),
        &phases.combine(&contemporary, &trees).unwrap()
    );
    let ReceiptDetail::Compare { residual, .. } = &delayed.receipt.detail else {
        panic!("a compare's receipt");
    };
    let expected: Vec<Vec<_>> = contemporary
        .logits
        .iter()
        .zip(&emitted.logits)
        .map(|(now, then)| now.iter().zip(then).map(|(a, b)| a - b).collect())
        .collect();
    assert_eq!(residual, &expected);
    assert!(residual.iter().flatten().any(|x| !x.is_zero()));
}
