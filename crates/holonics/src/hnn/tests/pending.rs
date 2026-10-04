//! One cut: a pending ratio is read from its anchor through its producing operands at the
//! contemporary constitution. With intervening refines and no deposit a delayed compare equals the
//! immediate one exactly, and so it does across an ingest that extends the moment and steps the lift
//! point (the pending ratio holds its own copy of the moment and its anchor); after a deposit it
//! returns the residual against the emitted face.
//!
//! Several pending ratios at one cut exist only at the `A = I` limit, where each word opens at rest:
//! under the default reception (the carry, the reception carry §8) the field's one motion is in one
//! word at a time (one chain, §2.6). The tests of concurrent pending ratios declare that limit; the
//! compare across an ingest needs only one, and runs under the default.

use num_traits::Zero;

use super::learning::{chain, generic};
use super::support::Draw;
use crate::hnn::field::Current;
use crate::hnn::port::{ExecutionPort, ReceiptDetail};
use crate::hnn::reference::{Reception, Reference, one_hot};

/// A cut on the chain: a generic constitution, or the declared initial one (whose first deposit
/// keeps the constitution small), under the default reception or at its rest limit.
fn cut(
    declared: bool,
    rest: bool,
) -> (
    Reference,
    crate::hnn::reference::Resident,
    crate::hnn::port::MomentId,
) {
    let field = chain();
    let reference = if rest {
        Reference::campaign_one().with_reception(Reception::Rest)
    } else {
        Reference::campaign_one()
    };
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

/// Lean `HNN/Retention.contemporary_read`: two pending ratios produced at one cut, with an
/// intervening refine and no deposit, compare identically, and neither has a residual.
#[test]
fn a_delayed_compare_with_no_deposit_equals_the_immediate_one() {
    let (reference, mut resident, moment) = cut(false, true);
    let phases = resident.admitted()[0].clone();
    let (first, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let (second, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let (_, immediate) = reference
        .compare(&mut resident, second, &one_hot(&[3, 1]))
        .unwrap();
    let (_, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
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
    let (reference, mut resident, moment) = cut(false, false);
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

/// After a deposit the delayed compare reads the contemporary constitution: its faces are a fresh
/// refine's wave at the successor with the successor's tree at the targets' addresses (the
/// landmark tree), and it returns the wave's residual against the face it emitted.
#[test]
fn after_a_deposit_the_compare_returns_the_residual_against_the_emitted_face() {
    let (reference, mut resident, moment) = cut(true, true);
    let phases = resident.admitted()[0].clone();
    let (first, emitted) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let emitted = emitted.forward.into_present().unwrap();
    let (second, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let (staged, _) = reference
        .compare(&mut resident, second, &one_hot(&[2, 0]))
        .unwrap();
    reference.deposit(&mut resident, staged).unwrap();
    let (fresh, contemporary) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let contemporary = contemporary.forward.into_present().unwrap();
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
    reference
        .discard(&mut resident, crate::hnn::port::Handle::Pending(fresh))
        .unwrap();
}
