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
use crate::hnn::reference::Reference;
use crate::hnn::tests::support::encoded;

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
        .ingest(&mut resident, None, &encoded(&field, &cells))
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
        .compare(&mut at_once, first, &encoded(&chain(), &[3, 1]))
        .unwrap();
    reference.refine(&mut resident, &moment, &phases).unwrap();
    reference.refine(&mut resident, &moment, &phases).unwrap();
    let (_, delayed) = reference
        .compare(&mut resident, first, &encoded(&chain(), &[3, 1]))
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
            .ingest(&mut resident, Some(&moment), &encoded(&chain(), &[2]))
            .unwrap();
    }
    let admitted = resident.admitted().to_vec();
    reference.close_aeon(&mut resident, &admitted).unwrap();
    let phases = resident.admitted()[0].clone();
    let (pending, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let mut before = resident.clone();
    let (_, immediate) = reference
        .compare(&mut before, pending, &encoded(&chain(), &[3, 1]))
        .unwrap();
    let lift = resident.current().lift().to_vec();
    let cells = resident.moment(&moment).unwrap().cells();
    let (_, ingested) = reference
        .ingest(
            &mut resident,
            Some(&moment),
            &encoded(&chain(), &[1, 2, 1, 1, 2]),
        )
        .unwrap();
    let ingested = ingested.forward.into_present().unwrap();
    assert_eq!((ingested.cells, ingested.carry_out), (5, false));
    assert_eq!(resident.moment(&moment).unwrap().cells(), cells + 5);
    assert_ne!(resident.current().lift(), lift.as_slice());
    let (_, delayed) = reference
        .compare(&mut resident, pending, &encoded(&chain(), &[3, 1]))
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
        .compare(&mut resident, second, &encoded(&chain(), &[2, 0]))
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
        .compare(&mut resident, first, &encoded(&chain(), &[2, 0]))
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

#[test]
fn observation_context_is_phase_specific_real_grain_metadata() {
    use crate::hnn::pending::PendingRatio;
    use crate::hnn::ratio::Faces;
    use crate::hnn::receiving::{ObservationPartition, ReceivingRead};
    use crate::hnn::ring::modes::ModeView;
    use crate::ratio::integer;
    let field = chain()
        .with_receiving_context(2, ObservationPartition::MaximumRealGrainSet)
        .unwrap();
    let reference = Reference::campaign_one();
    let mut resident = reference.mount(&field, &Current::at_rest(&field)).unwrap();
    let (moment, _) = reference
        .ingest(&mut resident, None, &encoded(&field, &[0, 1, 2]))
        .unwrap();
    let phases = resident.admitted()[0].clone();
    let original = PendingRatio::produce(
        resident.current(),
        resident.moment(&moment).unwrap(),
        resident.address(),
        &phases,
        resident.constitution().commit(),
    )
    .unwrap();
    let logits = [vec![0, 0, 1, 0, 1, 0, -1, 0], vec![2, 0, 0, 0, 0, 0, 0, 0]];
    let reads = logits
        .iter()
        .map(|row| {
            ReceivingRead::of_logits(row.iter().map(|&x| integer(x)).collect(), phases.grain())
        })
        .collect::<Vec<_>>();
    let wave = Faces::of_reads(&reads, phases.grain()).unwrap();
    let mut bound = original.clone();
    bound.admit_observed_read(&field, &[], &wave).unwrap();
    assert_eq!(
        bound.observation_bits().unwrap(),
        &[
            vec![false, true, true, false],
            vec![true, false, false, false]
        ]
    );
    assert_eq!(
        bound.bits() - original.bits(),
        (field.alphabet() * phases.aperture()) as u64
    );
    assert!(bound.admit_observed_read(&field, &[], &wave).is_err());
    assert!(bound.clone().with_view(&field, &ModeView::whole()).is_err());
    // Imaginary turns are retained in the Face but intentionally outside this declared partition.
    let changed_reads = reads
        .iter()
        .map(|read| {
            let mut logits = read.logits.clone();
            for x in logits.iter_mut().skip(1).step_by(2) {
                *x += integer(7);
            }
            ReceivingRead::of_logits(logits, phases.grain())
        })
        .collect::<Vec<_>>();
    let mut same_outcome = original.clone();
    same_outcome
        .admit_observed_read(
            &field,
            &[],
            &Faces::of_reads(&changed_reads, phases.grain()).unwrap(),
        )
        .unwrap();
    assert_eq!(bound.observation_bits(), same_outcome.observation_bits());
    assert_eq!(resident.current(), &original.current(&field).unwrap());
    let mut saved = String::new();
    bound.write_saved(&mut saved);
    let mut lines = saved.lines();
    let mut next = |what| {
        lines
            .next()
            .ok_or(crate::hnn::HnnError::ContinuingState { what })
    };
    let restored = PendingRatio::read_saved(&field, resident.address(), &mut next).unwrap();
    assert_eq!(restored, bound);
    assert!(lines.next().is_none());
    let wrong_grain = Faces::of_reads(&reads, phases.grain() + 1).unwrap();
    assert!(
        original
            .clone()
            .admit_observed_read(&field, &[], &wrong_grain)
            .is_err()
    );
}

#[test]
fn observation_context_flows_through_compare_deposit_and_cold_continuation() {
    use super::learning::OPEN_BUDGET;
    use crate::hnn::Constitution;
    use crate::hnn::constitution::ContinuingState;
    use crate::hnn::receiving::ObservationPartition;
    let field = chain()
        .with_receiving_context(2, ObservationPartition::MaximumRealGrainSet)
        .unwrap();
    let reference = Reference::new(64, OPEN_BUDGET);
    let opening = Constitution::initial(&field, OPEN_BUDGET).unwrap();
    let mut resident = reference
        .mount_with(&field, &Current::at_rest(&field), opening.clone())
        .unwrap();
    let (moment, _) = reference
        .ingest(&mut resident, None, &encoded(&field, &[0, 1, 2]))
        .unwrap();
    let phases = resident.admitted()[0].clone();
    let causal = resident.address().clone();
    let (pending, refined) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let expected = refined
        .forward
        .present()
        .unwrap()
        .faces
        .iter()
        .map(|face| {
            let mut bits = vec![false; field.alphabet()];
            for class in face.maximal_mass_classes() {
                bits[class] = true;
            }
            bits
        })
        .collect::<Vec<_>>();
    let mut other_target = resident.clone();
    let (staged, compared) = reference
        .compare(&mut resident, pending, &encoded(&field, &[2, 0]))
        .unwrap();
    let (_, other) = reference
        .compare(&mut other_target, pending, &encoded(&field, &[1, 3]))
        .unwrap();
    assert_eq!(
        compared.deposit.present().unwrap().landmark_observations(),
        Some(expected.as_slice())
    );
    assert_eq!(
        other.deposit.present().unwrap().landmark_observations(),
        Some(expected.as_slice())
    );
    assert_eq!(resident.address(), &causal);
    reference.deposit(&mut resident, staged).unwrap();
    // Re-forming the partition from the identical attained wave does not read the tree's
    // newly learned target counts. The tree can only affect the later combined face.
    let mut same_wave_context = crate::hnn::PendingRatio::produce(
        resident.current(),
        resident.moment(&moment).unwrap(),
        resident.address(),
        &phases,
        resident.constitution().commit(),
    )
    .unwrap();
    same_wave_context
        .admit_observed_read(&field, &[], refined.forward.present().unwrap())
        .unwrap();
    assert_eq!(
        same_wave_context.observation_bits(),
        Some(expected.as_slice())
    );
    // Arrived retains the original observation after material changes; saved passage carries it.
    let state = resident.continuing_state(field.sources()[0]).unwrap();
    let state = ContinuingState::from_text(&state.to_text()).unwrap();
    let passage = state.resident_passage(&field, &opening).unwrap().unwrap();
    assert_eq!(
        passage
            .parts()
            .arrived
            .as_ref()
            .unwrap()
            .ratio
            .observation_bits(),
        Some(expected.as_slice())
    );
    let mut invalid = passage.clone().into_parts();
    let arrived = invalid.arrived.as_mut().unwrap();
    let old = &arrived.ratio;
    arrived.ratio = crate::hnn::PendingRatio::produce(
        &old.current(&field).unwrap(),
        old.moment(),
        old.address(),
        old.phases(),
        old.commit(),
    )
    .unwrap();
    assert!(
        crate::hnn::reference::passage::ResidentPassage::new(
            &field,
            resident.constitution(),
            invalid
        )
        .is_err()
    );
    let invalid_text = passage
        .to_text()
        .lines()
        .filter(|line| !line.starts_with("observation-bits "))
        .map(|line| {
            if line.starts_with("ratio-observation ") {
                "ratio-observation 0"
            } else {
                line
            }
        })
        .collect::<Vec<_>>()
        .join("\n");
    assert!(
        crate::hnn::reference::passage::ResidentPassage::from_text(
            &field,
            resident.constitution(),
            &invalid_text
        )
        .is_err()
    );
    let mut restored = reference
        .mount_continued(&field, &Current::at_rest(&field), opening, &state)
        .unwrap();
    assert_eq!(restored.constitution(), resident.constitution());
    assert_eq!(restored.address(), resident.address());
    let (a, ar) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let (b, br) = reference.refine(&mut restored, &moment, &phases).unwrap();
    assert_eq!(ar.forward, br.forward);
    let (_, ac) = reference
        .compare(&mut resident, a, &encoded(&field, &[3, 1]))
        .unwrap();
    let (_, bc) = reference
        .compare(&mut restored, b, &encoded(&field, &[3, 1]))
        .unwrap();
    assert_eq!(ac.forward, bc.forward);
    assert_eq!(ac.deposit, bc.deposit);
}

/// [L3] **The receiving section flows through refine, compare, deposit and cold
/// continuation.** At the opening the receiving map moves no logit, so every source's maximum set
/// is the whole alphabet, while the section of the receiver's carrier (its operand before `R`)
/// already parts the sources. The reference's refine binds each phase's `3 σ(n)` section letters,
/// equal to the section read independently from the word's receiving anchors; the compare carries
/// them label-free into the deposit with their partition; the deposit refines the receiving tree,
/// which keeps its refining role; and a saved continuation restores the constitution and reads
/// and compares as the resident does.
#[test]
fn section_observation_flows_through_compare_deposit_and_cold_continuation() {
    use super::learning::OPEN_BUDGET;
    use crate::compression::landmark::context::{ObservationLetter, ObservationRole};
    use crate::hnn::Constitution;
    use crate::hnn::chart::Charts;
    use crate::hnn::constitution::ContinuingState;
    use crate::hnn::field::ConstitutionRead;
    use crate::hnn::pending::PendingRatio;
    use crate::hnn::receiving::{ObservationPartition, section_bits};
    use crate::hnn::word::WordOpening;
    let partition = ObservationPartition::ReceivingSection;
    let field = chain().with_receiving_context(2, partition).unwrap();
    let width = partition.outcome_bits(&field, 2);
    assert_eq!(width, 9);
    let reference = Reference::new(64, OPEN_BUDGET);
    let opening = Constitution::initial(&field, OPEN_BUDGET).unwrap();
    let tree = opening.landmarks(2).unwrap();
    assert_eq!(tree.observation_role(), ObservationRole::Refine);
    assert_eq!(tree.observation_width(), width);
    let mut sections = std::collections::BTreeSet::new();
    for cells in [[0, 1, 2], [3, 1, 0], [2, 2, 1], [1, 3, 3]] {
        let mut resident = reference
            .mount_with(&field, &Current::at_rest(&field), opening.clone())
            .unwrap();
        let (moment, _) = reference
            .ingest(&mut resident, None, &encoded(&field, &cells))
            .unwrap();
        let phases = resident.admitted()[0].clone();
        let mut independent = PendingRatio::produce(
            resident.current(),
            resident.moment(&moment).unwrap(),
            resident.address(),
            &phases,
            resident.constitution().commit(),
        )
        .unwrap();
        let (word, faces) = independent
            .read_on(
                &field,
                resident.constitution(),
                &mut Charts::new(),
                &WordOpening::Rest,
            )
            .unwrap();
        let anchors = word.receiving_anchors(&phases).unwrap();
        let expected: Vec<Vec<bool>> = anchors
            .iter()
            .map(|anchor| section_bits(&field, 2, anchor).unwrap())
            .collect();
        assert_eq!(expected.len(), phases.aperture());
        assert!(expected.iter().all(|path| path.len() == width));
        let tie = ObservationPartition::MaximumRealGrainSet
            .read(&field, &phases, &[], &faces)
            .unwrap();
        assert!(tie.iter().flatten().all(|&member| member));
        independent
            .admit_observed_read(&field, &anchors, &faces)
            .unwrap();
        assert_eq!(independent.observation_bits(), Some(expected.as_slice()));
        assert!(
            independent
                .clone()
                .admit_observed_read(&field, &anchors, &faces)
                .is_err()
        );
        sections.insert(expected.clone());

        let causal = resident.address().clone();
        let (pending, refined) = reference.refine(&mut resident, &moment, &phases).unwrap();
        assert_eq!(refined.forward.present().unwrap(), &faces);
        let mut other_target = resident.clone();
        let (staged, compared) = reference
            .compare(&mut resident, pending, &encoded(&field, &[2, 0]))
            .unwrap();
        let (_, other) = reference
            .compare(&mut other_target, pending, &encoded(&field, &[1, 3]))
            .unwrap();
        let deposit = compared.deposit.present().unwrap();
        assert_eq!(deposit.landmark_partition(), Some(partition));
        assert_eq!(deposit.landmark_observations(), Some(expected.as_slice()));
        assert_eq!(
            other.deposit.present().unwrap().landmark_observations(),
            Some(expected.as_slice())
        );
        let observed = deposit.observed_landmarks().unwrap().unwrap();
        assert!(observed.iter().all(|address| {
            address.observation().len() == width
                && address
                    .observation()
                    .letters()
                    .iter()
                    .all(|letter| matches!(letter, ObservationLetter::Section(_)))
        }));
        assert_eq!(resident.address(), &causal);
        reference.deposit(&mut resident, staged).unwrap();
        let learned = resident.constitution().landmarks(2).unwrap();
        assert_eq!(learned.observation_role(), ObservationRole::Refine);
        assert_ne!(learned.standing(), opening.landmarks(2).unwrap().standing());

        let state = resident.continuing_state(field.sources()[0]).unwrap();
        let state = ContinuingState::from_text(&state.to_text()).unwrap();
        let mut restored = reference
            .mount_continued(&field, &Current::at_rest(&field), opening.clone(), &state)
            .unwrap();
        assert_eq!(restored.constitution(), resident.constitution());
        assert_eq!(restored.address(), resident.address());
        let (a, ar) = reference.refine(&mut resident, &moment, &phases).unwrap();
        let (b, br) = reference.refine(&mut restored, &moment, &phases).unwrap();
        assert_eq!(ar.forward, br.forward);
        let (_, ac) = reference
            .compare(&mut resident, a, &encoded(&field, &[3, 1]))
            .unwrap();
        let (_, bc) = reference
            .compare(&mut restored, b, &encoded(&field, &[3, 1]))
            .unwrap();
        assert_eq!(ac.forward, bc.forward);
        assert_eq!(ac.deposit, bc.deposit);
    }
    assert!(sections.len() > 1);
}
