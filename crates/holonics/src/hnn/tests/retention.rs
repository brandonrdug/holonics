//! The collapse onto what the admitted future distinguishes: the time-indexed diamond on the
//! six-ring path of the retired [`release.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/release.py) (72 of 156
//! entries released at `A = 2`, 132 at `A = 1`), every
//! admitted reading unchanged with the released items replaced by arbitrary values, each retained
//! item tight, `deposit_descends`, whole-locus deletion, the pending ratios reached, and the
//! boundary's refusals.

use std::collections::BTreeSet;

use num_traits::{Signed, Zero};

use super::learning::{generic, moment, path_with, phases, six_path};
use super::support::Draw;
use crate::hnn::HnnError;
use crate::hnn::constitution::{
    Constitution, DepositReading, FactorGradient, FactorStep, Family, Locus, Reach,
};
use crate::hnn::field::{ConstitutionRead, Current, Field, ReceiverDeclaration};
use crate::hnn::pending::PendingRatio;
use crate::hnn::port::{Deposit, ExecutionPort, Handle};
use crate::hnn::propagation::Operands;
use crate::hnn::ratio::{HolonRatio, target_phases};
use crate::hnn::receiving::{ActiveAddress, ReceivingPhases};
use crate::hnn::reference::{Reception, Reference, compose, one_hot};
use crate::hnn::retention::{Diamond, Opens, collapse, loci, retained, retained_on_motion};
use crate::hnn::word::Word;
use crate::ratio::{Rat, integer, rat};

/// The anchors `v_R(e_j)` a word reads from an injection on ring 0's storage, at the admitted
/// receiver's phases: one chart of the operands at rest serves every injection, and the injections
/// are read lazily, so a caller that stops at the first difference reads no further.
fn readings<'a>(
    field: &'a Field,
    theta: &Constitution,
    phases: &'a ReceivingPhases,
    injections: &'a [Vec<Rat>],
) -> impl Iterator<Item = Vec<Vec<Rat>>> + 'a {
    let operands = Operands::at_cut(field, theta, &Current::at_rest(field)).unwrap();
    injections.iter().map(move |injection| {
        let mut storage: Vec<Vec<Rat>> = field
            .rings()
            .iter()
            .map(|ring| vec![Rat::from_integer(0.into()); ring.width()])
            .collect();
        storage[0] = injection.clone();
        let mut word = Word::on_operands(field, operands.clone(), storage).unwrap();
        word.forward(phases).unwrap()
    })
}

/// **The unit injections of ring 0's storage** (width 4). [agent-inferred] At fixed operands the word
/// is linear in its opening change (`HNN/Word.fieldTick`, the module header of `hnn::retention`), so
/// its readings on these four decide its readings on every injection: two words read alike on every
/// injection exactly when they read alike on these, and differ on some injection exactly when they
/// differ on one of these.
fn injections() -> Vec<Vec<Rat>> {
    (0..4)
        .map(|i| {
            (0..4)
                .map(|j| if i == j { integer(1) } else { integer(0) })
                .collect()
        })
        .collect()
}

/// Lean `HNN/Retention.diamond_recursion`: the two recursions retain the elements and junctions of
/// rings 0–2 and the channels (0,1), (1,2), (2,3), releasing 72 of 156 constitution entries at
/// `A = 2`; at the rim `A = 1` every element is released, channel (2,3) is released while its
/// conductance is kept, and 132 of 156 are released.
#[test]
fn the_recursions_release_seventy_two_of_one_fifty_six_on_the_six_ring_path() {
    for (aperture, elements, channels, conductances, released) in [
        (2, vec![0, 1, 2], vec![0, 1, 2], vec![0, 1, 2], 72),
        (1, vec![], vec![0, 1], vec![0, 1, 2], 132),
    ] {
        let field = six_path(aperture);
        let theta = generic(&field, 41);
        let current = Current::at_rest(&field);
        let admitted = [phases(&field, &theta, &current)];
        let diamond = Diamond::of(&field, &admitted[0]);
        assert_eq!(diamond.last_epoch(), aperture + 1);
        let kept = retained(&field, &admitted, Opens::AtRest);
        let of = |make: fn(usize) -> Locus, count: usize| -> Vec<usize> {
            (0..count).filter(|i| kept.contains(&make(*i))).collect()
        };
        assert_eq!(of(Locus::Element, 6), elements);
        assert_eq!(of(Locus::Junction, 6), vec![0, 1, 2]);
        assert_eq!(of(Locus::Channel, 5), channels);
        assert_eq!(of(Locus::Conductance, 5), conductances);
        let mut collapsed = theta.clone();
        let reading = collapse(&field, &mut collapsed, &admitted, Opens::AtRest).unwrap();
        assert_eq!(
            (reading.released_entries, reading.total_entries),
            (released, 156)
        );
    }
}

/// The reception carry §8, the diamond under the carry. A word opened on a carried change moves
/// from tick 0 wherever that change is: with the carried interior on ring 3 of the six-ring path
/// (source ring 0, receiver ring 2, `e_last = 3`), ring 3's element is read from tick 0, where the
/// rest diamond never reads it. The admitted future under the carry at `A = 0` keeps opening on
/// the continuing motion, which reaches every ring connected to a source and returns to the
/// receiver over the chain's clock, so the collapse releases none of the 156 entries the rest limit
/// releases 72 of.
#[test]
fn under_the_carry_the_diamond_opens_on_the_motion_and_the_collapse_keeps_every_connected_locus() {
    let field = six_path(2);
    let theta = generic(&field, 41);
    let current = Current::at_rest(&field);
    let admitted = [phases(&field, &theta, &current)];
    let rest = Diamond::of(&field, &admitted[0]);
    let opened = Diamond::opened(&field, &admitted[0], &[3]);
    assert_eq!(opened.last_epoch(), rest.last_epoch());
    assert!(!rest.element(3) && opened.element(3));
    assert!(!rest.element_window(3, 0) && opened.element_window(3, 0));
    assert!(!opened.element(5));
    // At rest the support is empty and the opened diamond is the rest one.
    assert_eq!(Diamond::opened(&field, &admitted[0], &[]), rest);
    let kept = retained(&field, &admitted, Opens::OnMotion);
    for g in 0..6 {
        assert!(kept.contains(&Locus::Element(g)) && kept.contains(&Locus::Junction(g)));
    }
    for a in 0..5 {
        assert!(kept.contains(&Locus::Channel(a)) && kept.contains(&Locus::Conductance(a)));
    }
    let mut collapsed = theta.clone();
    let reading = collapse(&field, &mut collapsed, &admitted, Opens::OnMotion).unwrap();
    assert_eq!((reading.released_entries, reading.total_entries), (0, 156));
    assert_eq!(collapsed, theta);
}

/// Lean `HNN/Retention.release_indistinguishable`: with every released item (elements, channels,
/// junction admittances and conductances) replaced by arbitrary values, and after the collapse
/// itself, every admitted reading is identical, exactly, on every injection (the four unit
/// injections decide them, [`injections`]).
#[test]
fn every_admitted_reading_is_identical_with_every_released_item_replaced() {
    for aperture in [2, 1] {
        let field = six_path(aperture);
        let theta = generic(&field, 43);
        let current = Current::at_rest(&field);
        let admitted = [phases(&field, &theta, &current)];
        let kept = retained(&field, &admitted, Opens::AtRest);
        let mut draw = Draw::new(44);
        let mut junctions = vec![integer(2); 6];
        for (g, junction) in junctions.iter_mut().enumerate() {
            if !kept.contains(&Locus::Junction(g)) {
                *junction = draw.rational().abs() + integer(1);
            }
        }
        let mut conductances = vec![integer(2); 5];
        for (a, conductance) in conductances.iter_mut().enumerate() {
            if !kept.contains(&Locus::Conductance(a)) {
                *conductance = draw.rational().abs() + integer(1);
            }
        }
        let replaced_field = path_with(aperture, &junctions, &conductances);
        let mut replaced = theta.clone();
        for g in 0..6 {
            if !kept.contains(&Locus::Element(g)) {
                replaced = replaced
                    .with_element(
                        g,
                        draw.matrix(4, 4),
                        draw.matrix(4, 4),
                        (0..4).map(|_| (draw.vector(4), draw.vector(4))).collect(),
                    )
                    .unwrap();
            }
        }
        for a in 0..5 {
            if !kept.contains(&Locus::Channel(a)) {
                replaced = replaced
                    .with_channel(a, draw.matrix(2, 2), draw.matrix(2, 2), draw.matrix(2, 2))
                    .unwrap();
            }
        }
        let mut collapsed = theta.clone();
        collapse(&field, &mut collapsed, &admitted, Opens::AtRest).unwrap();
        let injected = injections();
        let read = |field: &Field, theta: &Constitution| -> Vec<Vec<Vec<Rat>>> {
            readings(field, theta, &admitted[0], &injected).collect()
        };
        let base = read(&field, &theta);
        assert_eq!(read(&replaced_field, &replaced), base);
        assert_eq!(read(&field, &collapsed), base);
    }
}

/// The rule is tight: replacing any one retained item alone changes some reading (12 of 12 at
/// `A = 2`, 8 of 8 at `A = 1`, as in the retired [`release.py`](https://github.com/brandonrdug/holonics/blob/d4596102/research/notebook/hnn_design/release.py)),
/// read on the four unit injections that decide
/// every injection ([`injections`]).
#[test]
fn replacing_any_one_retained_item_changes_some_reading() {
    for (aperture, items) in [(2, 12), (1, 8)] {
        let field = six_path(aperture);
        let theta = generic(&field, 47);
        let current = Current::at_rest(&field);
        let admitted = [phases(&field, &theta, &current)];
        let kept: Vec<Locus> = retained(&field, &admitted, Opens::AtRest)
            .into_iter()
            .filter(|locus| {
                matches!(
                    locus,
                    Locus::Element(_)
                        | Locus::Junction(_)
                        | Locus::Channel(_)
                        | Locus::Conductance(_)
                )
            })
            .collect();
        assert_eq!(kept.len(), items);
        let injected = injections();
        let base: Vec<Vec<Vec<Rat>>> = readings(&field, &theta, &admitted[0], &injected).collect();
        let mut draw = Draw::new(49);
        for locus in kept {
            let (changed_field, changed) = match locus {
                Locus::Element(g) => (
                    field.clone(),
                    theta
                        .clone()
                        .with_element(
                            g,
                            draw.matrix(4, 4),
                            draw.matrix(4, 4),
                            (0..4).map(|_| (draw.vector(4), draw.vector(4))).collect(),
                        )
                        .unwrap(),
                ),
                Locus::Channel(a) => (
                    field.clone(),
                    theta
                        .clone()
                        .with_channel(a, draw.matrix(2, 2), draw.matrix(2, 2), draw.matrix(2, 2))
                        .unwrap(),
                ),
                Locus::Junction(g) => {
                    let mut junctions = vec![integer(2); 6];
                    junctions[g] = integer(7);
                    (
                        path_with(aperture, &junctions, &vec![integer(2); 5]),
                        theta.clone(),
                    )
                }
                Locus::Conductance(a) => {
                    let mut conductances = vec![integer(2); 5];
                    conductances[a] = integer(7);
                    (
                        path_with(aperture, &vec![integer(2); 6], &conductances),
                        theta.clone(),
                    )
                }
                _ => unreachable!(),
            };
            // Some unit injection's reading sees it: the first that does is its witness.
            assert!(
                readings(&changed_field, &changed, &admitted[0], &injected)
                    .zip(&base)
                    .any(|(reading, unchanged)| reading != *unchanged),
                "{locus:?} is retained, so some reading sees it"
            );
        }
    }
}

/// A compare's deposit on a constitution, computed exactly as the reference composes it.
fn deposited(field: &Field, theta: &Constitution, pending: &PendingRatio) -> Constitution {
    deposit_read(field, theta, pending).0
}

/// [`deposited`] with the deposit's reading.
fn deposit_read(
    field: &Field,
    theta: &Constitution,
    pending: &PendingRatio,
) -> (Constitution, DepositReading) {
    deposit_try(field, theta, pending).unwrap()
}

/// [`deposit_read`], refusals returned.
fn deposit_try(
    field: &Field,
    theta: &Constitution,
    pending: &PendingRatio,
) -> Result<(Constitution, DepositReading), HnnError> {
    theta.deposited(&compose_deposit(field, theta, pending))
}

/// A compare's deposit, composed exactly as the reference composes it.
fn compose_deposit(field: &Field, theta: &Constitution, pending: &PendingRatio) -> Deposit {
    let (word, faces) = pending.read(field, theta).unwrap();
    let targets = [1usize, 0];
    let anchors = target_phases(field, pending.anchor(), 2, &targets).unwrap();
    let ratio = HolonRatio::compare(faces, &targets, &anchors).unwrap();
    let back = word
        .pull_back(
            &ratio.covector().unwrap(),
            theta.receiving_map(2).unwrap(),
            &pending.anchor()[2],
            pending.phases(),
        )
        .unwrap();
    let (_, deposit) = compose(
        field,
        theta,
        pending,
        &crate::hnn::WordOpening::Rest,
        &back,
        &targets,
        &[],
    )
    .unwrap();
    deposit
}

/// Lean `HNN/LatticeDeposit.lattice_deposit_descends` (`HNN/Retention.deposit_descends` at the
/// budgeted carry): on the six-ring path, where the collapse releases 72 entries, and from a
/// constitution already carrying remainders and advanced clocks, the collapse commutes with a
/// deposit exactly: values, remainders and clocks.
#[test]
fn deposit_descends() {
    let field = six_path(2);
    let (current, open) = moment(&field, 52, 11);
    let phases = phases(&field, &generic(&field, 51), &current);
    let admitted = [phases.clone()];
    let pending = PendingRatio::produce(
        &current,
        &open,
        &ActiveAddress::boundary(phases.depth()),
        &phases,
        0,
    )
    .unwrap();
    let theta = deposited(&field, &generic(&field, 51), &pending);
    assert!(!theta.carried_remainders().is_empty());
    let pending = PendingRatio::produce(
        &current,
        &open,
        &ActiveAddress::boundary(phases.depth()),
        &phases,
        1,
    )
    .unwrap();
    let mut first = deposited(&field, &theta, &pending);
    collapse(&field, &mut first, &admitted, Opens::AtRest).unwrap();
    let mut collapsed = theta.clone();
    collapse(&field, &mut collapsed, &admitted, Opens::AtRest).unwrap();
    let second = deposited(&field, &collapsed, &pending);
    assert_eq!(first, second);
    assert_ne!(first, theta);
    assert_eq!(first.clock(Locus::Element(1)), 2);
}

/// The aeon collapse releases no carried remainder of a retained locus and resets no deposit
/// clock: after two deposits on the six-ring path, every retained locus keeps its remainders and
/// its clock exactly; a released locus leaves whole (no remainder, no clock, no bits), its
/// remainders reported, and the constitution's bits drop by exactly the released loci's.
#[test]
fn the_collapse_keeps_the_retained_remainders_and_clocks() {
    let field = six_path(2);
    let (current, open) = moment(&field, 56, 11);
    // The committed energy bound refuses storage grown where none was stored (a singular `C = c cᵀ`
    // has no certified growth into its kernel), so the channels store on every direction.
    let mut theta = generic(&field, 55);
    for a in 0..field.contacts().len() {
        let k = field.contact(a).width();
        let dissipation = theta.contact_dissipation(a).clone();
        let identity = crate::ratio::linear::ExactRatMatrix::identity(k).unwrap();
        theta = theta
            .with_channel(
                a,
                identity.clone(),
                identity.scaled(&crate::ratio::rat(1, 2)),
                dissipation,
            )
            .unwrap();
    }
    let phases = phases(&field, &theta, &current);
    let pending = PendingRatio::produce(
        &current,
        &open,
        &ActiveAddress::boundary(phases.depth()),
        &phases,
        0,
    )
    .unwrap();
    let once = deposited(&field, &theta, &pending);
    let pending = PendingRatio::produce(
        &current,
        &open,
        &ActiveAddress::boundary(phases.depth()),
        &phases,
        1,
    )
    .unwrap();
    let carried = deposited(&field, &once, &pending);
    let before = carried.carried_remainders();
    assert!(!before.is_empty());
    let mut collapsed = carried.clone();
    let reading = collapse(
        &field,
        &mut collapsed,
        std::slice::from_ref(&phases),
        Opens::AtRest,
    )
    .unwrap();
    assert!(!reading.released.is_empty());
    let kept: Vec<_> = before
        .iter()
        .filter(|(locus, ..)| !reading.released.contains(locus))
        .cloned()
        .collect();
    assert!(!kept.is_empty());
    assert_eq!(collapsed.carried_remainders(), kept);
    // A released locus received no covector in this family's deposits, so it carried nothing.
    assert!(reading.released_remainders.is_empty());
    // A narrower family (aperture 1) releases loci the deposits reached: their remainders leave
    // with them, each reported exactly (the lattice deposit: "leaves whole, with its remainder, reported").
    let narrow = ReceivingPhases::declare(
        &field,
        &carried,
        &current,
        &ReceiverDeclaration {
            ring: phases.ring(),
            aperture: 1,
            tolerance: crate::ratio::rat(1, 16),
            depth: 2,
            prior: crate::compression::landmark::context::StopPrior::half(),
            mass: 1,
            base: crate::compression::landmark::context::BaseMeasure::Even,
            receiving_prior: 0,
        },
    )
    .unwrap();
    let mut shrunk = carried.clone();
    let narrowed = collapse(&field, &mut shrunk, &[narrow], Opens::AtRest).unwrap();
    let left: Vec<_> = before
        .iter()
        .filter(|(locus, ..)| narrowed.released.contains(locus))
        .cloned()
        .collect();
    assert!(!left.is_empty());
    assert_eq!(narrowed.released_remainders, left);
    for locus in loci(&field) {
        if reading.released.contains(&locus) {
            assert_eq!(collapsed.clock(locus), 0, "{locus:?}");
        } else {
            assert_eq!(collapsed.clock(locus), carried.clock(locus), "{locus:?}");
        }
    }
    assert!(
        reading
            .retained
            .iter()
            .any(|locus| carried.clock(*locus) == 2)
    );
    let dropped: u64 = carried
        .bits_by_locus()
        .into_iter()
        .filter(|(locus, _)| reading.released.contains(locus))
        .map(|(_, bits)| bits)
        .sum();
    assert_eq!(
        reading.bits,
        [carried.exact_bits(), carried.exact_bits() - dropped]
    );
    for g in 0..3 {
        assert_eq!(collapsed.passive_factor(g), carried.passive_factor(g));
        assert_eq!(collapsed.slices(g), carried.slices(g));
    }
    assert_eq!(collapsed.receiving_map(2), carried.receiving_map(2));
}

/// Lean `HNN/Retention.local_retention_blocks`, `constitution_descends`: `V` deletes whole loci; the
/// retained loci keep their exact values, the released ones count no bits.
#[test]
fn the_collapse_deletes_whole_loci() {
    let field = six_path(2);
    let theta = generic(&field, 53);
    let current = Current::at_rest(&field);
    let admitted = [phases(&field, &theta, &current)];
    let mut collapsed = theta.clone();
    let reading = collapse(&field, &mut collapsed, &admitted, Opens::AtRest).unwrap();
    let released: BTreeSet<Locus> = reading.released.clone();
    for g in 0..6 {
        let element = released.contains(&Locus::Element(g));
        assert_eq!(
            collapsed.passive_factor(g) == theta.passive_factor(g),
            !element
        );
        assert_eq!(collapsed.slices(g) == theta.slices(g), !element);
    }
    for a in 0..5 {
        let channel = released.contains(&Locus::Channel(a));
        assert_eq!(
            collapsed.contact_storage(a) == theta.contact_storage(a),
            !channel
        );
    }
    assert_eq!(collapsed.receiving_map(2), theta.receiving_map(2));
    let loci: BTreeSet<Locus> = collapsed
        .bits_by_locus()
        .into_iter()
        .map(|(locus, _)| locus)
        .collect();
    assert!(loci.is_disjoint(&released));
    assert!(reading.bits[1] < reading.bits[0]);
}

/// Ingest zeros until the joint clock carries out.
fn to_the_carry_out(reference: &Reference, resident: &mut crate::hnn::reference::Resident) {
    let (moment, _) = reference.ingest(resident, None, &[]).unwrap();
    for _ in 0..4096 {
        let (_, ingested) = reference
            .ingest(resident, Some(&moment), &one_hot(&[0]))
            .unwrap();
        if ingested.forward.present().unwrap().carry_out {
            return;
        }
    }
    panic!("the joint clock carries out");
}

/// The six-ring path with a second admitted receiver at ring 5 (aperture 1).
fn two_receiver_path() -> Field {
    let base = six_path(2);
    let mut declared = crate::hnn::field::FieldDeclaration {
        rings: (0..6).map(|_| super::support::ring(2, vec![0])).collect(),
        contacts: (0..5)
            .map(|g| super::support::contact(g, g + 1, 1, 0))
            .collect(),
        loops: Vec::new(),
        sources: vec![0],
        offsets: vec![1],
        alphabet: 2,
        step: integer(1),
        exponent_grain: 1,
        receivers: base.receivers().to_vec(),
        crib: base.crib(),
        population: 1 << 16,
        lattice: Default::default(),
    };
    declared.receivers.push(ReceiverDeclaration {
        ring: 5,
        aperture: 1,
        tolerance: crate::ratio::rat(1, 16),
        depth: 2,
        prior: crate::compression::landmark::context::StopPrior::half(),
        mass: 1,
        base: crate::compression::landmark::context::BaseMeasure::Even,
        receiving_prior: 0,
    });
    Field::declare(declared.by_lattice_rule()).unwrap()
}

/// Design (a), retention item 9, and the boundary's refusals: `close_aeon` is refused except at a
/// carry-out and refuses an admitted family larger than the previous boundary's; a pending ratio
/// whose reading does not factor through the collapse is refused, naming its separator, and a
/// pending ratio that factors is carried; a staged deposit that reaches a released locus is refused
/// with the released loci it would reach and discarded (design (c): `close_aeon` carries every open
/// handle or refuses it). Narrowing the admitted family releases loci only at the rest limit
/// (`A = I`): under the carry the collapse keeps every locus a source-to-receiver walk passes, and
/// on this connected path that is every locus (record B §8, Lean
/// `HNN/Retention.continuing_collapse_connected`), so the refusals this test reads are the rest
/// regime's and it declares it. Several pending ratios are lawful under either reception.
#[test]
fn the_boundary_reaches_the_pending_ratios_and_refuses_out_of_turn() {
    let field = two_receiver_path();
    let reference = Reference::campaign_one().with_reception(Reception::Rest);
    let theta = generic(&field, 57);
    // The mount certifies the field's Holarchy, whose contacts' momentum chart needs each storage
    // `C_a` invertible: this drawn constitution has a singular one and is refused, typed.
    assert!(matches!(
        reference.mount_with(&field, &Current::at_rest(&field), theta.clone()),
        Err(HnnError::Linear(_))
    ));
    let theta = (0..field.contacts().len()).fold(theta, |theta, a| {
        let k = field.contact(a).width();
        let (stiffness, dissipation) = (
            theta.contact_stiffness(a).clone(),
            theta.contact_dissipation(a).clone(),
        );
        theta
            .with_channel(
                a,
                crate::ratio::linear::ExactRatMatrix::identity(k).unwrap(),
                stiffness,
                dissipation,
            )
            .unwrap()
    });
    let mut resident = reference
        .mount_with(&field, &Current::at_rest(&field), theta)
        .unwrap();
    assert_eq!(resident.parametric(), &field.parametric());
    let near = resident.admitted()[0].clone();
    let far = resident.admitted()[1].clone();
    assert_eq!(
        reference
            .close_aeon(&mut resident, &[near.clone()])
            .unwrap_err(),
        HnnError::NotAtCarryOut
    );
    to_the_carry_out(&reference, &mut resident);
    assert_eq!(
        reference
            .ingest(&mut resident, None, &one_hot(&[1]))
            .unwrap_err(),
        HnnError::AeonAwaitingClose
    );
    let moment = crate::hnn::port::MomentId(1);
    let (kept, _) = reference.refine(&mut resident, &moment, &near).unwrap();
    let (lost, _) = reference.refine(&mut resident, &moment, &far).unwrap();
    let (compared, _) = reference.refine(&mut resident, &moment, &far).unwrap();
    let (staged, _) = reference
        .compare(&mut resident, compared, &one_hot(&[1]))
        .unwrap();
    let wider = ReceivingPhases::declare(
        &field,
        resident.constitution(),
        resident.current(),
        &ReceiverDeclaration {
            ring: 3,
            aperture: 1,
            tolerance: crate::ratio::rat(1, 16),
            depth: 2,
            prior: crate::compression::landmark::context::StopPrior::half(),
            mass: 1,
            base: crate::compression::landmark::context::BaseMeasure::Even,
            receiving_prior: 0,
        },
    )
    .unwrap();
    assert_eq!(
        reference
            .close_aeon(&mut resident, &[near.clone(), wider])
            .unwrap_err(),
        HnnError::AdmittedGrowth { receivers: vec![3] }
    );
    let boundary = reference
        .close_aeon(&mut resident, &[near.clone()])
        .unwrap()
        .forward
        .into_present()
        .unwrap();
    assert_eq!(boundary.carried, vec![kept]);
    assert_eq!(boundary.refused.len(), 1);
    // The aeon through its owners: the forward word between its two lift points on the certified
    // Holarchy's parametric orientation, each ring's reading its displacement in turns, its epochs
    // the flux through its section. The last ring crosses its section once; its own lock steps it
    // past the section, so the aeon read on its clock is not a cycle, a declared absence.
    let aeon = boundary.aeon(resident.parametric()).unwrap();
    assert_eq!(
        (aeon.start(), aeon.end()),
        (&boundary.opening, &boundary.carry_out)
    );
    for (ring, reading) in boundary.readings.iter().enumerate() {
        let displacement = &boundary.carry_out[ring] - &boundary.opening[ring];
        assert_eq!(
            reading.turns(),
            Rat::new(displacement.clone(), integer(2).to_integer())
        );
        let crossings = (&boundary.carry_out[ring] / 2) - (&boundary.opening[ring] / 2);
        assert_eq!(boundary.epochs[ring], crossings);
    }
    assert_eq!(boundary.epochs[5], 1.into());
    assert!(!boundary.readings[5].is_whole());
    assert!(matches!(
        boundary.closing,
        crate::receiver::reception::Component::Absent(_)
    ));
    assert!(matches!(
        boundary.view,
        crate::receiver::reception::Component::Absent(_)
    ));
    // One compare ran in the aeon, and the collapse released loci its diamond reads: the first law
    // read one arrival, and the release re-read it as an exchange step.
    assert_eq!(boundary.first_law.arrivals, 1);
    assert_eq!(boundary.first_law.exchanges, 1);
    assert_eq!(boundary.refused_staged.len(), 1);
    let (refused_staged, reaching) = &boundary.refused_staged[0];
    assert_eq!(*refused_staged, staged);
    assert!(reaching.contains(&Locus::Channel(4)));
    assert!(
        reaching
            .iter()
            .all(|locus| boundary.collapse.released.contains(locus))
    );
    assert!(
        reference
            .discard(&mut resident, Handle::Staged(staged))
            .is_err()
    );
    // The collapse released loci: the state without it keeps them, at their bits when released.
    let released = boundary.collapse.bits[0] - boundary.collapse.bits[1];
    assert!(released > 0);
    assert_eq!(
        resident.state_bits_without_collapse(),
        resident.state_bits() + released
    );
    let (refused, separator) = &boundary.refused[0];
    assert_eq!(*refused, lost);
    assert!(separator.contains(&Locus::Junction(5)) && separator.contains(&Locus::Channel(4)));
    assert!(
        reference
            .discard(&mut resident, Handle::Pending(lost))
            .is_err()
    );
    // The family may shrink but never grow back past the boundary it shrank at.
    assert_eq!(
        contained_after(&reference, &mut resident, &[near, far]),
        HnnError::AdmittedGrowth { receivers: vec![5] }
    );
}

fn contained_after(
    reference: &Reference,
    resident: &mut crate::hnn::reference::Resident,
    admitted: &[ReceivingPhases],
) -> HnnError {
    to_the_carry_out(reference, resident);
    reference.close_aeon(resident, admitted).unwrap_err()
}

/// [definition; record B §8] **A releasing collapse under the carry releases the motion its
/// material held.** Closing an aeon onto no receiver releases every materialized locus (no walk
/// reaches an admitted receiver). The carried end held momentum `π_a = C_a w_a` at the contacts;
/// a released contact's storage is zero, so no rate holds that momentum on the next opening, and
/// the motion leaves with the material (`ReceptionCarry::released`): the resident's carry is the
/// held one with every released contact's state and momentum zero, and the collapsed medium reads
/// on. Two pending ratios open across the boundary, as the card's
/// `the_card_port_returns_the_reference_through_a_releasing_collapse` runs it.
#[test]
fn a_releasing_collapse_releases_the_carried_motion_its_material_held() {
    let field = super::learning::chain();
    let reference = Reference::campaign_one();
    let mut resident = reference
        .mount_with(&field, &Current::at_rest(&field), generic(&field, 23))
        .unwrap();
    let (moment, _) = reference.ingest(&mut resident, None, &[]).unwrap();
    let phases = resident.admitted()[0].clone();
    let mut draw = Draw::new(23);
    let cells: Vec<usize> = (0..64)
        .map(|k| if draw.below(8) == 0 { draw.below(4) } else { [0, 1, 2, 1][k % 4] })
        .collect();
    let mut position = 0;
    loop {
        let (id, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
        let targets = one_hot(&cells[position..position + 2]);
        let (staged, _) = reference.compare(&mut resident, id, &targets).unwrap();
        reference.deposit(&mut resident, staged).unwrap();
        let (_, ingested) = reference
            .ingest(&mut resident, Some(&moment), &targets)
            .unwrap();
        let ingested = ingested.forward.into_present().unwrap();
        position += ingested.cells;
        if ingested.carry_out {
            break;
        }
        assert!(position + 2 <= cells.len(), "the joint clock carries out within the cut");
    }
    let (id, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    let (other, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    reference
        .compare(&mut resident, other, &one_hot(&[1, 2]))
        .unwrap();
    let held = resident.carried().cloned().expect("the refine writes the carry");
    assert!(
        held.momenta.iter().flatten().any(|x| !x.is_zero()),
        "the carried end holds momentum at a contact"
    );
    let boundary = reference.close_aeon(&mut resident, &[]).unwrap();
    let collapse = &boundary.forward.present().unwrap().collapse;
    assert!(collapse.released.contains(&Locus::Channel(0)), "the collapse releases the contacts");
    let (expected, moved) = held.released(&collapse.released);
    assert!(!moved.is_empty(), "the released material held carried motion");
    let carry = resident.carried().expect("the carry stays, released where its material was");
    assert_eq!(carry, &expected);
    for locus in &collapse.released {
        if let Locus::Channel(a) = *locus {
            assert!(carry.change.states[a].iter().flatten().all(|x| x.is_zero()));
            assert!(carry.momenta[a].iter().all(|x| x.is_zero()));
            assert_eq!(carry.change.arrivals[a], held.change.arrivals[a], "the waves stay");
        }
    }
    // The collapsed medium reads on: a word opens on the released carry, and is compared.
    let _ = reference.compare(&mut resident, id, &one_hot(&[0, 1]));
    let (fresh, _) = reference.refine(&mut resident, &moment, &phases).unwrap();
    reference
        .compare(&mut resident, fresh, &one_hot(&[2, 3]))
        .unwrap();
    reference.read(&resident).unwrap();
}

/// The six rings of the six-ring path split in two: `0–1–2` (source ring 0, receiver ring 2) and
/// `3–4–5` (source ring 3, every ring reached from a source), which no walk from a source to the
/// receiver passes.
fn split_path() -> Field {
    let base = six_path(2);
    let declared = crate::hnn::field::FieldDeclaration {
        rings: (0..6).map(|_| super::support::ring(2, vec![0])).collect(),
        contacts: [0, 1, 3, 4]
            .into_iter()
            .map(|g| super::support::contact(g, g + 1, 1, 0))
            .collect(),
        loops: Vec::new(),
        sources: vec![0, 3],
        offsets: vec![1],
        alphabet: 2,
        step: integer(1),
        exponent_grain: 1,
        receivers: base.receivers().to_vec(),
        crib: base.crib(),
        population: 1 << 16,
        lattice: Default::default(),
    };
    Field::declare(declared.by_lattice_rule()).unwrap()
}

/// A collapse onto the receiver's own family changes no step a compare's deposit takes on
/// `theta` (each family's certified step, gain and moves, the joint reading, the lobe's hold, the
/// lock's proposal and the medium's pumped rings), and a deposit then the collapse equals the
/// collapse then the deposit. Returns the deposit's reading.
fn collapse_changes_no_step(
    field: &Field,
    theta: &Constitution,
    opens: Opens,
    released: &[Locus],
) -> DepositReading {
    let (current, open) = moment(field, 52, 11);
    let phases = phases(field, theta, &current);
    let admitted = [phases.clone()];
    let pending = PendingRatio::produce(
        &current,
        &open,
        &ActiveAddress::boundary(phases.depth()),
        &phases,
        0,
    )
    .unwrap();
    let mut collapsed = theta.clone();
    let reading = collapse(field, &mut collapsed, &admitted, opens).unwrap();
    for locus in released {
        assert!(reading.released.contains(locus), "{opens:?}: {locus:?} is released");
    }
    let (mut first, whole) = deposit_read(field, theta, &pending);
    let (second, kept) = deposit_read(field, &collapsed, &pending);
    assert!(!whole.steps.is_empty(), "{opens:?}: the deposit steps");
    assert_eq!(whole.steps, kept.steps, "{opens:?}");
    assert_eq!(whole.joint, kept.joint, "{opens:?}");
    assert_eq!(whole.lobe, kept.lobe, "{opens:?}");
    assert_eq!(whole.lock, kept.lock, "{opens:?}");
    assert_eq!(whole.pumped, kept.pumped, "{opens:?}");
    collapse(field, &mut first, &admitted, opens).unwrap();
    assert_ne!(second, collapsed, "the deposit moves the retained loci");
    assert_eq!(first, second, "{opens:?}");
    whole
}

/// [definition; record B §8, the reviewer's gap of October 4] **A collapse that releases a pumped
/// ring changes no step a deposit takes.** The joint certified step reads the medium's growth (the
/// contrast ports' `1 + ω`, the span factor `F(s)` of the rings not certified passive) only on the
/// rings the word's diamond holds, which a stepped difference passes on its way to the receiver's
/// stations; the collapse releases every other ring. Under the carry, on the split path, the
/// continuing collapse releases rings 3–5; at rest, on the six-ring path, the rest collapse releases
/// rings 3–5 too. With ring 4 pumped the deposit reads no pumped ring, and it takes the same steps
/// on the uncollapsed and the collapsed constitution.
#[test]
fn a_collapse_releasing_a_pumped_ring_changes_no_step() {
    for (field, opens) in [(split_path(), Opens::OnMotion), (six_path(2), Opens::AtRest)] {
        let theta = super::prediction::pumped_at(&field, generic(&field, 51), 4);
        let released = [Locus::Resonator(4), Locus::Element(4)];
        let whole = collapse_changes_no_step(&field, &theta, opens, &released);
        assert!(whole.pumped.is_none(), "{opens:?}: ring 4 is outside the word's diamond");
    }
}

/// [definition; record B §8, the reviewer's gap of October 4] **A collapse that releases a
/// standing's neighbours changes no lobe hold.** The standing's step leaves the joint certificate
/// and is held in its lobes, halved with every family whose move reaches a crossed slice. The lobes
/// held are the slices of the rings the word's diamond holds: an element outside it is read by no
/// admitted reading. On the six-ring path at rest the standing of ring 3 is retained beside the
/// element of ring 2, and the elements of rings 3–5 and the standings of rings 4 and 5 are released.
/// Each contact block is the identity on the node's two coordinates, so on them
/// `Δ_3 = −q_3 + q_2 + q_4` and `Δ_4 = −q_4 + q_3 + q_5`. The standings are set so that both are
/// zero there, their nodes, and a hand-built deposit steps `q_3` up on the first coordinate and down
/// on the second, which turns a slice of ring 3 and one of ring 4 negative: it crosses both. The
/// collapse zeroes `q_4` and `q_5`, so there `Δ_3 = q_2 − q_3` and `Δ_4 = q_3`, and the same move
/// crosses neither. The deposit, read on the diamond of the word (rings 0–2), takes the same step
/// on both, the lobe holds nothing, and a deposit then the collapse equals the collapse then the
/// deposit.
#[test]
fn a_collapse_releasing_a_standings_neighbours_changes_no_lobe_hold() {
    let field = six_path(2);
    let standings = [
        (2, [rat(1, 1), rat(-1, 2), rat(1, 2), rat(1, 1)]),
        (3, [rat(1, 2), rat(1, 1), rat(-1, 1), rat(1, 2)]),
        (4, [rat(-1, 2), rat(3, 2), rat(1, 1), rat(-1, 2)]),
        (5, [rat(-1, 1), rat(1, 2), rat(1, 2), rat(1, 1)]),
    ];
    let theta = standings
        .into_iter()
        .fold(generic(&field, 51), |theta, (ring, standing)| {
            theta.with_ports(ring, Some(standing.to_vec()), None, None).unwrap()
        });
    let contrasts = theta.standing_contrasts();
    assert!(contrasts[3][..2].iter().chain(&contrasts[4][..2]).all(Zero::is_zero));
    let (current, _) = moment(&field, 52, 11);
    let admitted = [phases(&field, &theta, &current)];
    let mut collapsed = theta.clone();
    let reading = collapse(&field, &mut collapsed, &admitted, Opens::AtRest).unwrap();
    for locus in [Locus::Element(3), Locus::Element(4), Locus::Standing(4), Locus::Standing(5)] {
        assert!(reading.released.contains(&locus), "{locus:?} is released");
    }
    assert!(reading.retained.contains(&Locus::Standing(3)));
    let deposit = |commit: u64| {
        Deposit::new(
            commit,
            Vec::new(),
            vec![FactorStep {
                gradient: FactorGradient::Standing {
                    ring: 3,
                    gradient: vec![integer(1 << 12), integer(-(1 << 12)), Rat::zero(), Rat::zero()],
                    reach: vec![(3, Rat::zero()), (2, integer(1)), (4, Rat::zero())],
                },
                energy: Rat::zero(),
                covector: integer(1),
            }],
            Vec::new(),
        )
        .with_reach(Reach {
            receiver: 2,
            stations: vec![1, 2],
            entries: vec![0],
            phases: 1,
            loci: Diamond::of(&field, &admitted[0]).retained(&field),
        })
    };
    let (mut first, whole) = theta.deposited(&deposit(theta.commit())).unwrap();
    let (second, kept) = collapsed.deposited(&deposit(collapsed.commit())).unwrap();
    assert!(
        whole
            .steps
            .iter()
            .any(|(locus, step)| *locus == Locus::Standing(3) && step.family == Family::Standing),
        "the standing of ring 3 steps"
    );
    assert!(whole.lobe.is_none());
    assert_eq!(whole.steps, kept.steps);
    assert_eq!(whole.lobe, kept.lobe);
    assert_eq!(whole.lock, kept.lock);
    collapse(&field, &mut first, &admitted, Opens::AtRest).unwrap();
    assert_ne!(second, collapsed, "the deposit moves the retained standing");
    assert_eq!(first, second);
}

/// The six-ring path at rest, its compare's pending ratio and admitted family (the fixtures of the
/// gates below).
fn six_path_at_rest(theta: &Constitution) -> (Field, PendingRatio, [ReceivingPhases; 1]) {
    let field = six_path(2);
    let (current, open) = moment(&field, 52, 11);
    let phases = phases(&field, theta, &current);
    let pending = PendingRatio::produce(
        &current,
        &open,
        &ActiveAddress::boundary(phases.depth()),
        &phases,
        0,
    )
    .unwrap();
    (field, pending, [phases])
}

/// [definition; record B §8, the reviewer's third routes of October 4] **A declared boost refuses
/// the steps whose word reads its channel, and no others.** A boost's signed stiffness stores
/// indefinite energy, so no gain is certified through a channel that carries one, and a deposit
/// whose word reads the channel's transit is refused (`ActiveContact`). A difference stepped at a
/// locus passes only the channels its word's diamond holds; a released channel's stiffness is zero,
/// so its signature signs nothing. On the six-ring path at rest, a boost on contact 4 (rings 4–5,
/// released by the rest collapse) refuses nothing and changes no step, collapsed or not; a boost on
/// contact 1 (rings 1–2, in the word) refuses the deposit on both.
#[test]
fn a_boost_refuses_only_the_steps_whose_word_reads_its_channel() {
    let field = six_path(2);
    let signed = |contact: usize| {
        let k = field.contact(contact).width();
        generic(&field, 51)
            .with_contact_signature(&field, contact, (0..k).map(|j| j != 0).collect())
            .unwrap()
    };
    let off = signed(4);
    collapse_changes_no_step(&field, &off, Opens::AtRest, &[Locus::Channel(4)]);
    let on = signed(1);
    let (field, pending, admitted) = six_path_at_rest(&on);
    let mut collapsed = on.clone();
    collapse(&field, &mut collapsed, &admitted, Opens::AtRest).unwrap();
    for theta in [&on, &collapsed] {
        assert_eq!(
            deposit_try(&field, theta, &pending).unwrap_err(),
            HnnError::ActiveContact { contact: 1 }
        );
    }
}

/// [definition; record B §8, the reviewer's third routes and law point of October 4] **The budget
/// reads the resident's retention.** `B_Θ` refuses a deposit whose successor's exact bits pass it,
/// and it bounds what the resident holds. After the admitted family's collapse the resident holds
/// its retention: counted over every unreleased locus, the bits include material the collapse
/// releases, so a deposit refused before the collapse would pass after it; counted over the word's
/// diamond alone, they omit material the collapse keeps and later words read, so a deposit would
/// pass while the retained resident is past `B_Θ`. On the six-ring path, a word opened at rest
/// reads rings 0–2. With `B_Θ` at the successor's bits on the rest retention (which holds the
/// word's diamond), the deposit passes against the rest retention on the uncollapsed and the
/// collapsed constitution alike and commutes with the collapse, while under the carry, whose
/// collapse keeps all six rings, the same deposit is refused although the word's diamond count
/// passes.
#[test]
fn the_budget_reads_the_residents_retention() {
    let open = generic(&six_path(2), 51);
    let (field, pending, admitted) = six_path_at_rest(&open);
    let (successor, _) = deposit_read(&field, &open, &pending);
    let word = Diamond::of(&field, &admitted[0]).retained(&field);
    let rest = retained(&field, &admitted, Opens::AtRest);
    let carry = retained(&field, &admitted, Opens::OnMotion);
    let read = successor.bits_within(&rest);
    assert!(successor.bits_within(&word) <= read);
    assert!(
        read < successor.bits_within(&carry),
        "the carry keeps rings 3–5: {read} against {}",
        successor.bits_within(&carry)
    );
    let theta = super::learning::generic_within(&field, 51, read);
    let mut collapsed = theta.clone();
    collapse(&field, &mut collapsed, &admitted, Opens::AtRest).unwrap();
    let deposit = compose_deposit(&field, &theta, &pending);
    let (mut first, reading) = theta.deposited_within(&deposit, &rest).unwrap();
    assert_eq!(reading.bits, successor.exact_bits());
    let (second, _) = collapsed
        .deposited_within(&compose_deposit(&field, &collapsed, &pending), &rest)
        .unwrap();
    collapse(&field, &mut first, &admitted, Opens::AtRest).unwrap();
    assert_eq!(first, second);
    for refused in [theta.deposited_within(&deposit, &carry), theta.deposited(&deposit)] {
        assert!(matches!(refused, Err(HnnError::ConstitutionBudget { .. })));
    }
}

/// [definition; record B §8, the coordinator's two moves of October 4] **A re-base reads the
/// resident's retention.** The contacts' refining grain re-bases each retained channel, a move of
/// that channel alone, admitted against `B_Θ`. Counted over every unreleased locus, its bits include
/// material the collapse releases: a re-base refused before the collapse would pass after it. Its
/// budget reads the resident's retention and its channel, as a deposit's does. On the six-ring path
/// at rest, with `B_Θ` at the re-based successor's bits on the rest retention (below its bits on
/// every locus), contact 0's re-base passes on the uncollapsed and the collapsed constitution
/// alike, one bit less refuses it on both, and the re-base commutes with the collapse.
#[test]
fn a_rebase_reads_the_residents_retention() {
    let field = six_path(2);
    let (_, _, admitted) = six_path_at_rest(&generic(&field, 51));
    let reads = retained(&field, &admitted, Opens::AtRest);
    let locus = Locus::Channel(0);
    assert!(reads.contains(&locus));
    let every: BTreeSet<Locus> = loci(&field).into_iter().collect();
    let measured = generic(&field, 51).rebased(locus, 3, &every).unwrap();
    let (read, whole) = (measured.bits_within(&reads), measured.exact_bits());
    assert!(read < whole, "the released rings hold bits: {read} against {whole}");
    let theta = super::learning::generic_within(&field, 51, read);
    let mut collapsed = theta.clone();
    let reading = collapse(&field, &mut collapsed, &admitted, Opens::AtRest).unwrap();
    assert!(reading.released.contains(&Locus::Element(4)));
    let mut first = theta.rebased(locus, 3, &reads).unwrap();
    let second = collapsed.rebased(locus, 3, &reads).unwrap();
    assert_eq!(first.contact_storage(0), second.contact_storage(0));
    collapse(&field, &mut first, &admitted, Opens::AtRest).unwrap();
    assert_eq!(first, second);
    let tight = super::learning::generic_within(&field, 51, read - 1);
    for theta in [tight.clone(), {
        let mut c = tight;
        collapse(&field, &mut c, &admitted, Opens::AtRest).unwrap();
        c
    }] {
        assert!(matches!(
            theta.rebased(locus, 3, &reads),
            Err(HnnError::ConstitutionBudget { .. })
        ));
    }
}

/// [definition; record B §8, the coordinator's two moves of October 4] **The executed source step
/// reads the retention under the carry.** The executed comparison's step moves the receiving ring's
/// source port alone, admitted against `B_Θ`, and its refinement's words continue under the carry,
/// so the resident it bounds is the retention that collapse keeps for the declared ring
/// ([`retained_on_motion`]). On the split path the continuing collapse releases rings 3–5. With
/// `B_Θ` at the stepped successor's bits on that retention (below its bits on every locus), the
/// step passes on the uncollapsed and the collapsed constitution alike with the same reading, one
/// bit less refuses it on both, and the step commutes with the collapse.
#[test]
fn the_source_step_reads_the_retention_under_the_carry() {
    let field = split_path();
    let open = generic(&field, 51);
    let (current, _) = moment(&field, 52, 11);
    let admitted = [phases(&field, &open, &current)];
    let reads = retained_on_motion(&field, &[admitted[0].ring()]);
    assert_eq!(reads, retained(&field, &admitted, Opens::OnMotion));
    let ring = field.sources()[0];
    let port = open.source_port(ring).unwrap().clone();
    let unit = |n: usize| (0..n).map(|j| integer(i64::from(j == 0))).collect::<Vec<_>>();
    let samples = [crate::hnn::constitution::Sample {
        weight: integer(1),
        feature: unit(port.columns()),
        covector: unit(port.rows()),
    }];
    let step = integer(1);
    let every: BTreeSet<Locus> = loci(&field).into_iter().collect();
    let (measured, _) = open.stepped_source(ring, &samples, &step, &every).unwrap().unwrap();
    let (read, whole) = (measured.bits_within(&reads), measured.exact_bits());
    assert!(read < whole, "the released rings hold bits: {read} against {whole}");
    let collapsed_at = |theta: &Constitution| {
        let mut collapsed = theta.clone();
        let reading = collapse(&field, &mut collapsed, &admitted, Opens::OnMotion).unwrap();
        assert!(reading.retained.contains(&Locus::SourcePort(ring)));
        assert!(reading.released.contains(&Locus::Element(4)));
        collapsed
    };
    let theta = super::learning::generic_within(&field, 51, read);
    let collapsed = collapsed_at(&theta);
    let (mut first, before) = theta.stepped_source(ring, &samples, &step, &reads).unwrap().unwrap();
    let (second, after) =
        collapsed.stepped_source(ring, &samples, &step, &reads).unwrap().unwrap();
    let unbilled = |step: crate::hnn::constitution::SourceStep| {
        crate::hnn::constitution::SourceStep { bits: 0, ..step }
    };
    assert_eq!(unbilled(before), unbilled(after));
    assert_ne!(first.source_port(ring), theta.source_port(ring), "the step moves the port");
    collapse(&field, &mut first, &admitted, Opens::OnMotion).unwrap();
    assert_eq!(first, second);
    let tight = super::learning::generic_within(&field, 51, read - 1);
    for theta in [collapsed_at(&tight), tight] {
        assert!(matches!(
            theta.stepped_source(ring, &samples, &step, &reads),
            Err(HnnError::ConstitutionBudget { .. })
        ));
    }
}
