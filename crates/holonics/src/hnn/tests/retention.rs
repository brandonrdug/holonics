//! The collapse onto what the admitted future distinguishes: the time-indexed diamond on the
//! six-ring path of `release.py` (72 of 156 entries released at `A = 2`, 132 at `A = 1`), every
//! admitted reading unchanged with the released items replaced by arbitrary values, each retained
//! item tight, `deposit_descends`, whole-locus deletion, the pending ratios reached, and the
//! boundary's refusals.

use std::collections::BTreeSet;

use num_traits::Signed;

use super::learning::{generic, moment, path_with, phases, six_path};
use super::support::Draw;
use crate::hnn::HnnError;
use crate::hnn::constitution::{Constitution, Locus};
use crate::hnn::field::{ConstitutionRead, Current, Field, ReceiverDeclaration};
use crate::hnn::pending::PendingRatio;
use crate::hnn::port::{ExecutionPort, Handle};
use crate::hnn::propagation::Operands;
use crate::hnn::ratio::{HolonRatio, target_phases};
use crate::hnn::receiving::ReceivingPhases;
use crate::hnn::reference::{Reference, compose, one_hot};
use crate::hnn::retention::{Diamond, collapse, loci, retained};
use crate::hnn::word::Word;
use crate::ratio::{Rat, integer};

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
        let kept = retained(&field, &admitted);
        let of = |make: fn(usize) -> Locus, count: usize| -> Vec<usize> {
            (0..count).filter(|i| kept.contains(&make(*i))).collect()
        };
        assert_eq!(of(Locus::Element, 6), elements);
        assert_eq!(of(Locus::Junction, 6), vec![0, 1, 2]);
        assert_eq!(of(Locus::Channel, 5), channels);
        assert_eq!(of(Locus::Conductance, 5), conductances);
        let mut collapsed = theta.clone();
        let reading = collapse(&field, &mut collapsed, &admitted).unwrap();
        assert_eq!(
            (reading.released_entries, reading.total_entries),
            (released, 156)
        );
    }
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
        let kept = retained(&field, &admitted);
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
        collapse(&field, &mut collapsed, &admitted).unwrap();
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
/// `A = 2`, 8 of 8 at `A = 1`, as in `release.py`), read on the four unit injections that decide
/// every injection ([`injections`]).
#[test]
fn replacing_any_one_retained_item_changes_some_reading() {
    for (aperture, items) in [(2, 12), (1, 8)] {
        let field = six_path(aperture);
        let theta = generic(&field, 47);
        let current = Current::at_rest(&field);
        let admitted = [phases(&field, &theta, &current)];
        let kept: Vec<Locus> = retained(&field, &admitted)
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
    let (_, deposit) = compose(field, theta, pending, &back, &targets).unwrap();
    theta.deposited(&deposit).unwrap().0
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
    let pending = PendingRatio::produce(&current, &open, &phases, 0);
    let theta = deposited(&field, &generic(&field, 51), &pending);
    assert!(!theta.carried_remainders().is_empty());
    let pending = PendingRatio::produce(&current, &open, &phases, 1);
    let mut first = deposited(&field, &theta, &pending);
    collapse(&field, &mut first, &admitted).unwrap();
    let mut collapsed = theta.clone();
    collapse(&field, &mut collapsed, &admitted).unwrap();
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
    let theta = generic(&field, 55);
    let phases = phases(&field, &theta, &current);
    let pending = PendingRatio::produce(&current, &open, &phases, 0);
    let once = deposited(&field, &theta, &pending);
    let pending = PendingRatio::produce(&current, &open, &phases, 1);
    let carried = deposited(&field, &once, &pending);
    let before = carried.carried_remainders();
    assert!(!before.is_empty());
    let mut collapsed = carried.clone();
    let reading = collapse(&field, &mut collapsed, std::slice::from_ref(&phases)).unwrap();
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
    // with them, each reported exactly (Decision 22: "leaves whole, with its remainder, reported").
    let narrow = ReceivingPhases::declare(
        &field,
        &carried,
        &current,
        &ReceiverDeclaration {
            ring: phases.ring(),
            aperture: 1,
            tolerance: crate::ratio::rat(1, 16),
            regions: crate::hnn::masses::Regions::PrecedingCell,
        },
    )
    .unwrap();
    let mut shrunk = carried.clone();
    let narrowed = collapse(&field, &mut shrunk, &[narrow]).unwrap();
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
    let reading = collapse(&field, &mut collapsed, &admitted).unwrap();
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
        population: 1 << 20,
        lattice: Default::default(),
    };
    declared.receivers.push(ReceiverDeclaration {
        ring: 5,
        aperture: 1,
        tolerance: crate::ratio::rat(1, 16),
        regions: crate::hnn::masses::Regions::PrecedingCell,
    });
    Field::declare(declared.by_lattice_rule()).unwrap()
}

/// Design (a), retention item 9, and the boundary's refusals: `close_aeon` is refused except at a
/// carry-out and refuses an admitted family larger than the previous boundary's; a pending ratio
/// whose reading does not factor through the collapse is refused, naming its separator, and a
/// pending ratio that factors is carried; a staged deposit that reaches a released locus is refused
/// with the released loci it would reach and discarded (design (c): `close_aeon` carries every open
/// handle or refuses it).
#[test]
fn the_boundary_reaches_the_pending_ratios_and_refuses_out_of_turn() {
    let field = two_receiver_path();
    let reference = Reference::campaign_one();
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
            regions: crate::hnn::masses::Regions::PrecedingCell,
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
