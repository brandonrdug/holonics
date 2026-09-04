use super::chart::{derive_occurrence, section_face};
use super::*;
use soma_membrane::SparseStandingSurface;

const AUDIO: SynchronizedReceiverId = SynchronizedReceiverId(1);
const VIDEO: SynchronizedReceiverId = SynchronizedReceiverId(2);
const TEXT: SynchronizedReceiverId = SynchronizedReceiverId(3);

fn integer(value: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
}

fn action() -> ActionCurrent {
    ActionCurrent::new(Cog::lit(1)).unwrap()
}

fn clock() -> ExactClockTransport {
    ExactClockTransport::new(integer(0), integer(0), integer(1)).unwrap()
}

fn cell(
    id: u64,
    chart: u64,
    material: i64,
    begin: i64,
    end: i64,
    stage: u32,
    origin: SynchronizedCellOrigin,
) -> TimedReceiverCell {
    TimedReceiverCell::new(
        SynchronizedCellId(id),
        ReceiverChartIdentity::new(chart),
        chart,
        relation_atom(material).unwrap(),
        integer(begin),
        integer(end),
        stage,
        origin,
    )
    .unwrap()
}

fn occurrence(
    occurrence: u64,
    audio_material: i64,
    video_material: i64,
    text_material: i64,
    text_origin: SynchronizedCellOrigin,
) -> ExactSynchronizedOccurrence {
    ExactSynchronizedOccurrence::new(
        occurrence,
        ReceiverChartIdentity::new(900),
        relation_atom(1).unwrap(),
        2,
        vec![
            SynchronizedReceiverSection::new(
                AUDIO,
                clock(),
                vec![cell(
                    occurrence * 10 + 1,
                    101,
                    audio_material,
                    0,
                    1,
                    0,
                    SynchronizedCellOrigin::Inherited,
                )],
            )
            .unwrap(),
            SynchronizedReceiverSection::new(
                VIDEO,
                clock(),
                vec![cell(
                    occurrence * 10 + 2,
                    201,
                    video_material,
                    0,
                    1,
                    0,
                    SynchronizedCellOrigin::Inherited,
                )],
            )
            .unwrap(),
            SynchronizedReceiverSection::new(
                TEXT,
                clock(),
                vec![cell(
                    occurrence * 10 + 3,
                    301,
                    text_material,
                    0,
                    1,
                    1,
                    text_origin,
                )],
            )
            .unwrap(),
        ],
        [
            SynchronizedInteraction::new(AUDIO, TEXT).unwrap(),
            SynchronizedInteraction::new(VIDEO, TEXT).unwrap(),
            SynchronizedInteraction::new(AUDIO, VIDEO).unwrap(),
        ],
    )
    .unwrap()
}

#[test]
fn local_clocks_form_one_overlap_without_becoming_one_clock() {
    let half = BigRational::new(BigInt::from(1), BigInt::from(2));
    let audio_clock = ExactClockTransport::new(integer(0), integer(0), half.clone()).unwrap();
    let video_clock = ExactClockTransport::new(integer(10), integer(0), integer(1)).unwrap();
    let occurrence = ExactSynchronizedOccurrence::new(
        1,
        ReceiverChartIdentity::new(900),
        relation_atom(1).unwrap(),
        2,
        vec![
            SynchronizedReceiverSection::new(
                AUDIO,
                audio_clock,
                vec![TimedReceiverCell::new(
                    SynchronizedCellId(1),
                    ReceiverChartIdentity::new(101),
                    101,
                    relation_atom(7).unwrap(),
                    integer(0),
                    integer(2),
                    0,
                    SynchronizedCellOrigin::Inherited,
                )
                .unwrap()],
            )
            .unwrap(),
            SynchronizedReceiverSection::new(
                TEXT,
                video_clock,
                vec![TimedReceiverCell::new(
                    SynchronizedCellId(2),
                    ReceiverChartIdentity::new(301),
                    301,
                    relation_atom(11).unwrap(),
                    integer(10),
                    integer(11),
                    1,
                    SynchronizedCellOrigin::Inherited,
                )
                .unwrap()],
            )
            .unwrap(),
        ],
        [SynchronizedInteraction::new(AUDIO, TEXT).unwrap()],
    )
    .unwrap();

    let contacts = SynchronizedOccurrenceChart::new()
        .contacts(&occurrence)
        .unwrap();
    assert_eq!(contacts.len(), 1);
    assert_eq!(contacts[0].interval_begin, integer(0));
    assert_eq!(contacts[0].interval_end, integer(1));
    assert_eq!(occurrence.sections[0].clock.occurrence_per_local, half);
    assert_eq!(occurrence.sections[1].clock.local_origin, integer(10));
}

#[test]
fn juxtaposed_interactions_keep_distinct_local_horizons() {
    let occurrence = occurrence(1, 7, 13, 17, SynchronizedCellOrigin::Inherited);
    let derived = derive_occurrence(&occurrence, &mut SynchronizedOccurrenceChart::new()).unwrap();
    assert_eq!(derived.elementary_intervals, 1);
    assert_eq!(derived.relations.len(), 3);
    assert_eq!(derived.horizons.len(), 3);
    assert_eq!(
        derived
            .relations
            .iter()
            .map(|relation| relation.receiver)
            .collect::<BTreeSet<_>>()
            .len(),
        3
    );
}

#[test]
fn one_holistic_contact_carries_independently_reachable_factor_germs() {
    let occurrence = ExactSynchronizedOccurrence::new(
        1,
        ReceiverChartIdentity::new(900),
        relation_atom(1).unwrap(),
        2,
        vec![
            SynchronizedReceiverSection::new(
                AUDIO,
                clock(),
                vec![
                    cell(1, 101, 7, 0, 1, 0, SynchronizedCellOrigin::Inherited),
                    cell(2, 102, 11, 0, 1, 0, SynchronizedCellOrigin::Inherited),
                ],
            )
            .unwrap(),
            SynchronizedReceiverSection::new(
                TEXT,
                clock(),
                vec![cell(3, 301, 17, 0, 1, 1, SynchronizedCellOrigin::Inherited)],
            )
            .unwrap(),
        ],
        [SynchronizedInteraction::new(AUDIO, TEXT).unwrap()],
    )
    .unwrap();
    let derived = derive_occurrence(&occurrence, &mut SynchronizedOccurrenceChart::new()).unwrap();
    assert_eq!(derived.relations.len(), 1);
    assert_eq!(derived.relations[0].support_slots.len(), 2);
    assert!(derived.relations[0]
        .support_slots
        .iter()
        .all(|factor| factor.len() > 1));

    let mut machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(8).unwrap());
    let received = SynchronizedOccurrenceChart::new()
        .observe(&mut machine, &occurrence, action())
        .unwrap();
    assert_eq!(received.contacts.len(), 1);
    assert_eq!(machine.standing().constituents().len(), 1);
    assert_eq!(
        machine.standing().constituents()[0].support_factor_count(),
        2
    );
}

#[test]
fn structural_section_fibers_do_not_depend_on_first_delivery() {
    let first = occurrence(1, 7, 13, 17, SynchronizedCellOrigin::Inherited);
    let second = occurrence(2, 19, 23, 29, SynchronizedCellOrigin::Inherited);
    let first_face = section_face(&[&first.sections[0].cells[0]]);
    let second_face = section_face(&[&second.sections[0].cells[0]]);

    let mut forward = SynchronizedOccurrenceChart::new();
    let forward_first = forward.receive_section_fiber(&first_face).unwrap();
    let forward_second = forward.receive_section_fiber(&second_face).unwrap();
    let mut reverse = SynchronizedOccurrenceChart::new();
    let reverse_second = reverse.receive_section_fiber(&second_face).unwrap();
    let reverse_first = reverse.receive_section_fiber(&first_face).unwrap();

    assert_eq!(forward_first, reverse_first);
    assert_eq!(forward_second, reverse_second);
    assert_ne!(forward_first, forward_second);
    assert_eq!(forward_first.words().len(), 2 + 2 + COG_WORDS + 1);
}

#[test]
fn independent_delivery_interleavings_are_gauge_but_receiver_chronology_is_not() {
    let events = [
        occurrence(1, 7, 13, 17, SynchronizedCellOrigin::Inherited),
        occurrence(2, 19, 23, 29, SynchronizedCellOrigin::Inherited),
        occurrence(3, 7, 13, 17, SynchronizedCellOrigin::Inherited),
        occurrence(4, 19, 23, 29, SynchronizedCellOrigin::Inherited),
    ];
    let train = |schedule: [usize; 4]| {
        let machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(8).unwrap());
        let mut ecology = SynchronizedEcology::new(machine);
        for at in schedule {
            ecology.receive(&events[at], action()).unwrap();
        }
        ecology
    };

    // Each material lineage keeps its own first-before-return order. Only the delivery word
    // interleaving the two independent lineages changes.
    let alternating = train([0, 1, 2, 3]);
    let reversed_interleave = train([1, 0, 3, 2]);
    let blocked = train([0, 2, 1, 3]);
    assert_eq!(
        alternating.machine().standing(),
        reversed_interleave.machine().standing()
    );
    assert_eq!(
        alternating.machine().standing(),
        blocked.machine().standing()
    );
    assert_eq!(alternating.atlas(), reversed_interleave.atlas());
    assert_eq!(alternating.atlas(), blocked.atlas());
    assert_eq!(
        alternating.machine().rest_image().unwrap(),
        reversed_interleave.machine().rest_image().unwrap()
    );
    assert_eq!(
        alternating.machine().rest_image().unwrap(),
        blocked.machine().rest_image().unwrap()
    );

    let earlier_text = occurrence(10, 7, 13, 17, SynchronizedCellOrigin::Inherited);
    let mut earlier_sensory = earlier_text.clone();
    earlier_sensory.sections[0].cells[0].arrival_stage = 1;
    earlier_sensory.sections[1].cells[0].arrival_stage = 1;
    earlier_sensory.sections[2].cells[0].arrival_stage = 0;
    earlier_sensory.validate().unwrap();

    let passage_shape = |event: &ExactSynchronizedOccurrence| {
        derive_occurrence(event, &mut SynchronizedOccurrenceChart::new())
            .unwrap()
            .relations
            .into_iter()
            .flat_map(|relation| relation.arcs)
            .filter_map(|arc| {
                arc.interface().receiver_passage().map(|passage| {
                    (
                        passage.antecedent().identity(),
                        passage.antecedent_order(),
                        passage.consequent().identity(),
                        passage.consequent_order(),
                    )
                })
            })
            .collect::<BTreeSet<_>>()
    };
    assert_ne!(
        passage_shape(&earlier_text),
        passage_shape(&earlier_sensory)
    );

    let mut text_first = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(8).unwrap());
    let mut sensory_first = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(8).unwrap());
    SynchronizedOccurrenceChart::new()
        .observe(&mut text_first, &earlier_text, action())
        .unwrap();
    SynchronizedOccurrenceChart::new()
        .observe(&mut sensory_first, &earlier_sensory, action())
        .unwrap();
    assert_ne!(text_first.standing(), sensory_first.standing());
}

#[test]
fn swing_return_alone_establishes_the_sparse_association() {
    let machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(8).unwrap());
    let mut ecology = SynchronizedEcology::new(machine);
    let first = ecology
        .receive(
            &occurrence(1, 7, 13, 17, SynchronizedCellOrigin::Inherited),
            action(),
        )
        .unwrap();
    assert!(!first.contacts.is_empty());
    assert!(ecology
        .atlas()
        .relations
        .values()
        .all(|lineage| !lineage.established()));

    let second = ecology
        .receive(
            &occurrence(2, 7, 13, 17, SynchronizedCellOrigin::Inherited),
            action(),
        )
        .unwrap();
    assert!(second.contacts.iter().any(|contact| contact.formed_ride));
    assert!(ecology
        .atlas()
        .relations
        .values()
        .any(SynchronizedAssociationLineage::established));
}

#[test]
fn prediction_is_plural_topology_and_return_grades_before_conditioning() {
    let machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(8).unwrap());
    let mut ecology = SynchronizedEcology::new(machine);
    for event in 1..=2 {
        ecology
            .receive(
                &occurrence(event, 7, 13, 17, SynchronizedCellOrigin::Inherited),
                action(),
            )
            .unwrap();
    }
    for event in 3..=4 {
        ecology
            .receive(
                &occurrence(event, 19, 23, 29, SynchronizedCellOrigin::Inherited),
                action(),
            )
            .unwrap();
    }

    let alternatives = [
        SynchronizedPredictionAlternative {
            candidate: SynchronizedCandidateId(17),
            occurrence: occurrence(10, 7, 13, 17, SynchronizedCellOrigin::Candidate),
        },
        SynchronizedPredictionAlternative {
            candidate: SynchronizedCandidateId(29),
            occurrence: occurrence(10, 7, 13, 29, SynchronizedCellOrigin::Candidate),
        },
    ];
    let prediction = ecology.predict(TEXT, &alternatives).unwrap();
    assert_eq!(prediction.invariant, Some(SynchronizedCandidateId(17)));
    let revision_before = ecology.revision();
    let (grade, returned) = ecology
        .grade_then_receive(
            &prediction,
            SynchronizedCandidateId(17),
            &occurrence(10, 7, 13, 17, SynchronizedCellOrigin::Inherited),
            action(),
        )
        .unwrap();
    assert!(grade.exact_invariant);
    assert_eq!(grade.ecology_revision, revision_before);
    assert_eq!(returned.occurrence, 10);
    assert_eq!(ecology.revision(), revision_before + 1);
}

#[test]
fn machine_and_association_atlas_rest_and_remount_exactly() {
    let machine = LiveCurrentMachine::new(SparseStandingSurface::empty_rank(8).unwrap());
    let mut ecology = SynchronizedEcology::new(machine);
    for event in 1..=2 {
        ecology
            .receive(
                &occurrence(event, 7, 13, 17, SynchronizedCellOrigin::Inherited),
                action(),
            )
            .unwrap();
    }
    let revision = ecology.revision();
    let relation_population = ecology.atlas().relations.len();
    let rest = ecology.into_rest_image().unwrap();
    let remounted = SynchronizedEcology::from_rest_image(rest).unwrap();
    assert_eq!(remounted.revision(), revision);
    assert_eq!(remounted.atlas().relations.len(), relation_population);
}
