use super::super::*;

/// The exterior order receiver acts on a declared sufficient row cover and leaves a plural
/// interval fibre unresolved rather than asking the host to select a row.

#[test]
#[ignore = "requires the RTX CUDA device"]
fn the_resident_interval_potential_receiver_selects_and_retains_plurality_on_card() {
    let card = CudaRefineExecutor::new().expect("the card mounts");
    let mut receiver = ResidentIntervalPotentialReceiver::mount(
        card,
        "test/potential-cover",
        3,
        2,
        &[7, 11, 13],
        &[
            4, 0, // row 7
            0, 6, // row 11
            3, 3, // row 13
        ],
        &[
            5, 1, // row 7
            1, 7, // row 11
            4, 4, // row 13
        ],
    )
    .expect("receiver cover mounts");
    let returned = receiver
        .conduct(&[vec![Rat::one(), Rat::zero()], vec![Rat::zero(), Rat::one()]])
        .expect("receiver returns");
    assert_eq!(returned.selected_native_addresses, vec![7, 11]);
    assert_eq!(returned.selected_lower, vec!["4", "6"]);
    assert_eq!(returned.selected_upper, vec!["5", "7"]);
    assert_eq!(returned.plural_population, vec![2, 1]);
    assert!(!returned.invariant_transport_reuploaded);
    assert!(!returned.cpu_semantic_replay_after_device);
}

/// The cpu law is exact on its own terms, without a card. A partition is an equivalence, so
/// this checks the property rather than the numbering.
#[test]
fn the_cpu_quotient_separates_exactly_on_the_pair() {
    let classes = [1u32, 1, 1, 2, 2];
    let keys = [10u64, 10, 11, 10, 11];
    let quotient = quotient_on_cpu(&classes, &keys);
    assert_eq!(quotient.classes, 4, "(1,10) (1,11) (2,10) (2,11)");
    assert_eq!(quotient.cell_class[0], quotient.cell_class[1]);
    assert_ne!(quotient.cell_class[0], quotient.cell_class[2]);
    assert_ne!(quotient.cell_class[0], quotient.cell_class[3]);
    assert!(quotient.same_partition_as(&Quotient {
        // A different numbering of the same partition must compare equal.
        cell_class: vec![9, 9, 8, 7, 6],
        classes: 4,
        carrier: QuotientCarrier::Device,
    }));
}

/// The physical-fold carrier: exact coordinate boxes cross once, and the matched presentation
/// pair is formed before the one terminal synchronization.
#[test]
#[ignore = "requires the RTX CUDA device"]
fn the_card_returns_contact_classes_and_the_ordered_cross_presentation_pair() {
    let mut card = CudaRefineExecutor::new().expect("the card mounts");
    // Five vertices: a free pair at squared distance 1, an occluded pair at squared distance
    // 9, and one interval [1,3] crossing the radius-2 aperture.
    let lower = [
        0_i64, 0, 0, // 0 free primary
        0, 1, 0, // 1 free secondary
        0, 0, 0, // 2 occluded primary
        0, 3, 0, // 3 occluded secondary
        1, 0, 0, // 4 uncertain secondary, x in [1,3]
    ];
    let upper = [0_i64, 0, 0, 0, 1, 0, 0, 0, 0, 0, 3, 0, 3, 0, 0];
    let returned = card
        .contact_passage_on_device(&lower, &upper, &[0, 2, 0], &[1, 3, 4], &[0], &[1], 4)
        .expect("the exact contact passage returns");
    assert_eq!(returned.contact_classes, vec![1, 0, 2]);
    assert_eq!(returned.paired_classes, vec![3]);
    assert_eq!(returned.launches, 2);
    assert_eq!(returned.synchronizations, 1);
}

/// The I2 return: finite closure, local commit, held-out change, disjoint control and targeted
/// ablation all cross in one resident deed.
#[test]
#[ignore = "requires the RTX CUDA device"]
fn the_card_returns_every_recurrence_after_one_local_difference() {
    let mut card = CudaRefineExecutor::new().expect("the card mounts");
    let returned = card
        .conduct_returned_recurrences_on_device(3, 1, &[1, 2, 1], 0, &[0, 1, 2], 17, 2, 2, 0)
        .expect("the returned recurrences close");
    assert!(returned.committed);
    assert_eq!(returned.trace_stride, 4);
    assert_eq!(returned.predecessor_lengths, vec![4, 3, 3]);
    assert_eq!(returned.successor_lengths, vec![4, 3, 2]);
    assert_eq!(returned.ablated_lengths, returned.predecessor_lengths);
    assert_eq!(&returned.predecessor_trace[..4], &[0, 1, 2, 1]);
    assert_eq!(&returned.successor_trace[..4], &[0, 1, 2, 2]);
    assert_eq!(returned.ablated_trace, returned.predecessor_trace);
    assert_eq!(returned.control_predecessor, 1);
    assert_eq!(returned.control_successor, 1);
    assert_eq!(returned.launches, 1);
    assert_eq!(returned.synchronizations, 1);
}

/// R3's returned receiver incidence: the card forms `A^T r`, commits the supported terminal
/// relation, changes a later start, and returns exact withdrawal in one launch.
#[test]
#[ignore = "requires the RTX CUDA device"]
fn the_card_returns_dynamic_morphology_from_the_receiver_adjoint() {
    let mut card = CudaRefineExecutor::new().expect("the card mounts");
    let returned = card
        .conduct_dynamic_morphology_on_device(
            &[0, 0],
            &[
                1, 0, // proof/checker
                1, 0, // exact owner
                1, 0, // rendering
                1, 0, // physical boundary
                1, 0, // later operator
            ],
            &[1, 1, 1, 1, 1],
            &[0, 1],
        )
        .expect("the dynamic morphology closes");
    assert_eq!(returned.returned_adjoint, vec![5, 0]);
    assert!(returned.committed);
    assert_eq!(returned.supported_state, Some(0));
    assert_eq!(returned.predecessor_action, vec![0, 0, 2]);
    assert_eq!(returned.successor_action, vec![2, 0, 2]);
    assert_eq!(returned.withdrawn_action, returned.predecessor_action);
    assert_eq!(returned.predecessor_lengths, vec![2, 3]);
    assert_eq!(returned.successor_lengths, vec![3, 4]);
    assert_eq!(returned.withdrawn_lengths, returned.predecessor_lengths);
    assert_eq!(&returned.predecessor_trace[..4], &[0, 0, 0, 0]);
    assert_eq!(&returned.successor_trace[..4], &[0, 2, 2, 2]);
    assert_eq!(returned.withdrawn_trace, returned.predecessor_trace);
    assert_eq!(returned.launches, 1);
    assert_eq!(returned.synchronizations, 1);

    let declined = card
        .conduct_dynamic_morphology_on_device(
            &[0, 0],
            &[1, 0, 1, 0, 1, 0, 1, 0, 1, 0],
            &[1, 1, 1, 1, 0],
            &[0, 1],
        )
        .expect("the incomplete returned family declines");
    assert_eq!(declined.returned_adjoint, vec![4, 0]);
    assert!(!declined.committed);
    assert_eq!(declined.successor_action, declined.predecessor_action);
    assert_eq!(declined.successor_trace, declined.predecessor_trace);
}

/// R4's resident context passage: distinct causal words retain their own extents and order
/// while the shared action crosses only once.
#[test]
#[ignore = "requires the RTX CUDA device"]
fn the_card_returns_plural_ragged_words_without_reordering_them() {
    let mut card = CudaRefineExecutor::new().expect("the card mounts");
    // Generator 0 is the R3 predecessor action; generator 1 is its cultivated successor.
    let returned = card
        .conduct_native_ragged_traces_on_device(
            3,
            2,
            &[0, 0, 2, 2, 0, 2],
            &[0, 1, 1, 0, 1],
            &[0, 2, 4, 5],
            &[1, 1, 0],
        )
        .expect("the plural addressed words return");
    assert_eq!(returned.trace_offsets, vec![0, 3, 6, 8]);
    assert_eq!(&returned.native_trace[0..3], &[1, 0, 2]);
    assert_eq!(&returned.native_trace[3..6], &[1, 0, 0]);
    assert_eq!(&returned.native_trace[6..8], &[0, 2]);
    assert_ne!(returned.native_trace[2], returned.native_trace[5]);
    assert_eq!(returned.launches, 1);
    assert_eq!(returned.synchronizations, 1);
    assert_eq!(returned.active_lanes, 3);
}

/// I3's recurrent condensation: a visited-incidence front returns both physical routes and
/// withdrawal of their shared generator without a host callback or authored trace extent.
#[test]
#[ignore = "requires the RTX CUDA device"]
fn the_card_returns_the_condensed_routes_and_shared_generator_withdrawal() {
    let mut card = CudaRefineExecutor::new().expect("the card mounts");
    let returned = card
        .conduct_condensed_recurrences_on_device(&[1, 2, 2], &[0, 1], 2, 1)
        .expect("the condensed recurrent family closes");
    assert_eq!(returned.trace_stride, 4);
    assert_eq!(returned.predecessor_lengths, vec![4, 3]);
    assert_eq!(returned.successor_lengths, vec![4, 3]);
    assert_eq!(returned.withdrawn_lengths, vec![2, 2]);
    assert_eq!(&returned.predecessor_trace[..4], &[0, 1, 2, 1]);
    assert_eq!(&returned.successor_trace[..4], &[0, 1, 2, 2]);
    assert_eq!(&returned.withdrawn_trace[..2], &[0, 0]);
    assert_eq!(returned.launches, 1);
    assert_eq!(returned.synchronizations, 1);
    assert_eq!(returned.visited_words, 1);
}

/// I4's conservation-of-faces law: the shared generator moves every port, while withdrawing
/// one port leaves the other on the shared successor.
#[test]
#[ignore = "requires the RTX CUDA device"]
fn the_card_enacts_one_shared_generator_and_every_local_withdrawal() {
    let mut card = CudaRefineExecutor::new().expect("the card mounts");
    // Two families × two ports × two states. Each native consequence has its own address.
    let returned = card
        .conduct_heterogeneous_fusion_on_device(
            &[1, 1],
            &[0, 1, 2, 3, 4, 5, 6, 7],
            &[0, 0, 0, 0],
            2,
            2,
        )
        .expect("the heterogeneous front returns");
    assert_eq!(returned.predecessor_consequence, vec![0, 2, 4, 6]);
    assert_eq!(returned.successor_consequence, vec![1, 3, 5, 7]);
    assert_eq!(returned.shared_ablated_consequence, vec![0, 2, 4, 6]);
    assert_eq!(
        returned.local_ablated_consequence,
        vec![0, 1, 3, 2, 4, 5, 7, 6]
    );
    assert_eq!(returned.launches, 1);
    assert_eq!(returned.synchronizations, 1);
}

/// R5's joint-media law: the source candidate population is counted without a winner and the
/// compact triadic subcomplex returns every shared/local withdrawal in one later front.
#[test]
#[ignore = "requires the RTX CUDA device"]
fn the_card_derives_and_enacts_the_joint_media_subcomplex() {
    let mut card = CudaRefineExecutor::new().expect("the card mounts");
    let source = card
        .derive_media_candidate_counts_on_device(
            &[0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2],
            &[0, 1, 1, 2, 0, 1, 2, 2, 0, 1, 2],
            3,
            3,
        )
        .expect("the complete source candidates return");
    assert_eq!(source.candidate_counts, vec![1, 2, 1, 1, 1, 2, 1, 1, 1]);
    assert_eq!(source.semantic_pair_visits, 99);

    let returned = card
        .conduct_joint_media_transport_on_device(
            &source.candidate_counts,
            3,
            &[1, 1],
            &[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11],
            &[0, 0, 0, 0, 0, 0],
            2,
            3,
        )
        .expect("the compact joint-media passage returns");
    assert_eq!(returned.joint_anchor, vec![1, 1, 1]);
    assert_eq!(returned.shared_ablated_joint_anchor, vec![0, 0, 0]);
    assert!(
        returned
            .local_ablated_joint_anchor
            .iter()
            .all(|value| *value == 0)
    );
    assert_eq!(returned.predecessor_consequence, vec![0, 2, 4, 6, 8, 10]);
    assert_eq!(returned.successor_consequence, vec![1, 3, 5, 7, 9, 11]);
    assert_eq!(returned.shared_ablated_consequence, vec![0, 2, 4, 6, 8, 10]);
    assert_eq!(returned.launches, 1);
    assert_eq!(returned.synchronizations, 1);
}
