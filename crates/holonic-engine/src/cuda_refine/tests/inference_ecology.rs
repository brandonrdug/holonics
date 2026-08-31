use super::super::*;

/// R6's fronts share no mutable standing and meet only after the exact card reduction.

#[test]
#[ignore = "requires the RTX CUDA device"]
fn the_card_returns_the_bounded_production_aperture_without_a_host_semantic_bridge() {
    let mut card = CudaRefineExecutor::new().expect("the card mounts");
    let returned = card
        .conduct_production_aperture_on_device(
            &[0, 0, 2, 2, 0, 2],
            3,
            &[0, 1, 0, 1],
            &[0, 1, 2],
            &[0, 0, 2],
            &[2, 0, 2],
            &[0, 1],
            &[1, 2, 3, 2, 1, 4, 2, 1],
            2,
            &[0, 1, 2, 2],
            3,
            2,
            3,
            true,
        )
        .expect("the production passage returns");
    assert_eq!(returned.context_trace_stride, 5);
    assert_eq!(returned.media_species_totals, vec![2, 6, 5, 3]);
    assert_eq!(returned.total_joint_incidence, 16);
    assert_eq!(returned.oriented_difference, 2);
    assert_eq!(returned.difference_magnitude, 2);
    assert_eq!(returned.difference_hand, 1);
    assert_eq!(returned.selected_cultivation_state, 1);
    assert_eq!(
        returned.derivation_selected_trace,
        returned.derivation_successor_trace
    );
    assert_eq!(returned.launches, 2);
    assert_eq!(returned.synchronizations, 1);
    assert_eq!(returned.typed_reductions, 1);
}

/// L0's first cross-family cultivation: two distinct homogeneous quadratic sections retain
/// their face under central inversion, while the mixed section under a single-axis reflection
/// returns the shortest separating obstruction.  Withdrawal selects the expanded route without
/// relaunching the law.
#[test]
#[ignore = "requires the RTX CUDA device"]
fn the_card_cultivates_and_dissects_quadratic_section_transport() {
    let mut card = CudaRefineExecutor::new().expect("the card mounts");
    let returned = card
        .conduct_quadratic_sections_on_device(
            &[1, 0, -1, 1, 0, 1, 0, 1, 0],
            &[-1, 0, 0, -1, -1, 0, 0, -1, -1, 0, 0, 1],
            true,
        )
        .expect("the quadratic sections return");
    assert_eq!(
        returned.transported_coefficients,
        vec![1, 0, -1, 1, 0, 1, 0, -1, 0]
    );
    assert_eq!(returned.invariant, vec![1, 1, 0]);
    assert_eq!(returned.selected_route, vec![1, 1, 2]);
    assert_eq!(returned.ablated_route, vec![0, 0, 2]);
    assert_eq!(returned.launches, 1);
    assert_eq!(returned.synchronizations, 1);
    assert_eq!(returned.semantic_work, 28);
    assert_eq!(returned.semantic_span, 5);
}

/// L1's common fixed-section law crosses an integer oriented-face family and an F2 additive
/// coordinate family without routing on their exterior subjects.  Both local withdrawals
/// reopen the composed route.
#[test]
#[ignore = "requires the RTX CUDA device"]
fn the_card_joins_independent_fixed_section_families_and_returns_every_local_ablation() {
    let mut card = CudaRefineExecutor::new().expect("the card mounts");
    let action = [0, -1, 1, -1, 0, 1, 1, 1, 0];
    let constraints = [1, 1, -1, 0, 0, 0, 0, 0, 0];
    let expanded = card
        .conduct_fixed_section_families_on_device(
            &[7, -7, 0, 1, 0, 1],
            &[action, action].concat(),
            &[constraints, constraints].concat(),
            &[1, 1],
            &[0, 2],
            &[0, 0],
        )
        .expect("the expanded family returns");
    assert_eq!(expanded.transported_sections, vec![7, -7, 0, 1, 0, 1]);
    assert_eq!(expanded.selected_route, vec![0, 0]);
    assert!(!expanded.joint_cultivated);
    assert_eq!(expanded.semantic_work, 46);

    let cultivated = card
        .conduct_fixed_section_families_on_device(
            &[7, -7, 0, 1, 0, 1],
            &[action, action].concat(),
            &[constraints, constraints].concat(),
            &[1, 1],
            &[0, 2],
            &[1, 1],
        )
        .expect("the cultivated family returns");
    assert_eq!(cultivated.constraint_held, vec![1, 1]);
    assert_eq!(cultivated.invariant, vec![1, 1]);
    assert_eq!(cultivated.selected_route, vec![1, 1]);
    assert_eq!(cultivated.ablated_route, vec![0, 0]);
    assert!(cultivated.joint_cultivated);
    assert_eq!(cultivated.local_ablated_joint, vec![0, 0]);
    assert_eq!(cultivated.semantic_work, 16);
    assert_eq!(cultivated.semantic_span, 5);
    assert_eq!(cultivated.predicted_local_semantic_work, vec![5, 20, 5, 20]);
    assert_eq!(cultivated.predicted_local_semantic_span, vec![3, 6, 3, 6]);
    assert_eq!(
        cultivated.host_ingress_octets + cultivated.host_egress_octets,
        508
    );
    assert_eq!(cultivated.launches, 2);
    assert_eq!(cultivated.synchronizations, 1);
    assert_eq!(cultivated.typed_reductions, 1);
}

/// L2 rests the repeated dense action as one oriented relation `T=I+L*C`.  The equal present
/// zero sections remain in distinct carrier charts, and `[1,1,0]` is their first admitted
/// future separator: its integer residual is two while its F2 residual vanishes.
#[test]
#[ignore = "requires the RTX CUDA device"]
fn the_card_conducts_the_native_fixed_section_relation_and_reopens_the_carrier_fibre() {
    let mut card = CudaRefineExecutor::new().expect("the card mounts");
    let cultivated = card
        .conduct_native_fixed_section_families_on_device(
            &[11, -11, 0, 1, 1, 0],
            &[1, 1, -1],
            &[-1, -1, 1],
            &[0, 2],
            &[1, 1],
        )
        .expect("the native family returns");
    assert_eq!(cultivated.constraint_residuals, vec![0, 0]);
    assert_eq!(cultivated.selected_route, vec![1, 1]);
    assert!(cultivated.joint_cultivated);
    assert_eq!(cultivated.local_ablated_joint, vec![0, 0]);
    assert_eq!(cultivated.semantic_work, 10);
    assert_eq!(cultivated.semantic_span, 4);
    assert_eq!(cultivated.predicted_local_semantic_work, vec![2, 5, 2, 5]);
    assert_eq!(cultivated.predicted_local_semantic_span, vec![2, 3, 2, 3]);
    assert_eq!(
        cultivated.host_ingress_octets + cultivated.host_egress_octets,
        234
    );

    let reopened = card
        .conduct_native_fixed_section_families_on_device(
            &[1, 1, 0, 1, 1, 0],
            &[1, 1, -1],
            &[-1, -1, 1],
            &[0, 2],
            &[1, 1],
        )
        .expect("the carrier separator returns");
    assert_eq!(reopened.constraint_residuals, vec![2, 0]);
    assert_eq!(reopened.transported_sections, vec![-1, -1, 2, 1, 1, 0]);
    assert_eq!(reopened.selected_route, vec![2, 1]);
    assert!(!reopened.joint_cultivated);
    assert_eq!(reopened.semantic_work, 13);
    assert_eq!(reopened.semantic_span, 5);
}

/// I5's composed front: recurrence and conserved text/vision faces are selected by one
/// resident decision without a host semantic bridge.
#[test]
#[ignore = "requires the RTX CUDA device"]
fn the_card_returns_one_committed_inference_ecology() {
    let mut card = CudaRefineExecutor::new().expect("the card mounts");
    let returned = card
        .conduct_inference_ecology_on_device(
            &[1, 2, 2],
            &[0, 1],
            2,
            1,
            &[1, 1],
            &[0, 1, 2, 3, 4, 5, 6, 7],
            &[0, 0, 0, 0],
            2,
            2,
            true,
        )
        .expect("the inference ecology closes");
    assert_eq!(returned.trace_stride, 4);
    assert_eq!(&returned.selected_trace[..4], &[0, 1, 2, 2]);
    assert_eq!(returned.selected_lengths, returned.successor_lengths);
    assert_eq!(returned.selected_consequence, vec![1, 3, 5, 7]);
    assert_eq!(returned.shared_ablated_consequence, vec![0, 2, 4, 6]);
    assert_eq!(returned.launches, 1);
    assert_eq!(returned.synchronizations, 1);
}

/// R1's full pullback: two material branches retain equal-payload quotient faces, exact
/// contacts, their own M1 event lineage, and every I5 first future under one resident return.
#[test]
#[ignore = "requires the RTX CUDA device"]
fn the_card_returns_the_material_operation_world_tube_without_selecting_a_branch() {
    let mut card = CudaRefineExecutor::new().expect("the card mounts");
    let returned = card
        .conduct_material_operation_world_tube_on_device(
            &[[1, 1, 1, 1], [2, 2, 2, 2], [1, 1, 1, 1], [3, 3, 3, 3]],
            &[0, 0, 1, 1],
            &[10, 20],
            &[11, 21],
            &[0, 1],
            &[2, 3],
            &[7, 8],
            &[1, 2, 2],
            &[0, 1],
            2,
            1,
            &[1, 1],
            &[0, 1, 2, 3, 4, 5, 6, 7],
            &[0, 0, 0, 0],
            2,
            2,
            true,
        )
        .expect("the material-operation world-tube closes");
    assert_eq!(returned.payload_classes, vec![1, 2, 1, 4]);
    assert_eq!(returned.payload_comparisons, vec![1, 2, 1, 4]);
    assert_eq!(returned.contact_left_classes, vec![1, 2]);
    assert_eq!(returned.contact_right_classes, vec![1, 4]);
    assert_eq!(returned.contact_relations, vec![7, 8]);
    assert_eq!(returned.face_staging_events, vec![10, 10, 20, 20]);
    assert_eq!(returned.face_terminal_events, vec![11, 11, 21, 21]);
    assert_eq!(returned.recurrence_staging_events, vec![10, 10, 20, 20]);
    assert_eq!(returned.recurrence_terminal_events, vec![11, 11, 21, 21]);
    assert_eq!(returned.inference.families, 4);
    assert_eq!(returned.inference.selected_lengths.len(), 4);
    assert_eq!(returned.inference.selected_consequence.len(), 8);
    assert_eq!(returned.launches, 1);
    assert_eq!(returned.synchronizations, 1);
}
