use super::super::*;

/// **The law is one law.** The cpu and the card must return the same partition for the same
/// `(classes, keys)`, on material built to make the table collide and to make many cells share
/// a pair — which is where a claim race shows up and where a wrong probe walks off.
///
/// `#[ignore]`d because it requires the mounted card; run with `-- --ignored`.
#[test]
#[ignore = "requires the RTX CUDA device"]
fn the_quotient_is_one_law_on_both_charts() {
    let mut card = CudaRefineExecutor::new().expect("the card mounts");
    // Deterministic material with heavy sharing: many cells per pair, several classes, and keys
    // chosen so distinct pairs land near each other under any probe.
    for cells in [1usize, 2, 31, 32, 33, 1024, 40_000] {
        let classes: Vec<u32> = (0..cells).map(|at| (at % 7) as u32 + 1).collect();
        let keys: Vec<u64> = (0..cells)
            .map(|at| ((at % 11) as u64) << 32 | (at % 5) as u64)
            .collect();
        let cpu = quotient_on_cpu(&classes, &keys);
        let device = card
            .quotient_on_device(&classes, &keys)
            .expect("the card quotients");
        assert_eq!(
            cpu.classes, device.classes,
            "class count at {cells} cells: cpu {} device {}",
            cpu.classes, device.classes
        );
        assert!(
            cpu.same_partition_as(&device),
            "the two charts must induce the same equivalence at {cells} cells"
        );
        assert_eq!(cpu.carrier, QuotientCarrier::Cpu);
        assert_eq!(device.carrier, QuotientCarrier::Device);
    }
}

/// Mounting separates invariant transport ingress from later addressed-state ingress.
#[test]
#[ignore = "requires the RTX CUDA device"]
fn the_resident_native_word_is_not_reuploaded_between_successors() {
    let card = CudaRefineExecutor::new().expect("the card mounts");
    // One generator carries the two hands through three boundaries and then rests.
    let table = [2, 3, 4, 5, 4, 5];
    let mut word = ResidentNativeWord::mount(card, 6, 1, &table, &[0, 0])
        .expect("the native word mounts once");
    assert_eq!(word.mount_host_ingress_octets(), 32);
    let first = word.conduct(&[0, 1]).expect("the first successor returns");
    let second = word.conduct(&[1]).expect("the later successor returns");
    assert_eq!(first.native_end, vec![4, 5]);
    assert_eq!(second.native_end, vec![5]);
    assert_eq!(first.host_ingress_octets, 8);
    assert_eq!(second.host_ingress_octets, 4);
    assert!(!first.invariant_transport_reuploaded);
    assert!(!second.invariant_transport_reuploaded);
    assert_eq!(
        first.resident_invariant_octets,
        second.resident_invariant_octets
    );
}

/// The pre-quotient receiver keeps both phase coordinates and mounts its incidence only once.
#[test]
#[ignore = "requires the RTX CUDA device"]
fn the_resident_complex_incidence_carries_phase_without_binary_collapse() {
    let card = CudaRefineExecutor::new().expect("the card mounts");
    let mut incidence =
        ResidentComplexIncidence::mount(card, "test/incidence", 0, 3, 2, &[1, 0, 2, 1, 0, 3])
            .expect("incidence mounts");
    let current = vec![
        ExactComplexWaveCurrent::one(),
        ExactComplexWaveCurrent::new(Rat::zero(), Rat::one()),
    ];
    let half_turn = current
        .iter()
        .map(ExactComplexWaveCurrent::negated)
        .collect::<Vec<_>>();
    let first = incidence
        .conduct(&[current.clone(), half_turn])
        .expect("complex fronts return");
    let later = incidence
        .conduct(&[current])
        .expect("later current returns");
    assert_eq!(
        first.sections[1],
        first.sections[0]
            .iter()
            .map(ExactComplexWaveCurrent::negated)
            .collect::<Vec<_>>()
    );
    assert_eq!(later.sections[0], first.sections[0]);
    assert_eq!(first.launches, 1);
    assert_eq!(later.launches, 1);
    assert!(!first.binary_receiver_taken);
    assert!(!first.invariant_transport_reuploaded);
    assert!(!later.invariant_transport_reuploaded);
    assert_eq!(
        first.resident_invariant_octets,
        later.resident_invariant_octets
    );
}

#[test]
#[ignore = "requires the RTX CUDA device"]
fn addressed_complex_junction_joins_before_the_positive_receiver() {
    let card = CudaRefineExecutor::new().expect("the card mounts");
    let mut resident = ResidentMembraneInteriorWord::mount(
        card,
        &[1],
        &[0, 1],
        &[0],
        &[1],
        &[1],
        &[1],
        &[ExactComplexWaveCurrent::one()],
    )
    .expect("the membrane context mounts");
    let current = |real: i64, imaginary: i64| {
        ExactComplexWaveCurrent::new(
            Rat::from_integer(BigInt::from(real)),
            Rat::from_integer(BigInt::from(imaginary)),
        )
    };
    let returned = resident
        .conduct_addressed_complex_junction(&[
            ResidentAddressedComplexJunctionTerm {
                occurrence: 0,
                target_site: 3,
                exterior_port: 7,
                factor: 0,
                current: current(1, 0),
            },
            ResidentAddressedComplexJunctionTerm {
                occurrence: 1,
                target_site: 5,
                exterior_port: 7,
                factor: 0,
                current: current(-1, 0),
            },
            ResidentAddressedComplexJunctionTerm {
                occurrence: 2,
                target_site: 3,
                exterior_port: 8,
                factor: 0,
                current: current(1, 2),
            },
            ResidentAddressedComplexJunctionTerm {
                occurrence: 3,
                target_site: 5,
                exterior_port: 8,
                factor: 0,
                current: current(2, -1),
            },
        ])
        .expect("the resident junction returns");
    assert_eq!(returned.groups.len(), 2);
    assert_eq!(returned.groups[0].exterior_port, 7);
    assert!(returned.groups[0].joined_current.is_zero());
    assert!(returned.groups[0].positive_numerator.is_zero());
    assert_eq!(returned.groups[1].exterior_port, 8);
    assert_eq!(returned.groups[1].joined_current, current(3, 1));
    assert_eq!(returned.groups[1].positive_numerator, BigUint::from(10_u8));
    assert_eq!(
        returned.groups[1].target_sections,
        vec![(3, vec![2]), (5, vec![3])]
    );
    assert_eq!(returned.positive_denominator, BigUint::from(1_u8));
    assert_eq!(returned.launches, 1);
    assert_eq!(returned.synchronizations, 1);
    assert_eq!(returned.intermediate_semantic_egress_octets, 0);
    assert!(!returned.invariant_transport_reuploaded);
    assert!(!returned.cpu_semantic_replay_after_device);
    let mut replayed = returned.clone();
    replayed.record_post_device_cpu_semantic_step();
    assert!(replayed.cpu_semantic_replay_after_device);
}

/// The exact causal-adjoint receipt derives its own finite population and refuses a ragged
/// substitute before any card is mounted.
#[test]
fn causal_adjoint_pulled_incidence_has_no_authored_width() {
    let receipt = CausalAdjointPulledIncidence::found(vec![vec![5, 0], vec![0, 5]])
        .expect("returned covectors found the population");
    assert_eq!(receipt.factors(), 2);
    assert_eq!(receipt.nodes(), 2);
    assert!(matches!(
        CausalAdjointPulledIncidence::found(vec![vec![5], vec![0, 5]]),
        Err(CudaRefineError::CoupledComplexParametronShape)
    ));
}

/// Primary causal-adjoint current and its mixed finite-Leibniz remainder stay in one mounted
/// body.  Withdrawing factor zero removes both its own row and every mixed contact incident
/// to it, while the other row remains productive without host replay.
#[test]
#[ignore = "requires the RTX CUDA device"]
fn the_coupled_parametron_withdraws_incident_mixed_current_on_card() {
    let card = CudaRefineExecutor::new().expect("the card mounts");
    let receipt = CausalAdjointPulledIncidence::found(vec![vec![5, 0], vec![0, 5]])
        .expect("returned covectors found");
    let interactions = vec![
        CoupledComplexInteraction {
            output_factor: 0,
            left_factor: 0,
            right_factor: 1,
            contribution: ExactComplexWaveCurrent::new(Rat::zero(), Rat::one()),
        },
        CoupledComplexInteraction {
            output_factor: 1,
            left_factor: 1,
            right_factor: 0,
            contribution: ExactComplexWaveCurrent::new(
                Rat::zero(),
                Rat::from_integer(BigInt::from(-1)),
            ),
        },
    ];
    let front = vec![
        ExactComplexWaveCurrent::one(),
        ExactComplexWaveCurrent::new(Rat::zero(), Rat::one()),
    ];
    let mut resident = ResidentCoupledComplexParametron::mount(
        card,
        "test/causal-adjoint-pulled",
        receipt,
        front,
        interactions,
    )
    .expect("coupled body mounts once");
    let complete = resident
        .conduct(&[true, true])
        .expect("complete coupled current returns");
    assert_eq!(
        complete.sections,
        vec![
            ExactComplexWaveCurrent::new(Rat::from_integer(BigInt::from(5)), Rat::one(),),
            ExactComplexWaveCurrent::new(Rat::zero(), Rat::from_integer(BigInt::from(4)),),
        ]
    );
    let withdrawn = resident
        .conduct(&[false, true])
        .expect("factor withdrawal returns");
    assert!(withdrawn.sections[0].is_zero());
    assert_eq!(
        withdrawn.sections[1],
        ExactComplexWaveCurrent::new(Rat::zero(), Rat::from_integer(BigInt::from(5)))
    );
    assert!(!complete.invariant_transport_reuploaded);
    assert!(!withdrawn.cpu_semantic_replay_after_device);
    assert!(!withdrawn.binary_receiver_taken);
    assert_eq!(complete.mixed_interaction_count, 2);
}

#[test]
fn the_coupled_limb_chart_derives_only_the_carry_width_the_exact_sum_requires() {
    let receipt = CausalAdjointPulledIncidence::found(vec![vec![1]])
        .expect("one returned covector founds one factor");
    let large = BigInt::one() << 130usize;
    let interaction = CoupledComplexInteraction {
        output_factor: 0,
        left_factor: 0,
        right_factor: 0,
        contribution: ExactComplexWaveCurrent::new(
            Rat::from_integer(large.clone()),
            Rat::from_integer(-large),
        ),
    };
    let chart =
        derive_coupled_limb_chart(&receipt, &[ExactComplexWaveCurrent::one()], &[interaction])
            .expect("the exact multi-limb chart is derived");
    assert_eq!(chart.limb_count, 5, "2^130 plus one needs five u32 limbs");
    assert_eq!(chart.denominator, BigInt::one());
    assert_eq!(chart.mixed_real_limbs.len(), chart.limb_count);
    assert_eq!(chart.mixed_imaginary_limbs.len(), chart.limb_count);
}

#[test]
#[ignore = "requires the RTX CUDA device"]
fn the_integrated_athena_front_keeps_three_leaf_laws_on_one_context() {
    let card = CudaRefineExecutor::new().expect("the card mounts once");
    let integrated = ResidentIntegratedFront::mount(
        card,
        "test/integrated-athena",
        CausalAdjointPulledIncidence::found(vec![vec![1, 0], vec![0, 1]])
            .expect("returned covectors found"),
        vec![
            ExactComplexWaveCurrent::one(),
            ExactComplexWaveCurrent::new(Rat::zero(), Rat::one()),
        ],
        vec![CoupledComplexInteraction {
            output_factor: 0,
            left_factor: 0,
            right_factor: 1,
            contribution: ExactComplexWaveCurrent::new(Rat::zero(), Rat::one()),
        }],
        &[1, 0],
        &[1, 0],
        &[0, 0],
        &[1, 0],
        &[1, 1],
        &[1, 1],
        &[1, 2],
        &[0, 1, 2],
        &[1, 1],
        &[1, 1],
        &[1, 1],
    )
    .expect("all three resident leaves mount on one card");
    let mut integrated = integrated;
    let returned = integrated
        .conduct(&[true, true], &[1, 1], 0)
        .expect("the fixed resident word returns");
    assert!(returned.one_underlying_context);
    assert_ne!(returned.context_identity, 0);
    assert_eq!(returned.launches, 3);
    assert_eq!(returned.synchronizations, 1);
    assert_eq!(returned.intermediate_host_egress_octets, 0);
    assert_eq!(returned.coupled.synchronizations, 0);
    assert_eq!(returned.affine.synchronizations, 0);
    assert_eq!(returned.participant.synchronizations, 0);
    assert!(!returned.invariant_transport_reuploaded);
    assert!(!returned.cpu_semantic_replay_after_device);
}

#[test]
#[ignore = "requires the RTX CUDA device"]
fn recurrent_factor_support_crosses_the_resident_membrane_without_affine_normalization() {
    let card = CudaRefineExecutor::new().expect("the card mounts");
    let mut resident = ResidentMembraneInteriorWord::mount(
        card,
        &[2, 3],
        &[0, 1, 2],
        &[0, 1],
        &[1, 1],
        &[1, 1],
        &[1, -1],
        &[ExactComplexWaveCurrent::new(
            Rat::from_integer(BigInt::from(2)),
            Rat::zero(),
        )],
    )
    .expect("the exact membrane constitution mounts");
    let returned = resident
        .conduct_factor_support(&[0, 1], &[0], 3)
        .expect("the recurrent support returns");
    assert_eq!(
        returned.family_overlaps,
        vec![Rat::from_integer(BigInt::from(6))]
    );
    assert_eq!(
        returned.returned_response,
        ExactComplexWaveCurrent::new(Rat::from_integer(BigInt::from(12)), Rat::zero())
    );
    assert_eq!(returned.launches, 3);
    assert_eq!(returned.device_dependency_edges, 2);
    assert_eq!(returned.synchronizations, 1);
    assert_eq!(returned.intermediate_host_egress_octets, 0);
    assert!(!returned.invariant_transport_reuploaded);
    assert!(!returned.cpu_semantic_replay_after_device);
    let weighted = resident
        .conduct_factor_current(&[(0, 2), (1, 1)], &[0], 3)
        .expect("the reflected path current returns");
    assert_eq!(weighted.context_factor_currents, vec![(0, 2), (1, 1)]);
    assert_eq!(
        weighted.family_overlaps,
        vec![Rat::from_integer(BigInt::from(12))]
    );
    assert_eq!(
        weighted.returned_response,
        ExactComplexWaveCurrent::new(Rat::from_integer(BigInt::from(24)), Rat::zero())
    );
    assert_ne!(weighted.returned_response, returned.returned_response);
}

#[test]
#[ignore = "requires the RTX CUDA device"]
fn observable_integral_form_frame_contracts_and_descends_on_the_resident_card() {
    use crate::receiver_history_compression::{
        ObservableIntegralFormFrame, SparseIntegralBilinearForm,
    };

    let present =
        SparseIntegralBilinearForm::new(3, [((0, 0), BigInt::from(2))]).expect("present form");
    let frame = ObservableIntegralFormFrame::found(vec![present], vec![vec![0, 0, 1]])
        .expect("closed integral form frame");
    let card = CudaRefineExecutor::new().expect("the card mounts");
    let mut resident = ResidentMembraneInteriorWord::mount(
        card,
        &[1, 1, 1],
        &[0, 1, 2, 3],
        &[0, 1, 2],
        &[1, 1, 1],
        &[1, 1, 1],
        &[1, 1, 1],
        &[ExactComplexWaveCurrent::one()],
    )
    .expect("the membrane constitution mounts");
    resident
        .mount_observable_integral_form_frame(&frame)
        .expect("the observable frame mounts once");
    let contexts = [AddressedCurrentSection {
        boundary_state: None,
        quadratic_weight: BigUint::from(1_u8),
        factor_current: vec![
            (0, BigUint::from(1_u8)),
            (1, BigUint::from(2_u8)),
            (2, BigUint::from(3_u8)),
        ],
    }];
    let returned = resident
        .conduct_observable_integral_form_frame(&contexts, 0)
        .expect("the observable section returns");
    assert_eq!(returned.coordinates, [1, 9, 36].map(BigInt::from));
    assert_eq!(returned.present_receivers, vec![BigInt::from(2)]);
    assert_eq!(
        returned.transported_coordinates,
        [9, 36, 36].map(BigInt::from)
    );
    assert_eq!(returned.launches, 3);
    assert_eq!(returned.synchronizations, 1);
    assert!(!returned.invariant_transport_reuploaded);
    assert!(!returned.cpu_semantic_replay_after_device);
}
