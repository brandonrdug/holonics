use super::super::*;

/// A non-injective plural generator front is carried as exact arbitrary-width current on the
/// card.  Equal transported rows condense once, their quadratic weights add, and every
/// `(source, generator)` incidence remains in the returned reconstruction fibre.

#[test]
#[ignore = "requires the RTX CUDA device"]
fn factored_current_transport_condenses_equal_rows_and_retains_the_complete_fibre() {
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
    .expect("the exact membrane constitution mounts");
    resident
        .mount_factor_receiver_faces(&[0], &[0, 0, 0])
        .expect("the receiver face mounts once");
    resident
        .mount_boundary_restriction_atlas(&ResidentBoundaryRestrictionAtlas {
            state_count: 1,
            universal_port_count: 1,
            state_port_transition: vec![0],
            transition_targets: vec![0],
            transition_factor_offsets: vec![0, 1],
            transition_factors: vec![0],
            transition_currents: vec![BigUint::from(1_u8)],
        })
        .expect("the restriction atlas mounts once");
    let wide = (BigUint::from(1_u8) << 97usize) + BigUint::from(3_u8);
    let contexts = vec![
        AddressedCurrentSection {
            boundary_state: None,
            quadratic_weight: BigUint::from(2_u8),
            factor_current: vec![
                (0, wide.clone()),
                (1, BigUint::from(1_u8)),
                (2, BigUint::from(4_u8)),
            ],
        },
        AddressedCurrentSection {
            boundary_state: None,
            quadratic_weight: BigUint::from(5_u8),
            factor_current: vec![
                (0, BigUint::from(1_u8)),
                (1, wide.clone()),
                (2, BigUint::from(4_u8)),
            ],
        },
    ];
    let returned = resident
        .mount_addressed_current_passage(&contexts, &[0, 0, 2, 1, 1, 2], 2)
        .expect("the resident factored passage returns");
    let combined = wide + BigUint::from(1_u8);
    assert_eq!(
        returned.passage.target,
        vec![
            AddressedCurrentSection {
                boundary_state: None,
                quadratic_weight: BigUint::from(7_u8),
                factor_current: vec![(0, combined.clone()), (2, BigUint::from(4_u8)),],
            },
            AddressedCurrentSection {
                boundary_state: None,
                quadratic_weight: BigUint::from(7_u8),
                factor_current: vec![(1, combined), (2, BigUint::from(4_u8))],
            },
        ]
    );
    assert_eq!(
        returned.passage.occurrences,
        vec![
            AddressedCurrentOccurrence {
                source_section: 0,
                generator: 0,
                target_section: 0,
            },
            AddressedCurrentOccurrence {
                source_section: 0,
                generator: 1,
                target_section: 1,
            },
            AddressedCurrentOccurrence {
                source_section: 1,
                generator: 0,
                target_section: 0,
            },
            AddressedCurrentOccurrence {
                source_section: 1,
                generator: 1,
                target_section: 1,
            },
        ]
    );
    assert_eq!(returned.passage.source.len(), 2);
    assert_eq!(returned.passage.occurrences.len(), 4);
    assert_eq!(returned.passage.target.len(), 2);
    assert_eq!(returned.launches, 3);
    assert_eq!(returned.synchronizations, 1);
    assert_eq!(returned.intermediate_host_egress_octets, 0);
    assert!(returned.source_current_mounted_this_pass);
    assert!(!returned.invariant_transport_reuploaded);
    assert!(!returned.cpu_semantic_replay_after_device);
    let later_source = returned.passage.target.clone();
    let later = resident
        .continue_addressed_current_passage(
            &returned.target_address,
            &later_source,
            &[0, 0, 2, 1, 1, 2],
            2,
        )
        .expect("the resident target becomes the later source");
    assert_eq!(later.passage.target.len(), 2);
    assert!(
        later
            .passage
            .target
            .iter()
            .all(|context| context.quadratic_weight == BigUint::from(14_u8))
    );
    assert_eq!(later.source_address, returned.target_address);
    assert_eq!(later.host_ingress_octets, 0);
    assert!(!later.source_current_mounted_this_pass);
    assert!(!later.invariant_transport_reuploaded);
}

#[test]
#[ignore = "requires the RTX CUDA device"]
fn factored_moment_foundation_and_factor_leg_transport_remain_resident() {
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
    .expect("the exact membrane constitution mounts");
    resident
        .mount_factor_receiver_faces(&[0], &[0, 0, 0])
        .expect("the receiver face mounts once");
    resident
        .mount_boundary_restriction_atlas(&ResidentBoundaryRestrictionAtlas {
            state_count: 1,
            universal_port_count: 1,
            state_port_transition: vec![0],
            transition_targets: vec![0],
            transition_factor_offsets: vec![0, 1],
            transition_factors: vec![0],
            transition_currents: vec![BigUint::from(1_u8)],
        })
        .expect("the restriction atlas mounts once");
    let contexts = vec![
        AddressedCurrentSection {
            boundary_state: None,
            quadratic_weight: BigUint::from(2_u8),
            factor_current: vec![(0, BigUint::from(1_u8)), (1, BigUint::from(2_u8))],
        },
        AddressedCurrentSection {
            boundary_state: None,
            quadratic_weight: BigUint::from(3_u8),
            factor_current: vec![(1, BigUint::from(1_u8)), (2, BigUint::from(1_u8))],
        },
    ];
    let returned = resident
        .mount_factored_moment_foundation(&contexts, &[0, 0, 2, 1, 1, 2], 2)
        .expect("the exact image section mounts");
    assert_eq!(returned.foundation.source_population, 2);
    assert_eq!(returned.foundation.reconstruction_fibre.len(), 2);
    assert_eq!(returned.target_address.generation, 0);
    assert_eq!(returned.target_address.factor_population, 3);
    assert_eq!(
        returned.target_address.image_population,
        returned.foundation.section.image_rank
    );
    assert!(!returned.source_current_retained_hot);
    assert!(!returned.ambient_covariance_materialized);
    assert!(returned.host_ingress_octets > 0);
    assert_eq!(returned.host_ingress_octets, returned.resident_octets);
    resident
        .validate_resident_factored_moment_address(&returned.target_address)
        .expect("the returned image address names the resident occurrence");
    let mounted = resident
        .factored_receiver_history
        .as_ref()
        .expect("the operation complex stands");
    assert!(mounted.current.is_none());
    assert!(mounted.image.is_some());
    let generators = [vec![0_u32, 0, 2], vec![1_u32, 1, 2]];
    let transport_address = resident
        .stage_resident_factored_moment_transport(
            &returned.target_address,
            &generators.iter().flatten().copied().collect::<Vec<_>>(),
            generators.len() as u32,
        )
        .expect("the resident image incidence crosses the plural generator front");
    let rank_address = resident
        .stage_resident_factored_moment_rank(&transport_address)
        .expect("the sufficient finite-chart rank atlas remains resident");
    let coordinate_address = resident
        .stage_resident_factored_moment_coordinates(&rank_address)
        .expect("the complete signed coordinate fibre remains resident");
    let descent_address = resident
        .stage_resident_factored_moment_descent(&coordinate_address)
        .expect("both exact squares stage one guarded target image");
    let rank_return = resident
        .inspect_resident_factored_moment_rank(&rank_address)
        .expect("the terminal rank observer returns the exact image witness");
    let coordinate_return = resident
        .inspect_resident_factored_moment_coordinates(&coordinate_address)
        .expect("the terminal coordinate observer returns the exact signed fibre");
    let descent_return = resident
        .inspect_resident_factored_moment_descent(&descent_address)
        .expect("the terminal descent observer returns the device-admitted target");
    let transported = resident
        .inspect_resident_factored_moment_transport(&transport_address)
        .expect("the terminal construction observer returns the transported incidence");
    let source_rows = returned.foundation.section.incidence.to_rows();
    let expected = ExactRatMatrix::new(
        generators
            .iter()
            .flat_map(|generator| {
                source_rows.iter().map(|source_row| {
                    let mut target = vec![Rat::zero(); 3];
                    for (source, target_factor) in generator.iter().copied().enumerate() {
                        target[target_factor as usize] += source_row[source].clone();
                    }
                    target
                })
            })
            .collect(),
    )
    .expect("the cold equality witness has one exact matrix shape");
    let direct_passage = returned
        .foundation
        .section
        .transport_direct_sum(&generators)
        .expect("the apparatus-neutral image passage returns");
    assert_eq!(rank_return.exact_rank, direct_passage.target.image_rank);
    assert_eq!(
        rank_return.basis_rows.len(),
        rank_return.exact_rank as usize
    );
    assert_eq!(
        rank_return.basis_factors.len(),
        rank_return.exact_rank as usize
    );
    assert_eq!(rank_return.primes.len(), 1);
    assert!(rank_return.chart_product > BigUint::one());
    assert_eq!(
        rank_return.modular_ranks.iter().copied().max(),
        Some(rank_return.exact_rank)
    );
    assert!(!rank_return.host_selected_rank_or_pivot);
    assert!(!rank_return.probabilistic_rank);
    assert_eq!(rank_return.intermediate_host_egress_octets, 0);
    let determinant = Rat::from_integer(coordinate_return.determinant.clone());
    let reconstructed_joining = ExactRatMatrix::new(
        coordinate_return
            .joining_numerator
            .to_rows()
            .into_iter()
            .map(|row| row.into_iter().map(|entry| entry / &determinant).collect())
            .collect(),
    )
    .expect("the joining denominator is nonzero");
    let expected_rows = expected.to_rows();
    let reconstructed_incidence = ExactRatMatrix::new(
        rank_return
            .basis_rows
            .iter()
            .map(|row| expected_rows[*row as usize].clone())
            .collect(),
    )
    .expect("the selected addressed rows form one exact target image");
    assert_eq!(
        reconstructed_joining
            .multiply(&reconstructed_incidence)
            .expect("the joining square composes"),
        expected
    );
    let source_constitutive_denominator = returned
        .foundation
        .section
        .constitutive
        .entries()
        .iter()
        .fold(BigInt::one(), |held, entry| {
            lcm_positive(held, entry.denom())
        });
    let target_denominator = Rat::from_integer(
        source_constitutive_denominator
            * &coordinate_return.determinant
            * &coordinate_return.determinant,
    );
    let reconstructed_constitutive = ExactRatMatrix::new(
        coordinate_return
            .constitutive_numerator
            .to_rows()
            .into_iter()
            .map(|row| {
                row.into_iter()
                    .map(|entry| entry / &target_denominator)
                    .collect()
            })
            .collect(),
    )
    .expect("the target constitutive denominator is nonzero");
    let reconstructed_target = FactoredMomentSection {
        schema: "holonic-engine.factored-moment-section.v2".to_owned(),
        factor_population: 3,
        image_rank: rank_return.exact_rank,
        basis_factors: rank_return.basis_factors.clone(),
        incidence: reconstructed_incidence,
        constitutive: reconstructed_constitutive,
    };
    reconstructed_target
        .validate_admitted()
        .expect("the device-selected image chart is exact and full rank");
    for left in 0..3 {
        for right in 0..3 {
            assert_eq!(
                reconstructed_target
                    .reconstruct_entry(left, right)
                    .expect("the device target returns one ambient receiver"),
                direct_passage
                    .target
                    .reconstruct_entry(left, right)
                    .expect("the direct target returns the same receiver")
            );
        }
    }
    assert_eq!(coordinate_return.address, coordinate_address);
    assert!(coordinate_return.good_chart_population > 0);
    assert!(!coordinate_return.host_crt_reconstruction);
    assert!(!coordinate_return.host_selected_coordinate_chart);
    assert_eq!(coordinate_return.intermediate_host_egress_octets, 0);
    assert_eq!(descent_return.address, descent_address);
    assert!(descent_return.admitted);
    assert!(
        descent_return
            .chart_witnesses
            .iter()
            .all(|witness| *witness == 1)
    );
    assert_eq!(descent_return.intermediate_host_egress_octets, 0);
    assert!(!descent_return.host_rational_continuation);
    assert!(!descent_return.source_replaced_before_device_admission);
    assert_eq!(
        descent_return
            .joining_map
            .multiply(&descent_return.target.incidence)
            .expect("the resident joining square composes"),
        expected
    );
    for left in 0..3 {
        for right in 0..3 {
            assert_eq!(
                descent_return
                    .target
                    .reconstruct_entry(left, right)
                    .expect("the staged target returns one ambient receiver"),
                direct_passage
                    .target
                    .reconstruct_entry(left, right)
                    .expect("the cold target returns the same exact receiver")
            );
        }
    }
    assert_eq!(transported.transported_incidence, expected);
    assert_eq!(transported.source_address, returned.target_address);
    assert_eq!(transported.occurrences.len(), 4);
    assert_eq!(transported.generator_targets, generators);
    assert_eq!(transported.launches, 1);
    assert_eq!(transported.synchronizations, 1);
    assert_eq!(transported.successor_host_ingress_octets, 0);
    assert_eq!(transported.intermediate_host_egress_octets, 0);
    assert!(!transported.invariant_transport_reuploaded);
    assert!(!transported.cpu_semantic_replay_after_device);
}

#[test]
#[ignore = "requires the RTX CUDA device"]
fn diagonal_chronology_foundation_equals_the_exact_suffix_recurrence_on_card() {
    use crate::factored_moment::SparseQuadraticMomentSection;

    let generators = vec![vec![0_u32, 0, 2], vec![1_u32, 1, 2]];
    let chronology = vec![
        AddressedDiagonalCurrentStep {
            source_state: 0,
            target_state: 1,
            entries: vec![(0, BigUint::from(2_u8)), (1, BigUint::from(1_u8))],
        },
        AddressedDiagonalCurrentStep {
            source_state: 1,
            target_state: 1,
            entries: vec![(1, BigUint::from(3_u8)), (2, BigUint::from(1_u8))],
        },
        AddressedDiagonalCurrentStep {
            source_state: 1,
            target_state: 0,
            entries: vec![(0, BigUint::from(1_u8)), (2, BigUint::from(2_u8))],
        },
    ];
    let action = SparseQuadraticMomentAction::complete_symmetric(3, generators.clone())
        .expect("the complete pair carrier is derived");
    let expected = SparseQuadraticMomentSection::from_diagonal_chronology(&action, &chronology)
        .expect("the apparatus-neutral chronology returns");

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
    .expect("the exact membrane constitution mounts");
    resident
        .mount_factor_receiver_faces(&[0], &[0, 0, 0])
        .expect("the receiver face mounts once");
    resident
        .mount_boundary_restriction_atlas(&ResidentBoundaryRestrictionAtlas {
            state_count: 2,
            universal_port_count: 1,
            state_port_transition: vec![0, 0],
            transition_targets: vec![0],
            transition_factor_offsets: vec![0, 1],
            transition_factors: vec![0],
            transition_currents: vec![BigUint::from(1_u8)],
        })
        .expect("the restriction atlas mounts once");
    let returned = resident
        .mount_sparse_quadratic_diagonal_chronology_foundation(
            &chronology,
            &generators.iter().flatten().copied().collect::<Vec<_>>(),
            generators.len() as u32,
        )
        .expect("the chronology founds one resident pair section");
    let state = resident
        .factored_receiver_history
        .as_ref()
        .and_then(|mount| mount.sparse_pair.as_ref())
        .expect("the pair section remains resident");
    let limb_count = state.coefficient_limb_count as usize;
    let mut wire = vec![0_u32; state.pair_population as usize * limb_count];
    state
        .coefficients
        .read(&mut wire)
        .expect("the exact test receiver reads the terminal section");
    let actual = wire
        .chunks_exact(limb_count)
        .map(|limbs| BigUint::new(limbs.to_vec()))
        .collect::<Vec<_>>();
    assert_eq!(actual, expected.coefficients);
    assert_eq!(returned.pair_population as usize, expected.pairs.len());
    assert_eq!(returned.chronology_reconstruction_fibre, chronology);
    assert!(!returned.source_current_retained_hot);
    assert!(!returned.ambient_covariance_materialized);
    assert_eq!(returned.terminal_synchronizations, 1);
}

#[test]
#[ignore = "requires the RTX CUDA device"]
fn factored_moment_descent_contracts_receivers_and_atomically_continues() {
    use crate::receiver_history_compression::{
        ObservableIntegralFormFrame, SparseIntegralBilinearForm,
    };

    let generators = vec![vec![0_u32, 0, 2], vec![1_u32, 1, 2]];
    let present = SparseIntegralBilinearForm::new(
        3,
        [
            ((0, 0), BigInt::from(1)),
            ((0, 1), BigInt::from(2)),
            ((2, 2), BigInt::from(-1)),
        ],
    )
    .expect("one exact present receiver");
    let frame = ObservableIntegralFormFrame::found(vec![present], generators.clone())
        .expect("the admitted generators close the primitive receiver family");
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
    .expect("the exact membrane constitution mounts");
    resident
        .mount_factor_receiver_faces(&[0], &[0, 0, 0])
        .expect("the receiver face mounts once");
    resident
        .mount_boundary_restriction_atlas(&ResidentBoundaryRestrictionAtlas {
            state_count: 1,
            universal_port_count: 1,
            state_port_transition: vec![0],
            transition_targets: vec![0],
            transition_factor_offsets: vec![0, 1],
            transition_factors: vec![0],
            transition_currents: vec![BigUint::from(1_u8)],
        })
        .expect("the restriction atlas mounts once");
    resident
        .mount_observable_integral_form_frame(&frame)
        .expect("the complete primitive receiver family mounts once");
    let contexts = vec![
        AddressedCurrentSection {
            boundary_state: None,
            quadratic_weight: BigUint::from(2_u8),
            factor_current: vec![(0, BigUint::from(1_u8)), (1, BigUint::from(2_u8))],
        },
        AddressedCurrentSection {
            boundary_state: None,
            quadratic_weight: BigUint::from(3_u8),
            factor_current: vec![(1, BigUint::from(1_u8)), (2, BigUint::from(1_u8))],
        },
    ];
    let foundation = resident
        .mount_factored_moment_foundation(
            &contexts,
            &generators.iter().flatten().copied().collect::<Vec<_>>(),
            generators.len() as u32,
        )
        .expect("the source image mounts once");
    let direct = foundation
        .foundation
        .section
        .transport_direct_sum(&generators)
        .expect("the apparatus-neutral target returns");
    let expected_receivers = frame
        .forms
        .iter()
        .map(|form| {
            form.entries.iter().try_fold(Rat::zero(), |sum, entry| {
                Ok::<Rat, crate::factored_moment::FactoredMomentError>(
                    sum + Rat::from_integer(entry.coefficient.clone())
                        * direct.target.reconstruct_entry(entry.row, entry.column)?,
                )
            })
        })
        .collect::<Result<Vec<_>, _>>()
        .expect("the cold receiver family contracts exactly");
    let transport = resident
        .stage_resident_factored_moment_transport(
            &foundation.target_address,
            &generators.iter().flatten().copied().collect::<Vec<_>>(),
            generators.len() as u32,
        )
        .expect("the plural incidence remains resident");
    let rank = resident
        .stage_resident_factored_moment_rank(&transport)
        .expect("the exact finite-chart rank remains resident");
    let coordinates = resident
        .stage_resident_factored_moment_coordinates(&rank)
        .expect("the signed reconstruction remains resident");
    let descent = resident
        .stage_resident_factored_moment_descent(&coordinates)
        .expect("the two exact squares admit one staged image");
    let receiver = resident
        .stage_resident_factored_moment_receivers(&descent)
        .expect("the mounted receiver family consumes the admitted image");
    let returned = resident
        .complete_resident_factored_moment_receivers(&receiver)
        .expect("the receiver return atomically advances the image");
    assert_eq!(returned.receiver_coordinates, expected_receivers);
    assert_eq!(returned.source_address, foundation.target_address);
    assert_eq!(returned.target_address.generation, 1);
    assert_eq!(
        returned.target_address.image_population,
        direct.target.image_rank
    );
    assert!(returned.atomic_image_replacement);
    assert!(returned.source_released_only_after_device_admission);
    assert!(!returned.ambient_factor_square_materialized);
    assert!(!returned.host_rational_continuation);
    assert_eq!(returned.intermediate_host_egress_octets, 0);
    assert_eq!(returned.apparatus_shape_host_egress_octets, 0);
    assert_eq!(returned.synchronizations, 1);
    resident
        .validate_resident_factored_moment_address(&returned.target_address)
        .expect("the admitted target is the sole continuing image");
    let mounted = resident
        .factored_receiver_history
        .as_ref()
        .expect("the operation complex continues");
    assert!(mounted.transported_image.is_none());
    assert_eq!(
        mounted.image.as_ref().map(|image| image.generation),
        Some(1)
    );
}

#[test]
#[ignore = "requires the RTX CUDA device"]
fn addressed_functional_pairs_contract_through_the_admitted_image() {
    use crate::receiver_history_compression::{
        AddressedFactoredIntegralReceiver, AddressedFactoredIntegralReceiverComplex,
        AddressedFactoredIntegralReceiverTerm, SparseIntegralFunctional,
    };

    let generators = vec![vec![0_u32, 0, 2], vec![1_u32, 1, 2]];
    let left = SparseIntegralFunctional::new(3, [(0, BigInt::from(1)), (1, BigInt::from(2))])
        .expect("the left functional is exact");
    let right = SparseIntegralFunctional::new(3, [(2, BigInt::from(-1))])
        .expect("the right functional is exact");
    let addressed_receiver = AddressedFactoredIntegralReceiver {
        terms: vec![
            AddressedFactoredIntegralReceiverTerm {
                coefficient: BigInt::from(2),
                left_functional: 0,
                right_functional: 1,
            },
            AddressedFactoredIntegralReceiverTerm {
                coefficient: BigInt::from(1),
                left_functional: 0,
                right_functional: 0,
            },
        ],
    };
    let receiver = AddressedFactoredIntegralReceiverComplex {
        schema: "holonic-engine.addressed-factored-integral-receiver-complex.v1".to_owned(),
        factor_population: 3,
        family_population: 1,
        receiver_population: 1,
        generator_population: 2,
        functionals: vec![left.clone(), right.clone()],
        receivers: vec![addressed_receiver; 4],
        reconstruction_fibre: vec![(0, BigUint::from(1_u8))],
    };
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
    .expect("the membrane mounts");
    resident
        .mount_factor_receiver_faces(&[0], &[0, 0, 0])
        .expect("the receiver axes mount");
    resident
        .mount_boundary_restriction_atlas(&ResidentBoundaryRestrictionAtlas {
            state_count: 1,
            universal_port_count: 1,
            state_port_transition: vec![0],
            transition_targets: vec![0],
            transition_factor_offsets: vec![0, 1],
            transition_factors: vec![0],
            transition_currents: vec![BigUint::from(1_u8)],
        })
        .expect("the restriction atlas mounts");
    let frame = resident
        .mount_addressed_factored_receiver_complexes(
            std::slice::from_ref(&receiver),
            &[0],
            &[BigUint::from(1_u8)],
            &[0],
        )
        .expect("the addressed functional pair crosses without an ambient square");
    assert_eq!(frame.functional_population, 2);
    assert_eq!(frame.receiver_population, 4);
    assert_eq!(frame.term_population, 8);
    assert!(!frame.ambient_factor_square_materialized);
    let contexts = vec![
        AddressedCurrentSection {
            boundary_state: None,
            quadratic_weight: BigUint::from(2_u8),
            factor_current: vec![(0, BigUint::from(1_u8)), (1, BigUint::from(2_u8))],
        },
        AddressedCurrentSection {
            boundary_state: None,
            quadratic_weight: BigUint::from(3_u8),
            factor_current: vec![(1, BigUint::from(1_u8)), (2, BigUint::from(1_u8))],
        },
    ];
    let generator_targets = generators.iter().flatten().copied().collect::<Vec<_>>();
    let foundation = resident
        .mount_factored_moment_foundation(&contexts, &generator_targets, 2)
        .expect("the source image mounts");
    let direct = foundation
        .foundation
        .section
        .transport_direct_sum(&generators)
        .expect("the direct target returns");
    let left_right = left.entries.iter().fold(Rat::zero(), |sum, left_entry| {
        right.entries.iter().fold(sum, |sum, right_entry| {
            sum + Rat::from_integer(&left_entry.coefficient * &right_entry.coefficient)
                * direct
                    .target
                    .reconstruct_entry(left_entry.factor, right_entry.factor)
                    .expect("the cross receiver returns")
        })
    });
    let left_left = left.entries.iter().fold(Rat::zero(), |sum, left_entry| {
        left.entries.iter().fold(sum, |sum, right_entry| {
            sum + Rat::from_integer(&left_entry.coefficient * &right_entry.coefficient)
                * direct
                    .target
                    .reconstruct_entry(left_entry.factor, right_entry.factor)
                    .expect("the self receiver returns")
        })
    });
    let expected = Rat::from_integer(BigInt::from(2)) * left_right + left_left;
    let transport = resident
        .stage_resident_factored_moment_transport(&foundation.target_address, &generator_targets, 2)
        .expect("the incidence transports");
    let rank = resident
        .stage_resident_factored_moment_rank(&transport)
        .expect("rank returns");
    let coordinates = resident
        .stage_resident_factored_moment_coordinates(&rank)
        .expect("coordinates return");
    let descent = resident
        .stage_resident_factored_moment_descent(&coordinates)
        .expect("the target is staged");
    let receiver_address = resident
        .stage_resident_factored_moment_addressed_receivers(&descent)
        .expect("functional pairs meet the target");
    let returned = resident
        .complete_resident_factored_moment_receivers(&receiver_address)
        .expect("the exact receiver admits the target");
    assert_eq!(returned.receiver_coordinates, vec![expected; 4]);
    assert!(returned.atomic_image_replacement);
    assert!(returned.source_released_only_after_device_admission);
    assert!(!returned.ambient_factor_square_materialized);
    assert!(!returned.host_rational_continuation);
    assert_eq!(returned.intermediate_host_egress_octets, 0);
    assert_eq!(
        returned.apparatus_shape_host_egress_octets,
        std::mem::size_of::<u32>() as u64
    );
    assert_eq!(returned.synchronizations, 2);

    let direct_second = direct
        .target
        .transport_direct_sum(&generators)
        .expect("the second direct target returns");
    let second_left_right = left.entries.iter().fold(Rat::zero(), |sum, left_entry| {
        right.entries.iter().fold(sum, |sum, right_entry| {
            sum + Rat::from_integer(&left_entry.coefficient * &right_entry.coefficient)
                * direct_second
                    .target
                    .reconstruct_entry(left_entry.factor, right_entry.factor)
                    .expect("the second cross receiver returns")
        })
    });
    let second_left_left = left.entries.iter().fold(Rat::zero(), |sum, left_entry| {
        left.entries.iter().fold(sum, |sum, right_entry| {
            sum + Rat::from_integer(&left_entry.coefficient * &right_entry.coefficient)
                * direct_second
                    .target
                    .reconstruct_entry(left_entry.factor, right_entry.factor)
                    .expect("the second self receiver returns")
        })
    });
    let expected_second = Rat::from_integer(BigInt::from(2)) * second_left_right + second_left_left;
    let second_transport = resident
        .stage_resident_factored_moment_transport(&returned.target_address, &generator_targets, 2)
        .expect("the rooted incidence transports again");
    let second_rank = resident
        .stage_resident_factored_moment_rank(&second_transport)
        .expect("the second rank returns");
    let second_coordinates = resident
        .stage_resident_factored_moment_coordinates(&second_rank)
        .expect("the second coordinates return");
    let second_descent = resident
        .stage_resident_factored_moment_descent(&second_coordinates)
        .expect("the second target is staged");
    let second_receiver = resident
        .stage_resident_factored_moment_addressed_receivers(&second_descent)
        .expect("the rooted functional pairs meet the second target");
    let second_return = resident
        .complete_resident_factored_moment_receivers(&second_receiver)
        .expect("the second exact receiver admits the target");
    assert_eq!(second_return.receiver_coordinates, vec![expected_second; 4]);
    assert_eq!(second_return.target_address.generation, 2);
    let continued = resident
        .factored_receiver_history
        .as_ref()
        .and_then(|mount| mount.image.as_ref())
        .and_then(|image| image.constitutive_spine.as_ref())
        .expect("the rooted productive spine continues");
    assert_eq!(
        continued.root_rank,
        foundation.foundation.section.image_rank
    );
    // Four presented ordered histories descend to the two complete incidence realizations
    // carried by these idempotent generators; multiplicity remains in the resident current.
    assert_eq!(continued.history_population, 2);
    assert!(continued.maximal_history_weight >= BigUint::from(2_u32));

    let direct_third = direct_second
        .target
        .transport_direct_sum(&generators)
        .expect("the third direct target returns");
    let third_left_right = left.entries.iter().fold(Rat::zero(), |sum, left_entry| {
        right.entries.iter().fold(sum, |sum, right_entry| {
            sum + Rat::from_integer(&left_entry.coefficient * &right_entry.coefficient)
                * direct_third
                    .target
                    .reconstruct_entry(left_entry.factor, right_entry.factor)
                    .expect("the third cross receiver returns")
        })
    });
    let third_left_left = left.entries.iter().fold(Rat::zero(), |sum, left_entry| {
        left.entries.iter().fold(sum, |sum, right_entry| {
            sum + Rat::from_integer(&left_entry.coefficient * &right_entry.coefficient)
                * direct_third
                    .target
                    .reconstruct_entry(left_entry.factor, right_entry.factor)
                    .expect("the third self receiver returns")
        })
    });
    let expected_third = Rat::from_integer(BigInt::from(2)) * third_left_right + third_left_left;
    let third_transport = resident
        .stage_resident_factored_constitutive_spine_transport(
            &second_return.target_address,
            &generator_targets,
            2,
        )
        .expect("the productive spine transports without a new compact square");
    let third_receiver = resident
        .stage_resident_factored_constitutive_spine_receivers(&third_transport)
        .expect("the receiver crosses the productive spine");
    let third_return = resident
        .complete_resident_factored_constitutive_spine_receivers(&third_receiver)
        .expect("the productive spine atomically continues");
    assert_eq!(third_return.receiver_coordinates, vec![expected_third; 4]);
    assert_eq!(third_return.target_address.generation, 3);
    let continued = resident
        .factored_receiver_history
        .as_ref()
        .and_then(|mount| mount.image.as_ref())
        .expect("the productive image continues");
    assert_eq!(continued.compact_generation, 2);
    assert_eq!(continued.generation, 3);
    assert_eq!(
        continued.productive_population,
        foundation.foundation.section.image_rank * 2
    );
    let spine = continued
        .constitutive_spine
        .as_ref()
        .expect("the descended rooted history remains resident");
    assert_eq!(spine.history_population, 2);
    assert!(spine.maximal_history_weight >= BigUint::from(4_u32));
}

#[test]
#[ignore = "requires the RTX CUDA device"]
fn complete_boundary_chain_returns_ports_and_storage_in_one_resident_word() {
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
    resident
        .mount_factor_receiver_faces(&[0], &[0, 1])
        .expect("the complete factor receiver face mounts once");
    let entering = ExactComplexWaveCurrent::new(
        Rat::from_integer(BigInt::from(5)),
        Rat::from_integer(BigInt::from(7)),
    );
    let returned = resident
        .conduct_joint_boundary_chain(
            &[
                ResidentBoundaryChainSupport {
                    port: 0,
                    reflected_quadratic_scale: BigUint::from(1_u8),
                    action_pair_scale: BigUint::from(1_u8),
                    action_quadratic_scale: BigUint::from(1_u8),
                    reflected_factor_current: vec![(0, BigUint::from(1_u8))],
                    action_factor_current: vec![(0, BigInt::from(3_i8))],
                },
                ResidentBoundaryChainSupport {
                    port: 1,
                    reflected_quadratic_scale: BigUint::from(1_u8),
                    action_pair_scale: BigUint::from(1_u8),
                    action_quadratic_scale: BigUint::from(1_u8),
                    reflected_factor_current: vec![(1, BigUint::from(1_u8))],
                    action_factor_current: vec![(1, BigInt::from(2_i8))],
                },
            ],
            2,
            &entering,
        )
        .expect("the complete port section returns");
    assert_eq!(returned.support_returns.len(), 2);
    assert_eq!(returned.port_returns.len(), 2);
    assert_eq!(
        returned.support_returns[0].reflected_family_overlaps,
        vec![Rat::from_integer(BigInt::from(2))]
    );
    assert_eq!(
        returned.support_returns[0].family_overlaps,
        vec![Rat::from_integer(BigInt::from(6))]
    );
    assert_eq!(
        returned.support_returns[1].reflected_family_overlaps,
        vec![Rat::from_integer(BigInt::from(-3))]
    );
    assert_eq!(
        returned.support_returns[1].family_overlaps,
        vec![Rat::from_integer(BigInt::from(-6))]
    );
    assert_eq!(
        returned.support_returns[0].returned_response,
        ExactComplexWaveCurrent::new(Rat::from_integer(BigInt::from(12)), Rat::zero())
    );
    assert_eq!(
        returned.support_returns[1].returned_response,
        ExactComplexWaveCurrent::new(Rat::from_integer(BigInt::from(-12)), Rat::zero())
    );
    assert!(returned.total_returned_current.is_zero());
    assert_eq!(returned.stored_difference, entering);
    assert!(returned.local_balance_closes);
    assert_eq!(returned.phase_locked_port_population, 1);
    assert!(returned.phase_front_is_unique);
    assert!(!returned.port_returns[0].lies_in_receiver_phase_front);
    assert!(returned.port_returns[1].lies_in_receiver_phase_front);
    assert_eq!(returned.launches, 6);
    assert_eq!(returned.device_dependency_edges, 5);
    assert_eq!(returned.synchronizations, 1);
    assert_eq!(returned.intermediate_host_egress_octets, 0);
    assert!(!returned.invariant_transport_reuploaded);
    assert!(!returned.cpu_semantic_replay_after_device);

    let multiplied = resident
        .conduct_joint_boundary_chain(
            &[ResidentBoundaryChainSupport {
                port: 0,
                reflected_quadratic_scale: BigUint::from(3_u8),
                action_pair_scale: BigUint::from(3_u8),
                action_quadratic_scale: BigUint::from(3_u8),
                reflected_factor_current: vec![(0, BigUint::from(1_u8))],
                action_factor_current: vec![(0, BigInt::from(3_i8))],
            }],
            1,
            &entering,
        )
        .expect("the quotiented reconstruction population returns once");
    assert_eq!(
        multiplied.support_returns[0].reflected_family_overlaps,
        vec![Rat::from_integer(BigInt::from(6))]
    );
    assert_eq!(
        multiplied.support_returns[0].family_overlaps,
        vec![Rat::from_integer(BigInt::from(18))]
    );
    assert_eq!(
        multiplied.support_returns[0].receiver_overlaps,
        vec![Rat::from_integer(BigInt::from(9))]
    );
    assert_eq!(
        multiplied.support_returns[0].receiver_action_norms,
        vec![BigUint::from(27_u8)]
    );
    assert_eq!(
        multiplied.total_returned_current,
        ExactComplexWaveCurrent::new(Rat::from_integer(BigInt::from(36)), Rat::zero())
    );

    let wide_current: BigUint = (BigUint::from(1_u8) << 96_usize) + BigUint::from(17_u8);
    let wide_return = resident
        .conduct_joint_boundary_chain(
            &[
                ResidentBoundaryChainSupport {
                    port: 0,
                    reflected_quadratic_scale: BigUint::from(1_u8),
                    action_pair_scale: BigUint::from(1_u8),
                    action_quadratic_scale: BigUint::from(1_u8),
                    reflected_factor_current: vec![(0, BigUint::from(1_u8))],
                    action_factor_current: vec![(0, BigInt::from(wide_current.clone()))],
                },
                ResidentBoundaryChainSupport {
                    port: 1,
                    reflected_quadratic_scale: BigUint::from(1_u8),
                    action_pair_scale: BigUint::from(1_u8),
                    action_quadratic_scale: BigUint::from(1_u8),
                    reflected_factor_current: vec![(1, BigUint::from(1_u8))],
                    action_factor_current: vec![(1, BigInt::from(1_i8))],
                },
            ],
            2,
            &entering,
        )
        .expect("the multi-limb factor section returns without a scalar aperture");
    assert_eq!(
        wide_return.support_returns[0].returned_response,
        ExactComplexWaveCurrent::new(
            Rat::from_integer(BigInt::from(wide_current) * BigInt::from(4_u8)),
            Rat::zero(),
        )
    );
    // Projective comparison is scale-natural in the action section: widening one action
    // coefficient does not manufacture a new phase direction.
    assert!(!wide_return.port_returns[0].lies_in_receiver_phase_front);
    assert!(wide_return.port_returns[1].lies_in_receiver_phase_front);
}

/// The resident moment quotient returns exactly the same quadratic consequences as the
/// explicitly enumerated context-by-restriction family on a bounded body.  The production
/// path may therefore retain that family only as reconstruction testimony.
#[test]
#[ignore = "requires the RTX CUDA device"]
fn quadratic_moment_front_equals_the_enumerated_boundary_law() {
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
    resident
        .mount_factor_receiver_faces(&[0], &[0, 1])
        .expect("the receiver face mounts once");
    resident
        .mount_boundary_restriction_atlas(&ResidentBoundaryRestrictionAtlas {
            state_count: 2,
            universal_port_count: 2,
            state_port_transition: vec![0, u32::MAX, u32::MAX, 1],
            transition_targets: vec![1, 0],
            transition_factor_offsets: vec![0, 2, 3],
            transition_factors: vec![0, 1, 1],
            transition_currents: vec![
                BigUint::from(1_u8),
                BigUint::from(3_u8),
                BigUint::from(2_u8),
            ],
        })
        .expect("the complete restriction atlas mounts once");
    let front = ResidentQuadraticMomentFront {
        contexts: vec![
            AddressedCurrentSection {
                boundary_state: None,
                quadratic_weight: BigUint::from(3_u8),
                factor_current: vec![(0, BigUint::from(2_u8)), (1, BigUint::from(1_u8))],
            },
            AddressedCurrentSection {
                boundary_state: None,
                quadratic_weight: BigUint::from(5_u8),
                factor_current: vec![(0, BigUint::from(1_u8))],
            },
        ],
        resident_source: None,
        resident_image: None,
        restrictions: ResidentQuadraticMomentRestrictionSource::DirectWitness(vec![
            ResidentQuadraticMomentRestriction {
                port: 0,
                factor_current: vec![(0, BigUint::from(1_u8)), (1, BigUint::from(3_u8))],
            },
            ResidentQuadraticMomentRestriction {
                port: 1,
                factor_current: vec![(1, BigUint::from(2_u8))],
            },
        ]),
        generator_targets: vec![1, 0],
        generator_count: 1,
        presented_current: None,
    };
    let returned = resident
        .conduct_quadratic_moment_front(
            &front,
            2,
            &ExactComplexWaveCurrent::new(
                Rat::from_integer(BigInt::from(5)),
                Rat::from_integer(BigInt::from(7)),
            ),
            true,
        )
        .expect("the moment quotient returns");
    assert_eq!(returned.ports.len(), 2);
    assert_eq!(
        returned.ports[0].moment,
        vec![17_u8, 18, 18, 27]
            .into_iter()
            .map(BigUint::from)
            .collect::<Vec<_>>()
    );
    assert_eq!(
        returned.ports[1].moment,
        vec![0_u8, 0, 0, 12]
            .into_iter()
            .map(BigUint::from)
            .collect::<Vec<_>>()
    );
    assert_eq!(
        returned.ports[0].reflected_family_overlaps,
        vec![BigInt::from(-47)]
    );
    assert_eq!(returned.ports[0].family_overlaps, vec![BigInt::from(29)]);
    assert_eq!(returned.ports[0].receiver_overlaps, vec![BigInt::from(-8)]);
    assert_eq!(
        returned.ports[0].receiver_action_norms,
        vec![BigUint::from(16_u8)]
    );
    assert_eq!(
        returned.ports[1].reflected_family_overlaps,
        vec![BigInt::from(-36)]
    );
    assert_eq!(returned.ports[1].family_overlaps, vec![BigInt::from(36)]);
    assert_eq!(returned.ports[1].receiver_overlaps, vec![BigInt::from(-12)]);
    assert_eq!(
        returned.ports[1].receiver_action_norms,
        vec![BigUint::from(24_u8)]
    );
    assert_eq!(returned.launches, 10);
    assert_eq!(returned.device_dependency_edges, 9);
    assert_eq!(returned.synchronizations, 1);
    assert_eq!(returned.intermediate_host_egress_octets, 0);
    assert!(!returned.invariant_transport_reuploaded);
    assert!(!returned.cpu_semantic_replay_after_device);

    let factorized = resident
        .conduct_quadratic_moment_front(
            &front,
            2,
            &ExactComplexWaveCurrent::new(
                Rat::from_integer(BigInt::from(5)),
                Rat::from_integer(BigInt::from(7)),
            ),
            false,
        )
        .expect("the sparse rank-one presentation returns the same receiver consequences");
    assert!(factorized.ports.iter().all(|port| port.moment.is_empty()));
    assert!(!factorized.moment_field_materialized);
    assert!(factorized.moment_factorization_retained);
    assert_eq!(factorized.active_factor_population, 2);
    assert_eq!(factorized.native_factor_population, 2);
    assert_eq!(factorized.launches, 10);
    assert_eq!(factorized.device_dependency_edges, 9);
    assert_eq!(factorized.port_returns, returned.port_returns);
    assert_eq!(
        factorized.total_returned_current,
        returned.total_returned_current
    );
    assert_eq!(factorized.stored_difference, returned.stored_difference);
    assert_eq!(
        factorized.local_balance_closes,
        returned.local_balance_closes
    );
    for (sparse, dense) in factorized.ports.iter().zip(&returned.ports) {
        assert_eq!(
            sparse.reflected_family_overlaps,
            dense.reflected_family_overlaps
        );
        assert_eq!(sparse.family_overlaps, dense.family_overlaps);
        assert_eq!(sparse.receiver_overlaps, dense.receiver_overlaps);
        assert_eq!(sparse.receiver_action_norms, dense.receiver_action_norms);
    }

    // Cross the card-derived context grain.  The factorized path must return the same exact
    // receiver section when its ordered summands occupy more than one resident context
    // interval; this distinguishes the parallel cover from a truncated first interval.
    let chunked_front = ResidentQuadraticMomentFront {
        contexts: (0..300)
            .map(|at| AddressedCurrentSection {
                boundary_state: None,
                quadratic_weight: BigUint::from((at % 3 + 1) as u32),
                factor_current: vec![
                    (0, BigUint::from((at % 5 + 1) as u32)),
                    (1, BigUint::from((at % 7 + 1) as u32)),
                ],
            })
            .collect(),
        resident_source: None,
        resident_image: None,
        restrictions: front.restrictions.clone(),
        generator_targets: front.generator_targets.clone(),
        generator_count: front.generator_count,
        presented_current: None,
    };
    let chunked_dense = resident
        .conduct_quadratic_moment_front(
            &chunked_front,
            2,
            &ExactComplexWaveCurrent::new(
                Rat::from_integer(BigInt::from(5)),
                Rat::from_integer(BigInt::from(7)),
            ),
            true,
        )
        .expect("the dense diagnostic crosses the context grain");
    let chunked_factorized = resident
        .conduct_quadratic_moment_front(
            &chunked_front,
            2,
            &ExactComplexWaveCurrent::new(
                Rat::from_integer(BigInt::from(5)),
                Rat::from_integer(BigInt::from(7)),
            ),
            false,
        )
        .expect("the factorized context cover crosses the same exact receiver");
    assert_eq!(chunked_factorized.port_returns, chunked_dense.port_returns);
    assert_eq!(
        chunked_factorized.total_returned_current,
        chunked_dense.total_returned_current,
    );
    assert_eq!(
        chunked_factorized.stored_difference,
        chunked_dense.stored_difference,
    );
    for (sparse, dense) in chunked_factorized.ports.iter().zip(&chunked_dense.ports) {
        assert_eq!(
            sparse.reflected_family_overlaps,
            dense.reflected_family_overlaps
        );
        assert_eq!(sparse.family_overlaps, dense.family_overlaps);
        assert_eq!(sparse.receiver_overlaps, dense.receiver_overlaps);
        assert_eq!(sparse.receiver_action_norms, dense.receiver_action_norms);
    }

    let resident_boundary = resident
        .conduct_quadratic_moment_front(
            &ResidentQuadraticMomentFront {
                contexts: front.contexts.clone(),
                resident_source: None,
                resident_image: None,
                restrictions: ResidentQuadraticMomentRestrictionSource::ResidentBoundary(
                    ResidentBoundaryRestrictionFront {
                        boundary_states: vec![0, 1],
                        universal_ports: vec![0, 1],
                    },
                ),
                generator_targets: front.generator_targets.clone(),
                generator_count: front.generator_count,
                presented_current: None,
            },
            2,
            &ExactComplexWaveCurrent::new(
                Rat::from_integer(BigInt::from(5)),
                Rat::from_integer(BigInt::from(7)),
            ),
            false,
        )
        .expect("the resident atlas returns the direct witness's exact consequences");
    assert_eq!(resident_boundary.restriction_population, 2);
    assert_eq!(resident_boundary.launches, 16);
    assert_eq!(resident_boundary.device_dependency_edges, 15);
    assert_eq!(resident_boundary.synchronizations, 3);
    assert!(
        resident_boundary.successor_host_ingress_octets < factorized.successor_host_ingress_octets
    );
    assert_eq!(resident_boundary.ports, factorized.ports);
    assert_eq!(resident_boundary.port_returns, factorized.port_returns);
    assert_eq!(
        resident_boundary.total_returned_current,
        factorized.total_returned_current
    );
    assert_eq!(
        resident_boundary.stored_difference,
        factorized.stored_difference
    );
    assert_eq!(
        resident_boundary.local_balance_closes,
        factorized.local_balance_closes
    );
    let conditioned = resident_boundary
        .conditioned_current
        .as_ref()
        .expect("the resident restriction returns its addressed successor current");
    assert_eq!(
        conditioned
            .passage
            .slots
            .iter()
            .map(|slot| slot.boundary_state)
            .collect::<BTreeSet<_>>(),
        BTreeSet::from([0_u32]),
        "each restriction slot carries its transition target rather than its source state",
    );
    assert_eq!(
        conditioned
            .passage
            .target
            .iter()
            .filter_map(|section| section.boundary_state)
            .collect::<BTreeSet<_>>(),
        BTreeSet::from([0_u32]),
        "equal current rows at distinct successor states remain distinct addressed targets",
    );
    assert!(!resident_boundary.invariant_transport_reuploaded);
    assert!(!resident_boundary.cpu_semantic_replay_after_device);
}
