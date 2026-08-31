#[cfg(test)]
mod tests {
    use crate::exact_linear::ExactRatMatrix;
    use crate::receiver_exact_compression::{Observation, compress};
    use crate::receiver_history_compression::*;
    use relational_geometry::Rat;

    fn exact(entries: &[[i64; 3]; 3]) -> ExactRatMatrix {
        ExactRatMatrix::new(
            entries
                .iter()
                .map(|row| {
                    row.iter()
                        .map(|entry| Rat::from_integer((*entry).into()))
                        .collect()
                })
                .collect(),
        )
        .expect("exact 3 by 3 matrix")
    }

    #[test]
    fn observable_moment_span_descends_every_generator_and_returns_its_complete_kernel() {
        let receiver = exact(&[[1, 0, 0], [0, 0, 0], [0, 0, 0]]);
        let generator = exact(&[[0, 1, 0], [0, 0, 1], [1, 0, 0]]);
        let compression = ObservableMomentReceiverHistoryCompression::found(
            vec![receiver.clone()],
            vec![generator.clone()],
        )
        .expect("invariant observable span");

        // One present receiver becomes the three diagonal faces encountered around the cycle.
        // The six off-diagonal covariance directions are returned as the exact invisible fibre.
        assert_eq!(compression.basis_forms.len(), 3);
        assert_eq!(compression.present_receiver_factors.rows(), 1);
        assert_eq!(compression.present_receiver_factors.columns(), 3);
        assert_eq!(compression.descended_generator_actions.len(), 1);
        assert_eq!(compression.descended_generator_actions[0].rows(), 3);
        assert_eq!(compression.descended_generator_actions[0].columns(), 3);
        assert_eq!(compression.reconstruction_kernel_basis.len(), 6);
        assert!(
            compression
                .reconstruction_kernel_basis
                .iter()
                .all(|direction| direction.len() == 9)
        );

        let moment = exact(&[[2, 3, 5], [7, 11, 13], [17, 19, 23]]);
        let transported = generator
            .multiply(&moment)
            .and_then(|left| left.multiply(&generator.transpose()?))
            .expect("source transport");
        let coordinates = compression.quotient(&moment).expect("observable section");
        assert_eq!(
            compression
                .quotient(&transported)
                .expect("transported section"),
            compression
                .transport_quotient(0, &coordinates)
                .expect("descended transport")
        );
        assert_eq!(
            contract_exact_forms(&receiver, &moment),
            compression
                .present_receiver(0, &coordinates)
                .expect("present receiver factor")
        );

        // Three turns return the same observable coordinate section for every source moment.
        let once = compression
            .transport_quotient(0, &coordinates)
            .expect("first turn");
        let twice = compression
            .transport_quotient(0, &once)
            .expect("second turn");
        let thrice = compression
            .transport_quotient(0, &twice)
            .expect("third turn");
        assert_eq!(thrice, coordinates);
    }

    #[test]
    fn primitive_integral_frame_carries_noninjective_preimages_with_their_exact_scale() {
        let present = SparseIntegralBilinearForm::new(3, [((0, 0), BigInt::from(2))])
            .expect("present receiver form");
        let frame = ObservableIntegralFormFrame::found(vec![present], vec![vec![0, 0, 1]])
            .expect("closed integral frame");

        // Pullback expands e_0 e_0^T through its two-point preimage, then through the complete
        // three-point preimage; the final all-ones form is fixed.
        assert_eq!(frame.forms.len(), 3);
        assert_eq!(frame.forms[0].entries.len(), 1);
        assert_eq!(frame.forms[1].entries.len(), 4);
        assert_eq!(frame.forms[2].entries.len(), 9);
        assert_eq!(
            frame.present_receiver_factors,
            vec![IntegralFormFrameFactor {
                coordinate: Some(0),
                scale: BigInt::from(2),
            }]
        );

        let current = vec![BigInt::from(1), BigInt::from(2), BigInt::from(3)];
        let coordinates = frame
            .quotient_rank_one_family(&[(BigInt::from(1), current)])
            .expect("observable coordinates");
        assert_eq!(coordinates, [1, 9, 36].map(BigInt::from));
        assert_eq!(
            frame
                .present_receivers(&coordinates)
                .expect("present receiver"),
            vec![BigInt::from(2)]
        );

        let transported_current = vec![BigInt::from(3), BigInt::from(3), BigInt::from(0)];
        let direct = frame
            .quotient_rank_one_family(&[(BigInt::from(1), transported_current)])
            .expect("direct transported coordinates");
        assert_eq!(
            frame
                .transport(0, &coordinates)
                .expect("descended transport"),
            direct
        );
        assert_eq!(direct, [9, 36, 36].map(BigInt::from));
    }

    #[test]
    fn factored_functional_frame_carries_plural_generator_moments_without_cross_terms() {
        let functional = |entries: &[(u32, i64)]| {
            SparseIntegralFunctional::new(
                3,
                entries
                    .iter()
                    .map(|(factor, coefficient)| (*factor, BigInt::from(*coefficient))),
            )
            .expect("sparse functional")
        };
        let present = FactoredIntegralReceiverForm::new(
            3,
            [
                FactoredIntegralReceiverTerm {
                    coefficient: BigInt::from(1),
                    left: functional(&[(0, 1)]),
                    right: functional(&[(0, 1)]),
                },
                FactoredIntegralReceiverTerm {
                    coefficient: BigInt::from(2),
                    left: functional(&[(1, 1)]),
                    right: functional(&[(2, 1)]),
                },
            ],
        )
        .expect("factored present receiver");
        let generators = vec![vec![1, 2, 0], vec![2, 0, 1]];
        let frame =
            FactoredIntegralReceiverHistoryFrame::found(vec![present.clone()], generators.clone())
                .expect("closed factored receiver history");
        assert_eq!(frame.forms.len(), 6);

        let family = vec![
            (BigInt::from(2), [1, 2, 3].map(BigInt::from).to_vec()),
            (BigInt::from(3), [2, 1, 1].map(BigInt::from).to_vec()),
        ];
        let coordinates = frame
            .quotient_rank_one_family(&family)
            .expect("factored quotient");
        let transport = |current: &[BigInt], targets: &[u32]| {
            let mut returned = vec![BigInt::ZERO; targets.len()];
            for (source, target) in targets.iter().enumerate() {
                returned[*target as usize] += &current[source];
            }
            returned
        };
        let direct_family = generators
            .iter()
            .flat_map(|generator| {
                family
                    .iter()
                    .map(|(weight, current)| (weight.clone(), transport(current, generator)))
            })
            .collect::<Vec<_>>();
        let direct = frame
            .quotient_rank_one_family(&direct_family)
            .expect("direct plural generator moment");
        let descended = frame
            .transport_direct_sum(&[0, 1], &coordinates)
            .expect("descended direct sum");
        assert_eq!(descended, direct);

        // Summing generator images before taking the moment creates cross terms and is distinct.
        let false_family = family
            .iter()
            .map(|(weight, current)| {
                let left = transport(current, &generators[0]);
                let right = transport(current, &generators[1]);
                (
                    weight.clone(),
                    left.into_iter().zip(right).map(|(l, r)| l + r).collect(),
                )
            })
            .collect::<Vec<_>>();
        assert_ne!(
            frame
                .quotient_rank_one_family(&false_family)
                .expect("false summed-current moment"),
            direct
        );
    }

    #[test]
    fn addressed_primitive_receiver_frame_reconstructs_scaled_swapped_and_zero_faces() {
        let functional = |entries: &[(u32, i64)]| {
            SparseIntegralFunctional::new(
                3,
                entries
                    .iter()
                    .map(|(factor, coefficient)| (*factor, BigInt::from(*coefficient))),
            )
            .expect("sparse functional")
        };
        let complex = |left_scale: i64, right_scale: i64, source: u32| {
            AddressedFactoredIntegralReceiverComplex {
                schema: "holonic-engine.addressed-factored-integral-receiver-complex.v1".to_owned(),
                factor_population: 3,
                family_population: 1,
                receiver_population: 2,
                generator_population: 1,
                functionals: vec![
                    functional(&[(0, left_scale)]),
                    functional(&[(1, right_scale)]),
                    functional(&[]),
                ],
                receivers: vec![
                    AddressedFactoredIntegralReceiver {
                        terms: vec![
                            AddressedFactoredIntegralReceiverTerm {
                                coefficient: BigInt::from(1),
                                left_functional: 0,
                                right_functional: 1,
                            },
                            AddressedFactoredIntegralReceiverTerm {
                                coefficient: BigInt::from(2),
                                left_functional: 1,
                                right_functional: 0,
                            },
                        ],
                    },
                    AddressedFactoredIntegralReceiver {
                        terms: vec![AddressedFactoredIntegralReceiverTerm {
                            coefficient: BigInt::from(5),
                            left_functional: 2,
                            right_functional: 0,
                        }],
                    },
                ],
                reconstruction_fibre: vec![(source, BigUint::from(source + 1))],
            }
        };
        let complexes = vec![complex(2, 3, 7), complex(4, -6, 11)];
        let frame = AddressedPrimitiveReceiverFrame::found(&complexes)
            .expect("one primitive pair-current frame");

        assert_eq!(frame.functionals.len(), 3);
        assert_eq!(frame.functional_pairs.len(), 2);
        assert_eq!(frame.presented_term_factors.len(), 6);
        assert_eq!(frame.receiver_factors.len(), 4);
        assert_eq!(frame.occurrence_receiver_offsets, vec![0, 2, 4]);
        assert_eq!(
            frame.occurrence_reconstruction_fibres,
            vec![
                vec![(7, BigUint::from(8_u8))],
                vec![(11, BigUint::from(12_u8))]
            ]
        );

        let family = vec![
            (BigInt::from(2), [7, 11, 13].map(BigInt::from).to_vec()),
            (BigInt::from(3), [2, 5, 17].map(BigInt::from).to_vec()),
        ];
        let pair_coordinates = frame
            .pair_coordinates(&family)
            .expect("primitive pair coordinates");
        let condensed = frame
            .receiver_coordinates(&pair_coordinates)
            .expect("sparse receiver projection");
        let presented = frame
            .presented_receiver_coordinates(&pair_coordinates)
            .expect("ordered reconstruction fibre");
        let direct = complexes
            .iter()
            .flat_map(|complex| {
                complex
                    .contract_rank_one_family(&family)
                    .expect("direct addressed contraction")
            })
            .collect::<Vec<_>>();
        assert_eq!(condensed, presented);
        assert_eq!(condensed, direct);
        assert_eq!(condensed[1], BigInt::ZERO);
        assert_eq!(condensed[3], BigInt::ZERO);
    }

    #[test]
    fn projective_current_passage_squares_removed_scale_and_condenses_only_the_live_front() {
        let source = ProjectiveCurrentSection::found(
            3,
            vec![
                (
                    BigUint::from(2_u8),
                    vec![(0, BigUint::from(2_u8)), (1, BigUint::from(4_u8))],
                ),
                (
                    BigUint::from(3_u8),
                    vec![(0, BigUint::from(1_u8)), (1, BigUint::from(2_u8))],
                ),
            ],
        )
        .expect("projective source section");
        assert_eq!(source.rays.len(), 1);
        assert_eq!(source.weights, vec![BigUint::from(11_u8)]);

        let passage = source
            .transport_direct_sum(&[vec![1, 0, 2], vec![0, 0, 2]])
            .expect("one live direct-sum passage");
        assert_eq!(passage.source_ray_population, 1);
        assert_eq!(passage.target_ray_population, 2);
        assert_eq!(passage.edges.len(), 2);
        assert_eq!(passage.target.weights[0], BigUint::from(11_u8));
        assert_eq!(passage.target.weights[1], BigUint::from(99_u8));
        assert_eq!(passage.edges[1].removed_scale, BigUint::from(3_u8));
        assert_eq!(passage.target.reconstruction_fibre.len(), 2);
    }

    #[test]
    fn membrane_form_frame_factors_scaled_restrictions_and_returns_every_declared_face() {
        let restriction = vec![
            (0, BigUint::from(1_u8)),
            (1, BigUint::from(2_u8)),
            (2, BigUint::from(3_u8)),
        ];
        let scaled = restriction
            .iter()
            .map(|(factor, coefficient)| (*factor, coefficient * BigUint::from(2_u8)))
            .collect::<Vec<_>>();
        let addressed = membrane_addressed_factored_receiver_complex(
            &restriction,
            &[1, 1, 1],
            &[1, 1, 1],
            &[0, 0, 1],
            &[2],
            &[vec![0, 0, 1]],
        )
        .expect("addressed membrane receiver complex");
        let factored = MembraneFactoredIntegralReceiverHistory::found(
            &[1, 1, 1],
            &[1, 1, 1],
            &[0, 0, 1],
            &[2],
            vec![restriction.clone(), scaled.clone()],
            vec![vec![0, 0, 1]],
        )
        .expect("factored membrane receiver history");
        let atlas = MembraneObservableIntegralFrame::found(
            &[1, 1, 1],
            &[1, 1, 1],
            &[0, 0, 1],
            &[2],
            vec![restriction, scaled],
            vec![vec![0, 0, 1]],
        )
        .expect("membrane observable frame");
        assert_eq!(atlas.primitive_restrictions.len(), 1);
        assert_eq!(atlas.transition_restriction_factors.len(), 2);
        assert_eq!(
            atlas.transition_restriction_factors[0].quadratic_scale,
            BigUint::from(1_u8)
        );
        assert_eq!(
            atlas.transition_restriction_factors[1].quadratic_scale,
            BigUint::from(4_u8)
        );
        assert_eq!(atlas.present_forms_per_restriction, 4);

        let family = [(
            BigInt::from(1),
            vec![BigInt::from(1), BigInt::from(2), BigInt::from(3)],
        )];
        let coordinates = atlas
            .frame
            .quotient_rank_one_family(&family)
            .expect("observable coordinates");
        let direct = atlas
            .frame
            .present_receivers(&coordinates)
            .expect("every direct present receiver face");
        assert_eq!(direct, [98, -57, -36, 162].map(BigInt::from));
        assert_eq!(
            addressed
                .contract_rank_one_family(&family)
                .expect("addressed receiver contraction"),
            direct
        );
        assert!(
            addressed.functionals.len()
                < addressed
                    .receivers
                    .iter()
                    .map(|receiver| receiver.terms.len())
                    .sum()
        );
        let factored_coordinates = factored
            .frame
            .quotient_rank_one_family(&family)
            .expect("factored coordinates");
        assert_eq!(
            factored
                .frame
                .present_receivers(&factored_coordinates)
                .expect("every factored present receiver face"),
            direct
        );
        assert!(factored.frame.forms.iter().all(|form| {
            form.terms
                .iter()
                .all(|term| !term.left.entries.is_empty() && !term.right.entries.is_empty())
        }));
    }

    struct PairedCycle;

    impl ObservedSystem for PairedCycle {
        fn items(&self) -> Vec<ItemId> {
            (0..8).map(ItemId).collect()
        }

        fn receivers(&self) -> Vec<ReceiverId> {
            vec![ReceiverId(0)]
        }

        fn inputs(&self) -> Vec<InputId> {
            vec![InputId(0), InputId(1)]
        }

        fn observation(&self, item: ItemId, _: ReceiverId) -> Observation {
            Observation(item.0 % 2)
        }

        fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
            Some(match input.0 {
                0 => ItemId((item.0 + 2) % 8),
                _ => ItemId(7 - item.0),
            })
        }
    }

    struct PairedPartialChain;

    impl ObservedSystem for PairedPartialChain {
        fn items(&self) -> Vec<ItemId> {
            (0..4).map(ItemId).collect()
        }

        fn receivers(&self) -> Vec<ReceiverId> {
            vec![ReceiverId(0)]
        }

        fn inputs(&self) -> Vec<InputId> {
            vec![InputId(9)]
        }

        fn observation(&self, item: ItemId, _: ReceiverId) -> Observation {
            Observation(item.0 / 2)
        }

        fn successor(&self, item: ItemId, _: InputId) -> Option<ItemId> {
            match item.0 {
                0 => Some(ItemId(2)),
                1 => Some(ItemId(3)),
                _ => None,
            }
        }
    }

    #[test]
    fn partial_native_action_retains_the_open_terminus_without_a_self_loop() {
        let system = PairedPartialChain;
        let exact = compress(&system);
        let native = PartialReceiverHistoryCompression::found(&system, &exact)
            .expect("partial native action");
        native.validate().expect("validated partial action");
        assert_eq!(native.native_population.len(), 2);
        assert_eq!(native.generators.len(), 1);
        assert_eq!(native.generators[0].native.len(), 1);
        assert_eq!(native.generators[0].terminating_natives.len(), 1);
        assert!(
            native.generators[0]
                .native
                .iter()
                .all(|edge| edge.from != edge.to)
        );
    }

    #[test]
    fn generator_squares_found_every_ordered_word_and_decoder_reopens_the_fibre() {
        let system = PairedCycle;
        let exact = compress(&system);
        let native = ReceiverHistoryCompression::found(&system, &exact).expect("stable quotient");
        assert!(native.native_population.len() < native.source_population.len());
        for source in &native.source_population {
            for word in [
                vec![],
                vec![InputId(0)],
                vec![InputId(1), InputId(0), InputId(1), InputId(0)],
            ] {
                assert!(
                    native
                        .ordered_word_consequence(*source, &word)
                        .expect("declared word")
                        .commutes()
                );
            }
        }
        let decoded = native
            .decode(native.encode(ItemId(0)).expect("encoded"), ReceiverId(0))
            .expect("declared image");
        assert_eq!(decoded.observation, Observation(0));
        assert!(decoded.reconstruction_fibre.len() > 1);
    }

    struct Terminates;

    impl ObservedSystem for Terminates {
        fn items(&self) -> Vec<ItemId> {
            vec![ItemId(0)]
        }
        fn receivers(&self) -> Vec<ReceiverId> {
            vec![ReceiverId(0)]
        }
        fn inputs(&self) -> Vec<InputId> {
            vec![InputId(0)]
        }
        fn observation(&self, _: ItemId, _: ReceiverId) -> Observation {
            Observation(0)
        }
        fn successor(&self, _: ItemId, _: InputId) -> Option<ItemId> {
            None
        }
    }

    #[test]
    fn a_partial_successor_cannot_pose_as_the_total_m3_transport_square() {
        let system = Terminates;
        let exact = compress(&system);
        assert!(matches!(
            ReceiverHistoryCompression::found(&system, &exact),
            Err(ReceiverHistoryRefusal::SourceTransportTerminates { .. })
        ));
    }
}
