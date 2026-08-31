use super::*;
use crate::exact_linear::ExactRatMatrix;
use crate::receiver_history_compression::{
    AddressedFactoredIntegralReceiver, AddressedFactoredIntegralReceiverComplex,
    AddressedFactoredIntegralReceiverTerm, FactoredIntegralReceiverForm,
    FactoredIntegralReceiverTerm, SparseIntegralFunctional,
};
use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use relational_geometry::Rat;

fn current(weight: u32, entries: &[(u32, u32)]) -> WeightedIntegralCurrent {
    WeightedIntegralCurrent {
        weight: BigUint::from(weight),
        entries: entries
            .iter()
            .map(|(factor, coefficient)| (*factor, BigUint::from(*coefficient)))
            .collect(),
    }
}

fn functional(entries: &[(u32, i64)]) -> SparseIntegralFunctional {
    SparseIntegralFunctional::new(
        3,
        entries
            .iter()
            .map(|(factor, coefficient)| (*factor, BigInt::from(*coefficient))),
    )
    .expect("functional")
}

fn transport_family(
    family: &[(BigInt, Vec<BigInt>)],
    generators: &[Vec<u32>],
) -> Vec<(BigInt, Vec<BigInt>)> {
    generators
        .iter()
        .flat_map(|generator| {
            family.iter().map(|(weight, source)| {
                let mut target = vec![BigInt::zero(); source.len()];
                for (source_factor, coefficient) in source.iter().enumerate() {
                    target[generator[source_factor] as usize] += coefficient;
                }
                (weight.clone(), target)
            })
        })
        .collect()
}

#[test]
fn sparse_pair_current_preserves_noninjective_collapse_and_fixed_carrier() {
    let family = vec![current(1, &[(0, 1), (1, 2)])];
    let generators = vec![vec![0, 0, 2]];
    let foundation = SparseQuadraticMomentFoundation::found(3, family, generators)
        .expect("sparse quadratic foundation");
    let off_diagonal = foundation
        .action
        .pairs
        .iter()
        .position(|pair| *pair == SymmetricFactorPair::new(0, 1))
        .expect("off diagonal");
    assert_eq!(foundation.action.multiplicities[off_diagonal], 2);
    let target = foundation
        .section
        .transport_direct_sum(&foundation.action)
        .expect("transport");
    assert_eq!(target.pairs, foundation.section.pairs);
    assert_eq!(target.coefficient(0, 0), Some(&BigUint::from(9_u32)));
    assert_eq!(target.generation, 1);
}

#[test]
fn quadratic_history_does_not_square_a_prematurely_integrated_first_moment() {
    let generators = vec![vec![0, 1]];
    let history = SparseQuadraticMomentFoundation::found(
        2,
        vec![current(1, &[(0, 1)]), current(1, &[(1, 1)])],
        generators.clone(),
    )
    .expect("separated occurrence moment");
    let integrated =
        SparseQuadraticMomentFoundation::found(2, vec![current(1, &[(0, 1), (1, 1)])], generators)
            .expect("prematurely integrated first moment");

    assert_eq!(history.section.coefficient(0, 0), Some(&BigUint::one()));
    assert_eq!(history.section.coefficient(1, 1), Some(&BigUint::one()));
    assert_eq!(history.section.coefficient(0, 1), None);
    assert_eq!(integrated.section.coefficient(0, 1), Some(&BigUint::one()));
    assert_ne!(history.section, integrated.section);
}

#[test]
fn returned_diagonal_restriction_conditions_both_moment_legs_without_advancing_time() {
    let foundation = SparseQuadraticMomentFoundation::found(
        3,
        vec![current(2, &[(0, 1), (1, 2), (2, 3)])],
        vec![vec![0, 1, 2]],
    )
    .expect("sparse quadratic foundation");
    let transported = foundation
        .section
        .transport_direct_sum(&foundation.action)
        .expect("transport");
    let restricted = transported
        .condition_by_diagonal_restriction(&[(0, BigUint::from(2_u8)), (2, BigUint::from(5_u8))])
        .expect("returned boundary restriction");

    assert_eq!(restricted.generation, transported.generation);
    assert_eq!(restricted.pairs, transported.pairs);
    assert_eq!(restricted.coefficient(0, 0), Some(&BigUint::from(8_u8)));
    assert_eq!(restricted.coefficient(0, 2), Some(&BigUint::from(60_u8)));
    assert_eq!(restricted.coefficient(1, 1), Some(&BigUint::zero()));
    assert_eq!(restricted.coefficient(2, 2), Some(&BigUint::from(450_u16)));
}

#[test]
fn sparse_pair_recurrence_and_receiver_equal_direct_family_over_several_orders() {
    let family = vec![
        current(2, &[(0, 1), (1, 2), (2, 3)]),
        current(3, &[(0, 2), (1, 1), (2, 1)]),
    ];
    let generators = vec![vec![1, 2, 0], vec![0, 0, 2]];
    let foundation = SparseQuadraticMomentFoundation::found(3, family.clone(), generators.clone())
        .expect("sparse quadratic foundation");
    let functionals = vec![
        functional(&[(0, 1), (1, -1)]),
        functional(&[(1, 1), (2, 2)]),
        functional(&[(0, 2), (2, -1)]),
    ];
    let complex = AddressedFactoredIntegralReceiverComplex {
        schema: "holonic-engine.addressed-factored-integral-receiver-complex.v1".to_owned(),
        factor_population: 3,
        family_population: family.len() as u32,
        receiver_population: 2,
        generator_population: generators.len() as u32,
        functionals,
        receivers: vec![
            AddressedFactoredIntegralReceiver {
                terms: vec![AddressedFactoredIntegralReceiverTerm {
                    coefficient: BigInt::from(3),
                    left_functional: 0,
                    right_functional: 1,
                }],
            },
            AddressedFactoredIntegralReceiver {
                terms: vec![
                    AddressedFactoredIntegralReceiverTerm {
                        coefficient: BigInt::from(-2),
                        left_functional: 2,
                        right_functional: 0,
                    },
                    AddressedFactoredIntegralReceiverTerm {
                        coefficient: BigInt::from(1),
                        left_functional: 1,
                        right_functional: 1,
                    },
                ],
            },
        ],
        reconstruction_fibre: vec![(0, BigUint::one())],
    };
    let frame = SparseQuadraticPairReceiverFrame::found(&foundation.action, &complex)
        .expect("pair receiver frame");
    let forms = complex.reopen_receiver_forms().expect("receiver forms");
    let mut direct_family = family
        .iter()
        .map(|current| {
            let mut dense = vec![BigInt::zero(); 3];
            for (factor, coefficient) in &current.entries {
                dense[*factor as usize] = BigInt::from(coefficient.clone());
            }
            (BigInt::from(current.weight.clone()), dense)
        })
        .collect::<Vec<_>>();
    let mut section = foundation.section;
    for generation in 0..4 {
        assert_eq!(section.generation, generation);
        let sparse_reading = frame.contract(&section).expect("sparse reading");
        let direct_reading = forms
            .iter()
            .map(|receiver| {
                receiver
                    .contract_rank_one_family(&direct_family)
                    .expect("direct reading")
            })
            .collect::<Vec<_>>();
        assert_eq!(sparse_reading, direct_reading);
        section = section
            .transport_direct_sum(&foundation.action)
            .expect("sparse recurrence");
        direct_family = transport_family(&direct_family, &generators);
    }
}

#[test]
fn equal_covariances_return_one_canonical_section_without_equal_sources() {
    let left = FactoredMomentSection::found(3, vec![current(4, &[(0, 1), (1, 2)])])
        .expect("left foundation");
    let right = FactoredMomentSection::found(3, vec![current(1, &[(0, 2), (1, 4)])])
        .expect("right foundation");
    assert_eq!(left.section, right.section);
    assert_ne!(left.reconstruction_fibre, right.reconstruction_fibre);
    assert_eq!(left.section.image_rank, 1);
    assert_eq!(left.section.basis_factors, vec![0]);
    assert_eq!(
        left.section.reconstruct_entry(0, 1).expect("entry"),
        Rat::from_integer(BigInt::from(8))
    );
}

#[test]
fn plural_generator_passage_matches_direct_rank_one_receiver() {
    let family = vec![
        current(2, &[(0, 1), (1, 2), (2, 3)]),
        current(3, &[(0, 2), (1, 1), (2, 1)]),
    ];
    let foundation = FactoredMomentSection::found(3, family.clone()).expect("foundation");
    let receiver = FactoredIntegralReceiverForm::new(
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
    .expect("receiver");
    let generators = vec![vec![1, 2, 0], vec![2, 0, 1]];
    let passage = foundation
        .section
        .transport_direct_sum(&generators)
        .expect("generator passage");
    let direct_family = generators
        .iter()
        .flat_map(|generator| {
            family.iter().map(|source| {
                let mut target = vec![BigInt::zero(); 3];
                for (factor, coefficient) in &source.entries {
                    target[generator[*factor as usize] as usize] +=
                        BigInt::from(coefficient.clone());
                }
                (BigInt::from(source.weight.clone()), target)
            })
        })
        .collect::<Vec<_>>();
    let direct = receiver
        .contract_rank_one_family(&direct_family)
        .expect("direct contraction");
    assert_eq!(
        passage
            .target
            .contract_receiver(&receiver)
            .expect("factored contraction"),
        Rat::from_integer(direct)
    );
    assert_eq!(passage.source_image_rank, 2);
    assert_eq!(passage.target_image_rank, 3);
    assert_eq!(passage.generator_source_to_target_image.rows(), 4);
    assert_eq!(passage.generator_source_to_target_image.columns(), 3);
}

#[test]
fn image_passages_compose_through_the_exact_target_occurrence() {
    let family = vec![
        current(2, &[(0, 1), (1, 2), (2, 3)]),
        current(3, &[(0, 2), (1, 1), (2, 1)]),
    ];
    let generators = vec![vec![1, 2, 0], vec![0, 0, 2]];
    let foundation = FactoredMomentSection::found(3, family.clone()).expect("foundation");
    let first = foundation
        .section
        .transport_direct_sum(&generators)
        .expect("first image passage");
    let second = first
        .target
        .transport_direct_sum(&generators)
        .expect("second image passage");
    assert_eq!(first.target, second.source);
    assert_eq!(first.target_image_rank, second.source_image_rank);

    let receiver = FactoredIntegralReceiverForm::new(
        3,
        [FactoredIntegralReceiverTerm {
            coefficient: BigInt::from(1),
            left: functional(&[(0, 1), (1, -1)]),
            right: functional(&[(1, 1), (2, 2)]),
        }],
    )
    .expect("receiver");
    let mut twice_transported = Vec::new();
    for first_generator in &generators {
        for second_generator in &generators {
            for source in &family {
                let mut first_current = vec![BigInt::zero(); 3];
                for (factor, coefficient) in &source.entries {
                    first_current[first_generator[*factor as usize] as usize] +=
                        BigInt::from(coefficient.clone());
                }
                let mut second_current = vec![BigInt::zero(); 3];
                for (factor, coefficient) in first_current.into_iter().enumerate() {
                    second_current[second_generator[factor] as usize] += coefficient;
                }
                twice_transported.push((BigInt::from(source.weight.clone()), second_current));
            }
        }
    }
    let direct = receiver
        .contract_rank_one_family(&twice_transported)
        .expect("direct two-step contraction");
    assert_eq!(
        second
            .target
            .contract_receiver(&receiver)
            .expect("two-step image contraction"),
        Rat::from_integer(direct)
    );
}

#[test]
fn rooted_constitutive_spine_commutes_with_ordered_plural_transport() {
    let family = vec![
        current(2, &[(0, 1), (1, 2), (2, 3)]),
        current(3, &[(0, 2), (1, 1), (2, 1)]),
    ];
    let generators = vec![vec![1, 2, 0], vec![0, 0, 2]];
    let foundation = FactoredMomentSection::found(3, family).expect("foundation");
    let root = FactoredConstitutiveSpine::found(&foundation.section).expect("root spine");
    assert!(
        root.agrees_with(&foundation.section)
            .expect("root equality")
    );

    let first_passage = foundation
        .section
        .transport_direct_sum(&generators)
        .expect("first compact passage");
    let first_spine = root
        .transport_direct_sum(&generators)
        .expect("first rooted passage");
    assert_eq!(first_spine.root_rank, foundation.section.image_rank);
    assert_eq!(first_spine.history_population, 2);
    assert!(
        first_spine
            .agrees_with(&first_passage.target)
            .expect("first chart equality")
    );

    let second_passage = first_passage
        .target
        .transport_direct_sum(&generators)
        .expect("second compact passage");
    let second_spine = first_spine
        .transport_direct_sum(&generators)
        .expect("second rooted passage");
    assert_eq!(second_spine.root_rank, foundation.section.image_rank);
    assert_eq!(second_spine.history_population, 4);
    assert!(
        second_spine
            .agrees_with(&second_passage.target)
            .expect("second chart equality")
    );
}

#[test]
fn equal_complete_history_blocks_descend_with_multiplicity_and_reconstruction_fibre() {
    let foundation = FactoredMomentSection::found(
        3,
        vec![current(2, &[(0, 1), (1, 2)]), current(3, &[(1, 1), (2, 1)])],
    )
    .expect("foundation");
    let repeated_generator = vec![1, 2, 0];
    let generators = vec![repeated_generator.clone(), repeated_generator];
    let compact = foundation
        .section
        .transport_direct_sum(&generators)
        .expect("compact direct sum");
    let descended = FactoredConstitutiveSpine::found(&foundation.section)
        .expect("root")
        .transport_direct_sum(&generators)
        .expect("exact history descent");

    assert_eq!(descended.history_population, 1);
    assert_eq!(descended.history_weights, vec![BigUint::from(2_u32)]);
    assert_eq!(descended.reconstruction_fibre.len(), 1);
    assert_eq!(
        descended.reconstruction_fibre[0].candidate_to_target,
        vec![0, 0]
    );
    assert!(
        descended
            .agrees_with(&compact.target)
            .expect("weighted descended moment")
    );
}

#[test]
fn canonical_section_exposes_integral_cross_moments_for_resident_mount() {
    let foundation = FactoredMomentSection::found(
        3,
        vec![current(2, &[(0, 1), (1, 2)]), current(3, &[(1, 1), (2, 1)])],
    )
    .expect("foundation");
    let integral = foundation
        .section
        .integral_incidence()
        .expect("integral chart");
    assert_eq!(integral.len(), foundation.section.image_rank as usize);
    assert!(integral.iter().all(|row| row.len() == 3));
}

#[test]
fn diagonal_chronology_equals_the_enumerated_suffix_moment() {
    let steps = vec![
        AddressedDiagonalCurrentStep {
            source_state: 0,
            target_state: 0,
            entries: vec![
                (0, BigUint::from(2_u8)),
                (1, BigUint::from(3_u8)),
                (2, BigUint::from(5_u8)),
            ],
        },
        AddressedDiagonalCurrentStep {
            source_state: 0,
            target_state: 0,
            entries: vec![
                (0, BigUint::from(7_u8)),
                (1, BigUint::from(11_u8)),
                (2, BigUint::from(13_u8)),
            ],
        },
        AddressedDiagonalCurrentStep {
            source_state: 0,
            target_state: 0,
            entries: vec![
                (0, BigUint::from(17_u8)),
                (1, BigUint::from(19_u8)),
                (2, BigUint::from(23_u8)),
            ],
        },
    ];
    let generators = vec![vec![1, 2, 0], vec![0, 0, 2]];
    let action = SparseQuadraticMomentAction::complete_symmetric(3, generators.clone())
        .expect("complete pair carrier");
    let recurrent = SparseQuadraticMomentSection::from_diagonal_chronology(&action, &steps)
        .expect("local chronology moment");

    let mut live = Vec::<Vec<BigUint>>::new();
    let mut enumerated = Vec::<WeightedIntegralCurrent>::new();
    for step in &steps {
        let diagonal = step
            .entries
            .iter()
            .map(|(_, coefficient)| coefficient.clone())
            .collect::<Vec<_>>();
        for suffix in &mut live {
            for (coordinate, coefficient) in suffix.iter_mut().zip(&diagonal) {
                *coordinate *= coefficient;
            }
        }
        live.push(diagonal);
        enumerated.extend(live.iter().map(|suffix| {
            WeightedIntegralCurrent {
                weight: BigUint::one(),
                entries: suffix
                    .iter()
                    .cloned()
                    .enumerate()
                    .map(|(factor, coefficient)| (factor as u32, coefficient))
                    .collect(),
            }
        }));
    }
    let explicit = SparseQuadraticMomentFoundation::found(3, enumerated, generators)
        .expect("enumerated suffix moment");
    assert_eq!(recurrent, explicit.section);
    assert_eq!(action, explicit.action);
}

#[test]
fn section_admission_rejects_false_basis_and_constitutive_certificates() {
    let foundation = FactoredMomentSection::found(
        3,
        vec![current(2, &[(0, 1), (1, 2)]), current(3, &[(1, 1), (2, 1)])],
    )
    .expect("foundation");
    assert_eq!(foundation.section.image_rank, 2);

    let mut duplicate = foundation.section.clone();
    duplicate.basis_factors = vec![0, 0];
    assert_eq!(
        duplicate.validate_admitted(),
        Err(FactoredMomentError::Shape)
    );

    let mut outside = foundation.section.clone();
    outside.basis_factors = vec![0, outside.factor_population];
    assert_eq!(outside.validate_admitted(), Err(FactoredMomentError::Shape));

    let mut asymmetric = foundation.section.clone();
    let mut rows = asymmetric.constitutive.to_rows();
    rows[0][1] += Rat::one();
    asymmetric.constitutive = ExactRatMatrix::new(rows).expect("asymmetric square form");
    assert_eq!(
        asymmetric.validate_admitted(),
        Err(FactoredMomentError::Reconstruction)
    );

    let mut dependent = foundation.section.clone();
    let first = dependent.basis_factors[0] as usize;
    let second = dependent.basis_factors[1] as usize;
    let mut rows = dependent.incidence.to_rows();
    for row in &mut rows {
        row[second] = row[first].clone();
    }
    dependent.incidence = ExactRatMatrix::new(rows).expect("dependent incidence");
    assert!(matches!(
        dependent.validate_admitted(),
        Err(FactoredMomentError::Linear(_))
    ));
}
