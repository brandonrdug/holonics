#[cfg(test)]
mod tests {
    use super::*;

    fn two_factor_action() -> GranularFactorAction {
        GranularFactorAction {
            native_states: vec![NativeStateId(10), NativeStateId(20)],
            receiver_factors: vec![
                vec![GranularFactorReceiver {
                    receiver: ReceiverId(0),
                    observation: Observation(10),
                }],
                vec![GranularFactorReceiver {
                    receiver: ReceiverId(0),
                    observation: Observation(20),
                }],
            ],
            generators: vec![GranularFactorGenerator {
                generator: InputId(0),
                targets: vec![1, 0],
                source_square_identity_sha256: "11".repeat(32),
            }],
            source_action_identity_sha256: "22".repeat(32),
        }
    }

    fn conditioned() -> NativeGranularPotential {
        let addresses = vec!["factor-a".to_owned(), "factor-b".to_owned()];
        let mut builder =
            NativeGranularPotentialBuilder::new(&addresses, two_factor_action()).unwrap();
        builder
            .receive_world_tube(
                0,
                [
                    ("occurrence-a", b"alpha beta".as_slice()),
                    ("occurrence-a-return", b"beta returns".as_slice()),
                ],
            )
            .unwrap();
        builder
            .receive_world_tube(
                1,
                [
                    ("occurrence-b", b"alpha gamma".as_slice()),
                    ("occurrence-b-return", b"gamma returns".as_slice()),
                ],
            )
            .unwrap();
        builder.finish().unwrap()
    }

    #[test]
    fn exterior_path_returns_plural_boundary_without_word_states() {
        let rest = conditioned();
        assert!(rest.boundary_port_population() <= port_population() + 1);
        let returned = rest.mount().unwrap().receive_open(b"alpha ").unwrap();
        let octets = returned
            .branches
            .iter()
            .map(|branch| branch.port.clone())
            .collect::<BTreeSet<_>>();
        assert!(octets.contains(&GranularExteriorPort::Octet(b'b')));
        assert!(octets.contains(&GranularExteriorPort::Octet(b'g')));
        assert!(
            returned
                .branches
                .iter()
                .all(|branch| !branch.target_states.is_empty()
                    && !branch.context_states.is_empty()
                    && !branch.reconstruction_nodes.is_empty()
                    && branch.reconstruction_path_population != BigUint::from(0_u8))
        );
    }

    #[test]
    fn plural_distinct_ports_return_as_one_quotiented_higher_current() {
        let rest = conditioned();
        let mounted = rest.mount().unwrap();
        let prior = mounted.receive_open(b"alpha ").unwrap();
        let prior_context_population = prior.current.contexts.len();
        let prior_active_node_population = prior
            .current
            .contexts
            .iter()
            .map(|context| context.reconstruction_nodes.len())
            .sum::<usize>();
        let returned = prior
            .branches
            .iter()
            .filter(|branch| {
                matches!(
                    branch.port,
                    GranularExteriorPort::Octet(b'b') | GranularExteriorPort::Octet(b'g')
                )
            })
            .map(|branch| GranularHigherBoundaryFace {
                port: branch.port.clone(),
                generator: branch.generator,
            })
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        assert_eq!(returned.len(), 2);
        let carried = mounted.carry_returned_faces(prior, &returned).unwrap();
        let active_nodes = carried
            .current
            .contexts
            .iter()
            .flat_map(|context| &context.reconstruction_nodes)
            .filter_map(|node| carried.current.reconstruction_nodes.get(*node as usize))
            .collect::<Vec<_>>();
        let reconstructed = active_nodes
            .iter()
            .flat_map(|node| &node.incoming)
            .flat_map(|edge| &edge.returned_higher_faces)
            .cloned()
            .collect::<BTreeSet<_>>();
        assert_eq!(reconstructed, returned.into_iter().collect());
        assert!(!carried.current.contexts.is_empty());
        assert_eq!(carried.current.boundary_front, vec![0]);
        assert!(
            carried
                .current
                .contexts
                .iter()
                .all(|context| context.state == 0)
        );
        assert!(carried.current.contexts.len() <= prior_context_population);
        assert!(active_nodes.len() <= prior_active_node_population);
        assert!(
            active_nodes
                .iter()
                .all(|node| node.incoming.iter().all(|edge| {
                    edge.entering_port.is_none() && edge.returned_higher_faces.len() == 2
                }))
        );
    }

    #[test]
    fn fine_path_differences_change_the_returned_boundary() {
        let rest = conditioned();
        let mounted = rest.mount().unwrap();
        let beta = mounted.receive_open(b"alpha b").unwrap();
        let gamma = mounted.receive_open(b"alpha g").unwrap();
        assert_eq!(beta.reached_state, 0);
        assert_eq!(gamma.reached_state, 0);
        assert_ne!(beta.branches, gamma.branches);
        assert!(
            beta.branches
                .iter()
                .any(|branch| branch.port == GranularExteriorPort::Octet(b'e'))
        );
        assert!(
            gamma
                .branches
                .iter()
                .any(|branch| branch.port == GranularExteriorPort::Octet(b'a'))
        );
    }

    #[test]
    fn occurrence_closure_returns_the_caused_opening_of_its_later_world_tube() {
        let rest = conditioned();
        let mounted = rest.mount().unwrap();
        let beta = mounted.receive_closed(b"alpha beta").unwrap();
        assert!(
            beta.branches
                .iter()
                .any(|branch| branch.port == GranularExteriorPort::Opening)
        );
        let opened = mounted
            .carry_port(&beta, GranularExteriorPort::Opening)
            .unwrap();
        assert!(
            opened
                .branches
                .iter()
                .any(|branch| branch.port == GranularExteriorPort::Octet(b'b'))
        );
    }

    #[test]
    fn source_neutral_projective_ingress_retains_terminal_quotient_and_compact_chronology() {
        let rest = conditioned();
        let mounted = rest.mount().unwrap();
        let projective = rest
            .cross_exterior_projective_current("held-out/state-history", b"alpha beta")
            .unwrap()
            .native;
        let (returned, crossed) = mounted
            .receive_native_projective_returning(&projective)
            .unwrap();
        assert_eq!(
            crossed,
            vec![GranularExteriorPort::Opening, GranularExteriorPort::Closure]
        );
        assert_eq!(returned.current.contexts.len(), projective.contexts.len());
        for (at, context) in returned.current.contexts.iter().enumerate() {
            let expected = &projective.contexts[at];
            assert_eq!(
                (
                    context.state,
                    &context.factor_current,
                    &context.quadratic_weight
                ),
                (
                    expected.boundary_state,
                    &expected.factor_current,
                    &expected.quadratic_weight,
                ),
            );
            assert_eq!(context.reconstruction_nodes, expected.reconstruction_nodes);
        }
        assert!(returned.current.contexts.iter().all(|context| {
            !context.factor_current.is_empty() && !context.reconstruction_nodes.is_empty()
        }));
        assert_eq!(
            returned
                .current
                .contexts
                .iter()
                .flat_map(|context| context.reconstruction_nodes.iter().copied())
                .collect::<BTreeSet<_>>(),
            projective
                .contexts
                .iter()
                .flat_map(|context| context.reconstruction_nodes.iter().copied())
                .collect(),
        );
        assert_eq!(
            returned.current.reconstruction_nodes,
            projective.reconstruction_nodes
        );
        assert_eq!(
            projective.diagonal_chronology.len() as u64,
            projective.entered_octet_population + 2
        );
        assert_eq!(returned.current.boundary_front, projective.boundary_front);
    }

    #[test]
    fn rest_remount_preserves_exact_boundary_without_source_payload() {
        let rest = conditioned();
        let before = rest.mount().unwrap().receive_open(b"alpha ").unwrap();
        let wire = serde_json::to_vec(&rest).unwrap();
        assert!(
            !wire
                .windows(b"alpha beta".len())
                .any(|window| window == b"alpha beta")
        );
        assert!(
            !wire
                .windows(b"alpha gamma".len())
                .any(|window| window == b"alpha gamma")
        );
        let remounted: NativeGranularPotential = serde_json::from_slice(&wire).unwrap();
        remounted.validate().unwrap();
        let after = remounted.mount().unwrap().receive_open(b"alpha ").unwrap();
        assert_eq!(before, after);
        assert_eq!(rest.identity(), remounted.identity());
    }

    #[test]
    fn hot_wire_and_identity_exclude_developmental_source_identity() {
        let rest = conditioned();
        assert!(rest.factor_faces().iter().all(factor_face_is_native));
        let wire = rest.canonical_bytes().unwrap();
        for forbidden in [
            b"source_action_identity_sha256".as_slice(),
            b"source_square_identity_sha256".as_slice(),
            b"occurrence_identity_sha256".as_slice(),
            b"occurrence-a".as_slice(),
            b"alpha beta".as_slice(),
        ] {
            assert!(
                !wire
                    .windows(forbidden.len())
                    .any(|window| window == forbidden)
            );
        }

        let mut changed_action = two_factor_action();
        changed_action.source_action_identity_sha256 = "ee".repeat(32);
        changed_action.generators[0].source_square_identity_sha256 = "ff".repeat(32);
        let addresses = vec!["factor-a".to_owned(), "factor-b".to_owned()];
        let mut changed_builder =
            NativeGranularPotentialBuilder::new(&addresses, changed_action).unwrap();
        changed_builder
            .receive_world_tube(
                0,
                [
                    ("renamed-a", b"alpha beta".as_slice()),
                    ("renamed-a-return", b"beta returns".as_slice()),
                ],
            )
            .unwrap();
        changed_builder
            .receive_world_tube(
                1,
                [
                    ("renamed-b", b"alpha gamma".as_slice()),
                    ("renamed-b-return", b"gamma returns".as_slice()),
                ],
            )
            .unwrap();
        let changed_rest = changed_builder.finish().unwrap();
        assert_eq!(changed_rest.identity(), rest.identity());
        assert_eq!(changed_rest.canonical_bytes().unwrap(), wire);
    }

    #[test]
    fn duplicated_developmental_scale_does_not_duplicate_the_hot_native_population() {
        let addresses = vec!["factor-a".to_owned(), "factor-b".to_owned()];
        let mut single =
            NativeGranularPotentialBuilder::new(&addresses, two_factor_action()).unwrap();
        single
            .receive_world_tube(0, [("single-a", b"alpha beta".as_slice())])
            .unwrap();
        single
            .receive_world_tube(1, [("single-b", b"alpha gamma".as_slice())])
            .unwrap();
        let single = single.finish().unwrap();

        let mut doubled =
            NativeGranularPotentialBuilder::new(&addresses, two_factor_action()).unwrap();
        doubled
            .receive_world_tube(0, [("double-a/0", b"alpha beta".as_slice())])
            .unwrap();
        doubled
            .receive_world_tube(0, [("double-a/1", b"alpha beta".as_slice())])
            .unwrap();
        doubled
            .receive_world_tube(1, [("double-b/0", b"alpha gamma".as_slice())])
            .unwrap();
        doubled
            .receive_world_tube(1, [("double-b/1", b"alpha gamma".as_slice())])
            .unwrap();
        let doubled = doubled.finish().unwrap();

        assert_eq!(single.factor_faces.len(), doubled.factor_faces.len());
        assert_eq!(
            single.factor_generators.len(),
            doubled.factor_generators.len()
        );
        assert_eq!(single.supports.len(), doubled.supports.len());
        assert_eq!(single.states.len(), doubled.states.len());
        assert_eq!(
            single
                .states
                .iter()
                .map(|state| state.transitions.len())
                .collect::<Vec<_>>(),
            doubled
                .states
                .iter()
                .map(|state| state.transitions.len())
                .collect::<Vec<_>>()
        );
        let single_current = single
            .cross_exterior_projective_current("held-out/single", b"alpha")
            .unwrap()
            .native;
        let doubled_current = doubled
            .cross_exterior_projective_current("held-out/doubled", b"alpha")
            .unwrap()
            .native;
        assert_eq!(
            single_current.boundary_front,
            doubled_current.boundary_front
        );
        assert_eq!(single_current.contexts, doubled_current.contexts);
        assert_eq!(
            single_current.diagonal_chronology,
            doubled_current.diagonal_chronology
        );
        assert_eq!(
            single_current.integrated_factor_current,
            doubled_current.integrated_factor_current
        );
    }

    #[test]
    fn generator_squares_compose_without_collapsing_ordered_successor_words() {
        let action = GranularFactorAction {
            native_states: vec![NativeStateId(0), NativeStateId(1), NativeStateId(2)],
            receiver_factors: (0..3)
                .map(|state| {
                    vec![GranularFactorReceiver {
                        receiver: ReceiverId(0),
                        observation: Observation(state),
                    }]
                })
                .collect(),
            generators: vec![
                GranularFactorGenerator {
                    generator: InputId(0),
                    targets: vec![1, 2, 0],
                    source_square_identity_sha256: "33".repeat(32),
                },
                GranularFactorGenerator {
                    generator: InputId(1),
                    targets: vec![2, 0, 1],
                    source_square_identity_sha256: "44".repeat(32),
                },
            ],
            source_action_identity_sha256: "55".repeat(32),
        };
        action.validate().unwrap();
        let native_generators = action
            .generators
            .iter()
            .map(|generator| NativeGranularFactorGenerator {
                generator: generator.generator,
                targets: generator.targets.clone(),
            })
            .collect::<Vec<_>>();
        let current = vec![
            GranularFactorCurrent {
                factor: 0,
                incidence: BigUint::from(2_u8),
            },
            GranularFactorCurrent {
                factor: 1,
                incidence: BigUint::from(1_u8),
            },
        ];
        let (first, first_scale) =
            apply_generator_current(&current, &native_generators[0]).unwrap();
        assert_eq!(first_scale, BigUint::from(1_u8));
        assert_eq!(
            first,
            vec![
                GranularFactorCurrent {
                    factor: 1,
                    incidence: BigUint::from(2_u8),
                },
                GranularFactorCurrent {
                    factor: 2,
                    incidence: BigUint::from(1_u8),
                },
            ]
        );
        let (difference, difference_scale) =
            generator_action_difference(&current, &native_generators[0]).unwrap();
        assert_eq!(difference_scale, BigUint::from(1_u8));
        assert_eq!(
            difference,
            vec![
                GranularSignedFactorCurrent {
                    factor: 0,
                    coefficient: BigInt::from(-2_i8),
                },
                GranularSignedFactorCurrent {
                    factor: 1,
                    coefficient: BigInt::from(1_i8),
                },
                GranularSignedFactorCurrent {
                    factor: 2,
                    coefficient: BigInt::from(1_i8),
                },
            ]
        );
        assert_eq!(
            receiver_action_current(
                &difference,
                &action
                    .native_states
                    .iter()
                    .enumerate()
                    .map(|(factor, native)| GranularFactorFace {
                        factor: factor as u32,
                        factor_address: format!("factor-{factor}"),
                        native: *native,
                        receiver_factors: action.receiver_factors[factor].clone(),
                        receiver_schema: FACTOR_FACE_SCHEMA,
                        receiver_words: vec![factor as u32],
                    })
                    .collect::<Vec<_>>(),
            )
            .unwrap(),
            vec![
                GranularReceiverActionCurrent {
                    receiver: ReceiverId(0),
                    observation: Observation(0),
                    coefficient: BigInt::from(-2_i8),
                },
                GranularReceiverActionCurrent {
                    receiver: ReceiverId(0),
                    observation: Observation(1),
                    coefficient: BigInt::from(1_i8),
                },
                GranularReceiverActionCurrent {
                    receiver: ReceiverId(0),
                    observation: Observation(2),
                    coefficient: BigInt::from(1_i8),
                },
            ]
        );
        let (second, second_scale) =
            apply_generator_current(&first, &native_generators[1]).unwrap();
        assert_eq!(second_scale, BigUint::from(1_u8));
        assert_eq!(
            second,
            vec![
                GranularFactorCurrent {
                    factor: 0,
                    incidence: BigUint::from(2_u8),
                },
                GranularFactorCurrent {
                    factor: 1,
                    incidence: BigUint::from(1_u8),
                },
            ]
        );
    }

    #[test]
    fn dynamic_moment_identifies_equal_covariance_not_equal_factorization() {
        let context = |weight: u8, coordinates: &[(u32, u8)]| GranularCausalContext {
            state: 0,
            factor_current: coordinates
                .iter()
                .map(|(factor, incidence)| GranularFactorCurrent {
                    factor: *factor,
                    incidence: BigUint::from(*incidence),
                })
                .collect(),
            quadratic_weight: BigUint::from(weight),
            reconstruction_nodes: vec![0],
        };
        let left = canonical_dynamic_moment(&[context(4, &[(0, 1), (1, 2)])], 3).unwrap();
        let equal = canonical_dynamic_moment(&[context(1, &[(0, 2), (1, 4)])], 3).unwrap();
        let same_first_face =
            canonical_dynamic_moment(&[context(1, &[(0, 2), (1, 1)])], 3).unwrap();
        let rescaled = canonical_dynamic_moment(&[context(1, &[(0, 1), (1, 2)])], 3).unwrap();

        assert_eq!(left, equal);
        assert_ne!(left, same_first_face);
        assert_ne!(left, rescaled);
        assert_eq!(left.rank, 1);
        assert_eq!(left.pivot_factors, vec![0]);
        assert_eq!(
            left.pivot_cross_moments,
            vec![BigUint::from(4_u8), BigUint::from(8_u8), BigUint::ZERO]
        );
    }
}
