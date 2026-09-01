use super::*;

fn phase_population_one() -> Vec<SourceNeutralPhasePopulation> {
    vec![SourceNeutralPhasePopulation {
        factor: 0,
        phase: 0,
        occurrence_population: 1,
    }]
}

fn bounded_transport_fixture() -> (
    SourceNeutralExteriorRealizationMorphology,
    SourceNeutralRelationalMorphology,
    SourceNeutralExteriorSiteHistoryQuotient,
) {
    let face = |address: &str| SourceNeutralRelationalFace {
        address: address.to_owned(),
        factor_support: vec![0],
        phase_population: phase_population_one(),
        cell_incidence: Vec::new(),
    };
    let relational = SourceNeutralRelationalMorphology {
        schema: String::new(),
        factor_population: 1,
        factor_adjacency: Vec::new(),
        faces: vec![face("face-0"), face("face-1")],
        cells: vec![SourceNeutralRelationalCell {
            address: "cell-0".to_owned(),
            oriented_boundary: vec![0, 1, 0],
            factor_support: vec![0],
            phase_population: phase_population_one(),
        }],
        obstructed_delivery_population: 0,
        identity_sha256: String::new(),
    };
    let morphology = SourceNeutralExteriorRealizationMorphology {
        schema: String::new(),
        relational_identity_sha256: String::new(),
        face_population: 2,
        cell_population: 1,
        sites: vec![
            SourceNeutralExteriorRealizationSite {
                face: 0,
                cell: 0,
                boundary_position: 0,
                incidence_population: 1,
                successor_site: Some(1),
            },
            SourceNeutralExteriorRealizationSite {
                face: 1,
                cell: 0,
                boundary_position: 1,
                incidence_population: 1,
                successor_site: None,
            },
        ],
        factor_population: 1,
        face_root_states: vec![0, 1],
        presentation_roots: vec![(0, 0), (1, 1)],
        realization_state_population: 5,
        transitions: vec![
            SourceNeutralExteriorRealizationTransition {
                face: 0,
                state: 0,
                source: 1,
                target: 2,
                target_state: Some(2),
                occurrence_population: 1,
            },
            SourceNeutralExteriorRealizationTransition {
                face: 0,
                state: 0,
                source: 1,
                target: 3,
                target_state: Some(3),
                occurrence_population: 1,
            },
            SourceNeutralExteriorRealizationTransition {
                face: 1,
                state: 1,
                source: 1,
                target: 4,
                target_state: Some(4),
                occurrence_population: 1,
            },
        ],
        developmental_transition_population: 3,
        identity_sha256: String::new(),
    };
    let quotient = SourceNeutralExteriorSiteHistoryQuotient {
        site_to_class: vec![0, 1],
        representatives: vec![0, 1],
        fibres: vec![vec![0], vec![1]],
        carrier_addresses: BTreeMap::from([((0, 0, 0), 0), ((1, 0, 0), 1)]),
        carrier_representatives: vec![(0, 0, 0), (1, 0, 0)],
        carrier_fibres: vec![vec![(0, 0, 0)], vec![(1, 0, 0)]],
        identity_sha256: String::new(),
    };
    (morphology, relational, quotient)
}

#[test]
fn ordinary_port_law_retains_diagonal_and_off_diagonal_pair_fibres() {
    let (morphology, relational, quotient) = bounded_transport_fixture();
    let source_currents = vec![
        SourceNeutralExteriorRealizationComplexSiteCurrent {
            carrier: 0,
            site: 0,
            factor: 0,
            phase: 0,
            local_source_port: 1,
            realization_state: Some(0),
            incidence_coefficient: Ratio::one(),
        },
        SourceNeutralExteriorRealizationComplexSiteCurrent {
            carrier: 1,
            site: 1,
            factor: 0,
            phase: 0,
            local_source_port: 1,
            realization_state: Some(1),
            incidence_coefficient: Ratio::one(),
        },
    ];
    let (contributions, obstructions) = morphology
        .complex_site_transport_contributions(&relational, &quotient, &source_currents)
        .expect("the oriented ordinary port law returns");
    assert!(obstructions.is_empty());
    assert!(contributions.iter().any(|current| {
        current.source_carrier == 0
            && current.source_site == 0
            && current.target_carrier == 1
            && current.target_site == 1
    }));
    assert!(contributions.iter().any(|current| {
        current.source_carrier == 1
            && current.source_site == 1
            && current.target_carrier == 1
            && current.target_site == 1
    }));
    for source in [0_u32, 1] {
        let returned = contributions
            .iter()
            .filter(|current| current.source_carrier == source)
            .fold(Ratio::zero(), |sum, current| {
                sum + &current.incidence_coefficient
            });
        assert_eq!(returned, Ratio::one());
    }

    let response = SourceNeutralAddressedResponsePairCurrent {
        response_face: 5,
        native_port: 7,
        native_generator: 11,
        source_section: 13,
        selected_slot: 17,
        target_section: 19,
        factor: 0,
        current: ExactComplexWaveCurrent::one(),
    };
    let oriented = vec![SourceNeutralExteriorRealizationOrientedFactorCurrent {
        factor: 0,
        current: ExactComplexWaveCurrent::one(),
        pair_currents: vec![response.clone()],
        ingress_face_currents: Vec::new(),
    }];
    assert_eq!(oriented[0].pair_currents, vec![response]);
    let realized = contributions
        .iter()
        .map(|contribution| {
            let coefficient = Ratio::new(
                BigInt::from(contribution.incidence_coefficient.numer().clone()),
                BigInt::from(contribution.incidence_coefficient.denom().clone()),
            );
            oriented[0].current.scaled(&coefficient)
        })
        .collect::<Vec<_>>();
    assert_eq!(realized.len(), contributions.len());
    assert!(realized.iter().all(|current| !current.is_zero()));
}
