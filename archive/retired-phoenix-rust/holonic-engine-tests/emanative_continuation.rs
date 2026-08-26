//! Exterior guards for the E0 addressed continuation rest.

use holonic_engine::cultivated_rest::{
    PredecessorProductIdentity, RuntimeChart, RuntimeLawReceipt,
};
use holonic_engine::exact_work::ExactWork;
use holonic_engine::phoenix::continuation::CultivatedBodyIdentity;
use holonic_engine::phoenix::emanative::{
    EMANATIVE_REST_SCHEMA, EmanativeCandidate, EmanativeContinuationRest, EmanativeFront,
    EmanativeOccurrence, EmanativePotential, EmanativeStatus, ExactBoundarySelection,
};

fn body() -> CultivatedBodyIdentity {
    CultivatedBodyIdentity::new(
        PredecessorProductIdentity::from_bytes(b"product"),
        PredecessorProductIdentity::from_bytes(b"predecessor"),
        PredecessorProductIdentity::from_bytes(b"morphology"),
        Vec::new(),
        &RuntimeLawReceipt {
            schema: "holonic-engine.phoenix.runtime-law.v1".to_owned(),
            grain: 1,
            series_aperture: 1,
            band_terms: 1,
            vocabulary_extent: 3,
            hidden_extent: 2,
            rank: 1,
            left_population: "left".to_owned(),
            right_population: "right".to_owned(),
            chart: RuntimeChart::Interval,
            fuse: false,
            add_special_tokens: false,
        },
    )
    .expect("synthetic cultivated body identity")
}

fn valid_rest() -> EmanativeContinuationRest {
    let entering =
        EmanativeOccurrence::found(None, vec![1], "x".to_owned()).expect("entering occurrence");
    let selected = EmanativeCandidate {
        native_id: 2,
        surface: " y".to_owned(),
        lower: 9,
        upper: 10,
    };
    let potential = EmanativePotential::found(3, 1, 9, vec![selected], 2).expect("exact future");
    let after = EmanativeOccurrence::found(
        Some(entering.address_sha256.clone()),
        vec![1, 2],
        "x y".to_owned(),
    )
    .expect("successor occurrence");
    let entering_address = entering.address_sha256.clone();
    EmanativeContinuationRest {
        schema: EMANATIVE_REST_SCHEMA.to_owned(),
        body: body(),
        cultivation_continuation: None,
        factor_complex: None,
        predecessor_rest_sha256: None,
        entering,
        fronts: vec![EmanativeFront {
            index: 0,
            before_address_sha256: entering_address,
            after: Some(after),
            potential,
            selection: Some(ExactBoundarySelection {
                law: "exact-singleton-maximizer-fibre".to_owned(),
                selected_native_id: 2,
            }),
            semantic_receipt_sha256: format!("{:064x}", 11),
            exact_work: ExactWork::nothing(),
        }],
        codec_identity: "codec".to_owned(),
        status: EmanativeStatus::FrontierAperture {
            conducted_fronts: 1,
        },
        open_exterior: vec!["richer successor histories".to_owned()],
    }
}

#[test]
fn the_rest_reconstructs_its_addressed_word_and_refuses_lineage_tampering() {
    let rest = valid_rest();
    let bytes = rest.canonical_bytes().expect("canonical rest");
    assert_eq!(
        EmanativeContinuationRest::read(&bytes).expect("detached remount"),
        rest
    );

    let mut tampered = rest;
    tampered.fronts[0]
        .after
        .as_mut()
        .expect("successor")
        .predecessor_address_sha256 = Some(format!("{:064x}", 99));
    assert!(tampered.canonical_bytes().is_err());
}

#[test]
fn equal_codec_faces_under_distinct_predecessors_are_distinct_occurrences() {
    let first =
        EmanativeOccurrence::found(Some(format!("{:064x}", 1)), vec![1, 2], "same".to_owned())
            .expect("first occurrence");
    let second =
        EmanativeOccurrence::found(Some(format!("{:064x}", 2)), vec![1, 2], "same".to_owned())
            .expect("second occurrence");
    assert_ne!(first.address_sha256, second.address_sha256);
}
