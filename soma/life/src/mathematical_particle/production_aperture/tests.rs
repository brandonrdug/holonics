use std::fs;
use std::path::PathBuf;

use holonic_engine::phoenix::inference_ecology::InferenceEcologyRest;

use super::*;
use crate::mathematical_particle::{
    DynamicMorphologyRest, LongHorizonRetainedBoundary, MultimodalTransportRest,
};

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../..")
        .canonicalize()
        .expect("workspace root")
}

fn component_rest() -> ProductionAthenaRest {
    let root = root();
    let i5 = root.join("output/the_athena_gemma_ecology_infers_returns_and_remounts/native-rest");
    let inference = InferenceEcologyRest::read(
        &fs::read(i5.join("recurrent-standing.json")).expect("I5 recurrent standing"),
        &fs::read(i5.join("recurrent-decoder.json")).expect("I5 recurrent decoder"),
        &fs::read(i5.join("recurrent-fibres.json")).expect("I5 recurrent fibres"),
        &fs::read(i5.join("heterogeneous-standing.json")).expect("I5 heterogeneous standing"),
        &fs::read(i5.join("heterogeneous-decoder.json")).expect("I5 heterogeneous decoder"),
        &fs::read(i5.join("heterogeneous-fibres.json")).expect("I5 heterogeneous fibres"),
        &fs::read(i5.join("inference-junction.json")).expect("I5 junction"),
    )
    .expect("I5 rest");
    let morphology = DynamicMorphologyRest::read(
        &fs::read(root.join("output/the_returned_constraints_found_dynamic_local_morphology/04-source-detached-dynamic-morphology-rest.json"))
            .expect("R3 rest"),
    )
    .expect("R3 rest");
    let r4 = root
        .join("output/the_retained_causal_boundary_carries_the_long_horizon_inquiry/native-rest");
    let retained_boundary = LongHorizonRetainedBoundary::read(
        &fs::read(r4.join("standing.json")).expect("R4 standing"),
        &fs::read(r4.join("decoder.json")).expect("R4 decoder"),
        &fs::read(r4.join("fibres.json")).expect("R4 fibres"),
    )
    .expect("R4 rest");
    let r5 =
        root.join("output/the_mathematical_and_physical_faces_share_native_transport/native-rest");
    let media = MultimodalTransportRest::read(
        &fs::read(r5.join("standing.json")).expect("R5 standing"),
        &fs::read(r5.join("decoder.bin")).expect("R5 decoder"),
        &fs::read(r5.join("fibres.json")).expect("R5 fibres"),
    )
    .expect("R5 rest");
    ProductionAthenaRest::found(
        inference,
        morphology,
        retained_boundary,
        media,
        vec!["r6/development/control".to_owned()],
        "r6/decision/declined".to_owned(),
    )
    .expect("production rest")
}

#[test]
fn one_owner_round_trips_and_rejects_a_development_occurrence() {
    let rest = component_rest();
    let standing = rest.standing_bytes().expect("standing");
    let decoder = rest.decoder_bytes().expect("decoder");
    let fibres = rest.fibre_bytes().expect("fibres");
    let reopened = ProductionAthenaRest::read(&standing, &decoder, &fibres).expect("reopened");
    assert_eq!(reopened.standing_bytes().expect("standing"), standing);
    assert_eq!(reopened.decoder_bytes().expect("decoder"), decoder);
    assert_eq!(reopened.fibre_bytes().expect("fibres"), fibres);

    let inquiry = ProductionInquiry::found(
        reopened.canonical_identity().expect("identity"),
        ProductionInquiryPresentation {
            natural_language: "return the exact oriented raster difference".to_owned(),
            notation: "N_4-N_8".to_owned(),
            vector_face_sha256: format!("{:064x}", 1),
            raster_face_sha256: format!("{:064x}", 2),
            prior_history_occurrences: vec!["r4/history/heldout".to_owned()],
        },
        vec![0, 1],
        vec![
            ProductionReceiver::Language,
            ProductionReceiver::LeanProof,
            ProductionReceiver::ExactValue,
            ProductionReceiver::UnitDimension,
            ProductionReceiver::ExactVisual,
        ],
        ProductionInquiryFace {
            left_species: 2,
            right_species: 3,
            oriented_relation: "left-minus-right".to_owned(),
            carrier: "integer-incidence".to_owned(),
            unit: "dimensionless-correspondence".to_owned(),
            dimension: 0,
        },
        reopened.media.standing.heldout_family,
    )
    .expect("inquiry");
    reopened.admit_inquiry(&inquiry).expect("new inquiry");
}

#[test]
fn committed_return_changes_the_owner_and_withdrawal_restores_it_exactly() {
    let rest = component_rest();
    let predecessor = rest.canonical_identity().expect("predecessor");
    let committed = rest
        .commit_return(
            ProductionWorldReturn {
                occurrence: "r6/world/lean/accepted".to_owned(),
                emitted_product_sha256: format!("{:064x}", 11),
                returned_product_sha256: format!("{:064x}", 12),
                receiver: "Lean kernel".to_owned(),
                accepted: true,
                exact_difference_octets: 1,
            },
            "r6/decision/committed".to_owned(),
        )
        .expect("commit");
    assert_ne!(
        committed.canonical_identity().expect("committed"),
        predecessor
    );
    let (restored, receipt) = committed.withdraw().expect("withdraw");
    assert!(receipt.exact_predecessor_restored);
    assert_eq!(
        restored.canonical_identity().expect("restored"),
        predecessor
    );
}
