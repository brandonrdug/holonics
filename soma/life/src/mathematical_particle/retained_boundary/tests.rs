use holonic_engine::receiver_exact_compression::{compress, Observation};
use sha2::{Digest, Sha256};

use super::{
    AddressedHistorySystem, CultivatedActionLineage, HistoricalInterior, LongHorizonBoundaryError,
    LongHorizonRetainedBoundary,
};

fn digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

fn interior(name: &str, predecessor: Option<&str>, payload: &[u8]) -> HistoricalInterior {
    HistoricalInterior {
        occurrence: name.to_owned(),
        predecessor: predecessor.map(str::to_owned),
        payload_sha256: digest(payload),
        payload: payload.to_vec(),
    }
}

fn fixture() -> LongHorizonRetainedBoundary {
    let system = AddressedHistorySystem::found(
        3,
        3,
        vec![0, 0, 2, 2, 0, 2],
        vec![
            vec![Observation(0), Observation(0), Observation(1)],
            vec![Observation(7), Observation(7), Observation(9)],
        ],
    )
    .expect("system");
    let exact = compress(&system);
    assert!(!exact.collapsed.is_empty());
    LongHorizonRetainedBoundary::found(
        digest(b"predecessor"),
        digest(b"boundary"),
        vec![
            interior("root", None, b"remote construction"),
            interior("later", Some("root"), b"later proof"),
            interior("diagram", None, b"diagram incidence"),
        ],
        &system,
        &exact,
        CultivatedActionLineage {
            dynamic_rest_sha256: digest(b"rest"),
            predecessor_action_sha256: digest(b"before"),
            successor_action_sha256: digest(b"after"),
            returned_occurrences: vec!["world-return".to_owned()],
            commutator_rank: 1,
        },
    )
    .expect("retained boundary")
}

#[test]
fn every_future_factors_while_the_richer_receiver_reopens_the_interior() {
    let boundary = fixture();
    assert_eq!(boundary.standing.native_states.len(), 3);
    assert_eq!(boundary.fibres.fibres.len(), 3);
    assert!(!boundary.fibres.shortest_separators.is_empty());
    assert_eq!(boundary.standing.ordered_holonomy.left_endpoint.0, 2);
    assert_eq!(boundary.standing.ordered_holonomy.right_endpoint.0, 0);
    let reconstructed = boundary
        .reconstruct_history("later")
        .expect("the remote predecessor reopens");
    assert!(reconstructed
        .windows(19)
        .any(|window| window == b"remote construction"));
    assert!(reconstructed
        .windows(11)
        .any(|window| window == b"later proof"));

    let standing = boundary.standing_bytes().expect("standing");
    let decoder = boundary.decoder_bytes().expect("decoder");
    let fibres = boundary.fibre_bytes().expect("fibres");
    let remounted = LongHorizonRetainedBoundary::read(&standing, &decoder, &fibres)
        .expect("three components remount");
    assert_eq!(remounted, boundary);
}

#[test]
fn a_changed_historical_payload_refuses_source_detached_remount() {
    let boundary = fixture();
    let standing = boundary.standing_bytes().expect("standing");
    let mut decoder: serde_json::Value =
        serde_json::from_slice(&boundary.decoder_bytes().expect("decoder")).expect("json");
    decoder["interiors"][0]["payload"][0] = serde_json::json!(0);
    let fibres = boundary.fibre_bytes().expect("fibres");
    assert_eq!(
        LongHorizonRetainedBoundary::read(
            &standing,
            &serde_json::to_vec(&decoder).expect("bytes"),
            &fibres,
        ),
        Err(LongHorizonBoundaryError::Decoder)
    );
}
