//! Exterior regression guard for the third inherited source port.
//!
//! Test material stays outside the protected production-owner census. The production change is
//! only the typed `AudioFrame` port; the existing heterogeneous fusion law remains its owner.

use holonic_engine::phoenix::heterogeneous_fusion::{
    HeterogeneousFusionRest, ModalityPort, PortDeclaration, SharedWorldGenerator,
    SourcePortResponse,
};

fn sha(value: u32) -> String {
    format!("{value:064x}")
}

#[test]
fn the_same_owner_admits_an_audio_port_without_changing_the_fusion_law() {
    let ports = [
        ModalityPort::TextCodeword,
        ModalityPort::VisionPatch,
        ModalityPort::AudioFrame,
    ];
    let responses = (0..2)
        .flat_map(|family| {
            ports.into_iter().flat_map(move |port| {
                (0..2).map(move |state| {
                    let mark = 1 + family * 6 + (port as u32) * 2 + state;
                    SourcePortResponse {
                        family,
                        state,
                        port,
                        occurrence: format!("family-{family}/state-{state}/{port:?}"),
                        occurrence_sha256: sha(mark),
                        consequence_sha256: sha(mark + 32),
                        incidence_sha256: sha(mark + 64),
                        semantic_units: 1,
                    }
                })
            })
        })
        .collect();
    let rest = HeterogeneousFusionRest::found(
        sha(42),
        vec![
            PortDeclaration {
                port: ModalityPort::TextCodeword,
                boundary: "ordered codewords".to_owned(),
                source_population: "text".to_owned(),
                width: 8,
                incidence: "serial".to_owned(),
            },
            PortDeclaration {
                port: ModalityPort::VisionPatch,
                boundary: "patches".to_owned(),
                source_population: "vision".to_owned(),
                width: 3,
                incidence: "planar".to_owned(),
            },
            PortDeclaration {
                port: ModalityPort::AudioFrame,
                boundary: "exact PCM frames".to_owned(),
                source_population: "audio".to_owned(),
                width: 5,
                incidence: "sample and frame chronology".to_owned(),
            },
        ],
        responses,
        SharedWorldGenerator {
            name: "g".to_owned(),
            predecessor: 0,
            successor: 1,
            lineage: "one caused passage".to_owned(),
            common_world_receiver: "declared before conduct".to_owned(),
        },
        Vec::new(),
        vec!["broader histories".to_owned()],
    )
    .expect("three typed ports share the same declared action");
    assert_eq!(rest.standing.ports.len(), 3);
    assert_eq!(rest.decoder.consequences.len(), 12);
    assert_eq!(rest.fibres.naturality_squares.len(), 6);
}
