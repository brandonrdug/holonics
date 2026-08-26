//! Exterior regression guard for a third nominal source boundary.
//!
//! Test material stays outside the protected production-owner census. The production change is
//! only a fresh `BoundaryId`; the existing heterogeneous fusion law remains its owner.

use holonic_engine::{
    category::BoundaryId,
    native_ecology::heterogeneous_fusion::{
        HeterogeneousFusionRest, PortDeclaration, SharedWorldGenerator, SourcePortResponse,
    },
};

fn sha(value: u32) -> String {
    format!("{value:064x}")
}

#[test]
fn the_same_owner_admits_an_audio_port_without_changing_the_fusion_law() {
    let ports = [BoundaryId(11), BoundaryId(29), BoundaryId(47)];
    let responses = (0..2)
        .flat_map(|family| {
            ports
                .into_iter()
                .enumerate()
                .flat_map(move |(boundary_at, boundary)| {
                    (0..2).map(move |state| {
                        let mark = 1 + family * 6 + boundary_at as u32 * 2 + state;
                        SourcePortResponse {
                            family,
                            state,
                            boundary,
                            occurrence: format!("family-{family}/state-{state}/{boundary:?}"),
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
                boundary: ports[0],
                source_boundary: "ordered codewords".to_owned(),
                source_population: "text".to_owned(),
                source_extent: 8,
                incidence: "serial".to_owned(),
            },
            PortDeclaration {
                boundary: ports[1],
                source_boundary: "patches".to_owned(),
                source_population: "vision".to_owned(),
                source_extent: 3,
                incidence: "planar".to_owned(),
            },
            PortDeclaration {
                boundary: ports[2],
                source_boundary: "exact PCM frames".to_owned(),
                source_population: "audio".to_owned(),
                source_extent: 5,
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
