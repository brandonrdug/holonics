use sha2::{Digest, Sha256};

use super::{
    ExactMediaAxis, ExactSpatialDeclaration, FamilyCorrespondenceFibre, MathematicalMediaPort,
    MediaCandidatePair, MediaSourceFamily, MediaSourceInterior, MultimodalTransportRefusal,
    MultimodalTransportRest, ProductLineage,
};

fn digest(bytes: &[u8]) -> String {
    Sha256::digest(bytes)
        .iter()
        .map(|octet| format!("{octet:02x}"))
        .collect()
}

fn interior(family: u32, port: MathematicalMediaPort) -> MediaSourceInterior {
    let canonical = format!("family-{family}-{port:?}-exact-spatial-incidence").into_bytes();
    let artifact = digest(format!("artifact-{family}-{port:?}").as_bytes());
    MediaSourceInterior {
        family,
        port,
        artifact_occurrence: format!("source-{family}-{port:?}"),
        artifact_sha256: artifact.clone(),
        chart: format!("{port:?}"),
        occurrence_population: 2,
        contact_population: 1,
        incidence_sha256: digest(&canonical),
        spatial: ExactSpatialDeclaration {
            dimension: 2,
            axes: vec![
                ExactMediaAxis {
                    name: "x".to_owned(),
                    extent_numerator: 2,
                    extent_denominator: 1,
                    common_scale_numerator: 1,
                    common_scale_denominator: 1,
                    forward_hand: 1,
                },
                ExactMediaAxis {
                    name: "y".to_owned(),
                    extent_numerator: 3,
                    extent_denominator: 1,
                    common_scale_numerator: 1,
                    common_scale_denominator: 1,
                    forward_hand: -1,
                },
            ],
            uncertainty_fibre_sha256: digest(format!("uncertainty-{family}").as_bytes()),
            source_lineage_sha256: artifact,
        },
        canonical_interior: canonical,
    }
}

fn family(family: u32) -> MediaSourceFamily {
    let pairs = vec![
        MediaCandidatePair {
            anchor: 0,
            member: 0,
        },
        MediaCandidatePair {
            anchor: 1,
            member: 1,
        },
    ];
    MediaSourceFamily {
        family,
        occurrence: format!("family-{family}"),
        notation: interior(family, MathematicalMediaPort::Notation),
        vector: interior(family, MathematicalMediaPort::Vector),
        raster: interior(family, MathematicalMediaPort::RasterVision),
        correspondences: FamilyCorrespondenceFibre {
            family,
            anchor_population: 2,
            vector_population: 2,
            raster_four_population: 2,
            raster_eight_population: 2,
            text_vector: pairs.clone(),
            text_raster_four: pairs.clone(),
            text_raster_eight: pairs,
            unmatched: Vec::new(),
        },
    }
}

fn found() -> MultimodalTransportRest {
    MultimodalTransportRest::found(
        ProductLineage {
            m0_source_sha256: digest(b"m0-source"),
            m0_product_sha256: digest(b"m0-product"),
            i4_rest_sha256: digest(b"i4-rest"),
            r4_boundary_sha256: digest(b"r4-boundary"),
            source_occurrence: "m0-natural-pages-five-and-ten".to_owned(),
        },
        vec![family(0), family(1)],
        1,
        "heat-kernel-common-page-world".to_owned(),
        "i4-shared-action-through-r4-boundary".to_owned(),
        vec![1, 1, 2, 1, 1, 2],
        vec!["an unasked media receiver remains exterior".to_owned()],
    )
    .expect("the fixture found one exact joint-media rest")
}

#[test]
fn the_joint_media_rest_round_trips_without_cloning_the_owner() {
    let rest = found();
    let standing = rest.standing_bytes().expect("standing");
    let decoder = rest.decoder_bytes().expect("decoder");
    let fibres = rest.fibre_bytes().expect("fibres");
    let remounted =
        MultimodalTransportRest::read(&standing, &decoder, &fibres).expect("remounted rest");
    assert_eq!(remounted, rest);
    assert_eq!(
        remounted
            .reconstruct_interior(1, MathematicalMediaPort::RasterVision)
            .expect("held-out raster interior"),
        b"family-1-RasterVision-exact-spatial-incidence"
    );
}

#[test]
fn the_rest_refuses_an_incomplete_joint_anchor() {
    let mut families = vec![family(0), family(1)];
    families[1]
        .correspondences
        .text_raster_eight
        .retain(|pair| pair.anchor != 1);
    let refused = MultimodalTransportRest::found(
        ProductLineage {
            m0_source_sha256: digest(b"m0-source"),
            m0_product_sha256: digest(b"m0-product"),
            i4_rest_sha256: digest(b"i4-rest"),
            r4_boundary_sha256: digest(b"r4-boundary"),
            source_occurrence: "fixture".to_owned(),
        },
        families,
        1,
        "world".to_owned(),
        "generator".to_owned(),
        vec![1, 1, 2, 1, 1, 1],
        vec!["open".to_owned()],
    );
    assert_eq!(
        refused,
        Err(MultimodalTransportRefusal::IncompleteJointAnchor(1))
    );
}

#[test]
fn the_rest_refuses_a_changed_exact_source_interior() {
    let mut rest = found();
    rest.decoder.interiors[0].canonical_interior.push(0);
    assert_eq!(
        rest.decoder_bytes(),
        Err(MultimodalTransportRefusal::Interior)
    );
}
