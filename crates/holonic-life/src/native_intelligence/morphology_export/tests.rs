use std::collections::BTreeSet;

use holonic_engine::{
    native_spool::fixture,
    receiver_exact_compression::{Observation, ReceiverId},
    EventId,
};

use super::*;
use crate::native_intelligence::{
    consume_dismantling_return, ConfigurationEvaluationReceipt, InferenceConfigurationAddress,
    MorphologyLineage, NativeMorphologyArtifact,
};

fn package(observation: Option<u64>) -> NativeMorphologyArtifact {
    let hot = consume_dismantling_return(fixture::returned())
        .expect("handoff")
        .0;
    let evaluation = observation
        .map(|observation| ConfigurationEvaluationReceipt {
            configuration: InferenceConfigurationAddress {
                ingress_aperture: "declared-aperture".to_owned(),
                occurrence: EventId(1),
                receiver: fixture::FIXTURE_RECEIVER,
                continuation_receiver: "unique-actual-successor".to_owned(),
                world_return_law: "declared-local-return".to_owned(),
                emission_codec: "inspection".to_owned(),
                apparatus: "reference".to_owned(),
                stochastic_current: None,
            },
            observations: vec![Observation(observation)],
            qualitative_surface_is_probe: true,
        })
        .into_iter()
        .collect();
    NativeMorphologyArtifact::found(
        hot,
        MorphologyLineage::origin(),
        evaluation,
        Vec::new(),
        Vec::new(),
    )
    .expect("package")
}

#[test]
fn exact_safetensors_and_onnx_exports_round_trip_the_complete_package() {
    let package = package(None);
    for codec in [ExportCodecKind::Safetensors, ExportCodecKind::Onnx] {
        let returned = export_morphology(
            &package,
            MorphologyExportRequest {
                codec,
                receiver_family: BTreeSet::from([fixture::FIXTURE_RECEIVER]),
                purpose: ExportPurpose::RestedInference,
            },
        )
        .expect("export");
        match returned {
            MorphologyExportReturn::Exact(exact) => {
                assert!(exact.complete_package_round_trip);
                assert!(!exact.artifact.bytes.is_empty());
                let imported = import_exact_export(&exact.artifact).expect("import");
                assert_eq!(
                    imported.canonical_bytes().expect("imported bytes"),
                    package.canonical_bytes().expect("package bytes")
                );
            }
            other => panic!("unexpected export {other:?}"),
        }
    }
}

#[test]
fn anatomy_projection_retains_both_packages_and_a_configuration_separator() {
    let left = package(Some(1));
    let right = package(Some(2));
    for codec in [ExportCodecKind::Safetensors, ExportCodecKind::Onnx] {
        let returned = project_common_anatomy(&left, &right, codec).expect("projection");
        match returned {
            MorphologyExportReturn::Projected(projected) => {
                assert_eq!(projected.collapsed_package_fibre.len(), 2);
                assert_eq!(projected.separator.left_observations, vec![Observation(1)]);
                assert_eq!(projected.separator.right_observations, vec![Observation(2)]);
                assert_eq!(
                    NativeMorphologyArtifact::read(&projected.collapsed_package_fibre[0])
                        .expect("left fibre")
                        .canonical_bytes()
                        .expect("left bytes"),
                    left.canonical_bytes().expect("left package")
                );
            }
            other => panic!("unexpected projection {other:?}"),
        }
    }
}

#[test]
fn cultivation_world_return_and_unsupported_receiver_exports_refuse() {
    let package = package(None);
    let controls = [
        (
            ExportPurpose::Cultivation,
            BTreeSet::from([fixture::FIXTURE_RECEIVER]),
            MorphologyExportRefusal::CultivationIsNotRestedInference,
        ),
        (
            ExportPurpose::WorldReturn,
            BTreeSet::from([fixture::FIXTURE_RECEIVER]),
            MorphologyExportRefusal::WorldReturnIsNotRestedInference,
        ),
        (
            ExportPurpose::RestedInference,
            BTreeSet::from([ReceiverId(99)]),
            MorphologyExportRefusal::ReceiverOutsidePackage,
        ),
    ];
    for (purpose, receiver_family, expected) in controls {
        let returned = export_morphology(
            &package,
            MorphologyExportRequest {
                codec: ExportCodecKind::Onnx,
                receiver_family,
                purpose,
            },
        )
        .expect("refusal");
        assert_eq!(returned, MorphologyExportReturn::Refused(expected));
    }
}
