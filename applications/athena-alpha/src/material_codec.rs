//! Cold octet projection of an already-returned native fine emission.

use life::native_intelligence::NativeMaterialEmissionBoundary;
use serde::Serialize;
use thiserror::Error;

/// Editable application artifact with its complete native source boundary retained beside it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct AthenaMaterialArtifact {
    pub octets: Vec<u8>,
    pub native: NativeMaterialEmissionBoundary,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum AthenaMaterialCodecError {
    #[error("the native emission observation does not fit the declared octet face")]
    ObservationOutsideOctet,
}

pub fn render_material_artifact(
    native: NativeMaterialEmissionBoundary,
) -> Result<AthenaMaterialArtifact, AthenaMaterialCodecError> {
    let octets = native
        .fine_emission
        .iter()
        .map(|fine| {
            u8::try_from(fine.emitted_observation.0)
                .map_err(|_| AthenaMaterialCodecError::ObservationOutsideOctet)
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(AthenaMaterialArtifact { octets, native })
}

#[cfg(test)]
mod tests {
    use std::path::PathBuf;

    use holonic_engine::{
        EventId,
        native_ecology::holonic_intelligence::{
            NativeInferenceAddress, NativeInferenceRequest, direct_source_neutral_rest,
        },
        receiver_exact_compression::ReceiverId,
    };
    use life::native_intelligence::{
        InferenceConfigurationAddress, MorphologyLineage, NativeCirculationConfiguration,
        NativeEcologyRest, NativeMorphologyArtifact, NativeWorldStage,
    };

    use crate::{AthenaAlphaApplication, ExactReadbackWorld, ProcessArtifactWorld};

    use super::*;

    #[test]
    fn application_renders_only_the_native_observation_face() {
        let package = NativeMorphologyArtifact::found(
            NativeEcologyRest::found(direct_source_neutral_rest().expect("direct rest"))
                .expect("ecology rest"),
            MorphologyLineage::origin(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )
        .expect("package");
        let application = AthenaAlphaApplication::mount(
            package,
            NativeCirculationConfiguration::found(InferenceConfigurationAddress {
                ingress_aperture: "declared-native-occurrence".to_owned(),
                occurrence: EventId(1),
                receiver: ReceiverId(9),
                continuation_receiver: "issued-world-face-family".to_owned(),
                world_return_law: "session-constituted-return".to_owned(),
                emission_codec: "application-octet-face".to_owned(),
                apparatus: "resident-native-word".to_owned(),
                stochastic_current: None,
            })
            .expect("configuration"),
        )
        .expect("application");
        let request = NativeInferenceRequest {
            address: NativeInferenceAddress {
                spool: "spool/direct-cycle".to_owned(),
                thread: "thread/outward".to_owned(),
                occurrence: EventId(1),
            },
            receiver: ReceiverId(9),
        };
        let ingress = application
            .ingress_octets(request, "application/material", &[3, 8, 2])
            .expect("ingress");
        let native = application
            .conduct_material(ingress)
            .expect("native emission");
        let artifact = render_material_artifact(native).expect("artifact");
        assert_eq!(artifact.octets, vec![101, 101, 101]);
        assert_eq!(artifact.native.fine_emission.len(), artifact.octets.len());
        assert_eq!(artifact.native.cold_preimage.exact_octets, vec![3, 8, 2]);

        let rejected = ProcessArtifactWorld {
            program: PathBuf::from("/bin/sh"),
            arguments: vec!["-c".to_owned(), "printf rejected >&2; exit 9".to_owned()],
            artifact_name: "emission.bin".to_owned(),
        }
        .act(&artifact.octets)
        .expect("process world");
        assert!(matches!(
            application
                .stage_world_return(
                    &artifact.native.circulation,
                    rejected
                        .faces_for(&artifact.native.circulation)
                        .expect("rejected faces"),
                    EventId(99),
                )
                .expect("rejected return"),
            NativeWorldStage::Obstructed(_)
        ));

        let admitted = ExactReadbackWorld
            .act(&artifact.octets)
            .expect("readback world");
        assert!(matches!(
            application
                .stage_world_return(
                    &artifact.native.circulation,
                    admitted
                        .faces_for(&artifact.native.circulation)
                        .expect("admitted faces"),
                    EventId(100),
                )
                .expect("admitted return"),
            NativeWorldStage::Candidate { .. }
        ));
    }
}
