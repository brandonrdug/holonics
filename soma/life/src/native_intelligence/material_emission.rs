//! Native fine emission from one addressed material current.

use holonic_engine::{
    native_ecology::holonic_intelligence::{NativeFutureFace, NativeMaterialCurrentOccurrence},
    receiver_exact_compression::Observation,
};
use serde::Serialize;

use super::{
    NativeCirculationBoundary, NativeCirculationSession, NativeMaterialColdPreimage,
    NativeMaterialIngress, NativeSessionError,
};

/// One finest-grain material current after the addressed native future has met it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeMaterialEmissionOccurrence {
    pub ordinal: u64,
    pub entering: NativeMaterialCurrentOccurrence,
    pub emitted_future: NativeFutureFace,
    pub emitted_observation: Observation,
}

/// Complete native material emission before any application codec renders octets.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeMaterialEmissionBoundary {
    pub circulation: NativeCirculationBoundary,
    pub fine_emission: Vec<NativeMaterialEmissionOccurrence>,
    pub cold_preimage: NativeMaterialColdPreimage,
}

impl NativeMaterialEmissionBoundary {
    pub fn validate_for(
        &self,
        session: &NativeCirculationSession,
    ) -> Result<(), NativeSessionError> {
        self.circulation.validate_for(session)?;
        let emitted = self
            .circulation
            .emission
            .grains
            .get(self.circulation.emission.selected_grain)
            .ok_or(NativeSessionError::Boundary)?
            .future;
        if self.fine_emission.is_empty()
            || self.fine_emission.len() != self.cold_preimage.exact_octets.len()
            || self.fine_emission.iter().enumerate().any(|(ordinal, fine)| {
                fine.ordinal != ordinal as u64
                    || fine.entering.ordinal != fine.ordinal
                    || fine.emitted_future != emitted
                    || fine.emitted_observation != emitted.observation
            })
        {
            return Err(NativeSessionError::Boundary);
        }
        Ok(())
    }
}

impl NativeCirculationSession {
    /// Conduct one already-addressed material current through the same session boundary used by
    /// ordinary inference. The complete fine current remains beside the emitted receiver face.
    pub fn conduct_material(
        &self,
        ingress: NativeMaterialIngress,
    ) -> Result<NativeMaterialEmissionBoundary, NativeSessionError> {
        let (request, current, cold_preimage) = ingress.into_parts();
        let circulation = self.conduct(request)?;
        let emitted = circulation
            .emission
            .grains
            .get(circulation.emission.selected_grain)
            .ok_or(NativeSessionError::Boundary)?
            .future;
        let fine_emission = current
            .occurrences
            .into_iter()
            .map(|entering| NativeMaterialEmissionOccurrence {
                ordinal: entering.ordinal,
                entering,
                emitted_future: emitted,
                emitted_observation: emitted.observation,
            })
            .collect();
        let boundary = NativeMaterialEmissionBoundary {
            circulation,
            fine_emission,
            cold_preimage,
        };
        boundary.validate_for(self)?;
        Ok(boundary)
    }
}

#[cfg(test)]
mod tests {
    use holonic_engine::{
        native_ecology::holonic_intelligence::{
            direct_source_neutral_rest, NativeInferenceAddress, NativeInferenceRequest,
        },
        receiver_exact_compression::ReceiverId,
        EventId,
    };

    use crate::native_intelligence::{
        InferenceConfigurationAddress, MorphologyLineage, NativeCirculationConfiguration,
        NativeEcologyRest, NativeMorphologyArtifact,
    };

    use super::*;

    fn session() -> NativeCirculationSession {
        let package = NativeMorphologyArtifact::found(
            NativeEcologyRest::found(direct_source_neutral_rest().expect("direct rest"))
                .expect("ecology rest"),
            MorphologyLineage::origin(),
            Vec::new(),
            Vec::new(),
            Vec::new(),
        )
        .expect("package");
        NativeCirculationSession::mount(
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
        .expect("session")
    }

    fn request() -> NativeInferenceRequest {
        NativeInferenceRequest {
            address: NativeInferenceAddress {
                spool: "spool/direct-cycle".to_owned(),
                thread: "thread/outward".to_owned(),
                occurrence: EventId(1),
            },
            receiver: ReceiverId(9),
        }
    }

    #[test]
    fn complete_fine_current_remains_beside_the_native_emission_face() {
        let session = session();
        let ingress = session
            .ingress_octets(request(), "application/material", &[3, 8, 2])
            .expect("ingress");
        let entering = ingress.current().occurrences.clone();
        let boundary = session.conduct_material(ingress).expect("emission");
        assert_eq!(boundary.fine_emission.len(), 3);
        assert_eq!(
            boundary
                .fine_emission
                .iter()
                .map(|fine| fine.entering.clone())
                .collect::<Vec<_>>(),
            entering
        );
        assert!(boundary.validate_for(&session).is_ok());
    }
}
