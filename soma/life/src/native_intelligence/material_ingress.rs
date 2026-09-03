//! Finest-occurrence material current at one declared native ingress address.

use holonic_engine::native_ecology::holonic_intelligence::{
    NativeInferenceRequest, NativeMaterialCurrent,
};
use serde::Serialize;

use super::{NativeCirculationSession, NativeSessionError};

/// Exact exterior source testimony. This lane is never accepted by native conduct.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeMaterialColdPreimage {
    pub exterior_occurrence: String,
    pub exact_octets: Vec<u8>,
}

/// One addressed native current and its physically separate source preimage.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeMaterialIngress {
    request: NativeInferenceRequest,
    current: NativeMaterialCurrent,
    cold_preimage: NativeMaterialColdPreimage,
}

impl NativeMaterialIngress {
    pub fn request(&self) -> &NativeInferenceRequest {
        &self.request
    }

    pub fn current(&self) -> &NativeMaterialCurrent {
        &self.current
    }

    pub fn cold_preimage(&self) -> &NativeMaterialColdPreimage {
        &self.cold_preimage
    }

    pub(super) fn into_parts(
        self,
    ) -> (
        NativeInferenceRequest,
        NativeMaterialCurrent,
        NativeMaterialColdPreimage,
    ) {
        (self.request, self.current, self.cold_preimage)
    }
}

impl NativeCirculationSession {
    /// Present octets as exact ordered boundary-difference current at a caller-declared native
    /// ingress. The octets cannot select another spool, thread, occurrence, or receiver.
    pub fn ingress_octets(
        &self,
        request: NativeInferenceRequest,
        exterior_occurrence: impl Into<String>,
        octets: &[u8],
    ) -> Result<NativeMaterialIngress, NativeSessionError> {
        let exterior_occurrence = exterior_occurrence.into();
        if exterior_occurrence.is_empty() || request.receiver != self.configuration().address.receiver {
            return Err(NativeSessionError::Ingress(
                "the material occurrence or declared receiver is malformed".to_owned(),
            ));
        }
        let native = self.package().hot().native();
        let section = native
            .addressed_section(
                &request.address.spool,
                &request.address.thread,
                request.address.occurrence,
            )
            .map_err(|error| NativeSessionError::Ingress(error.to_string()))?;
        if !section.spool().receiver_family.contains(&request.receiver) {
            return Err(NativeSessionError::Ingress(
                "the material receiver lies outside the declared native family".to_owned(),
            ));
        }
        let current = NativeMaterialCurrent::from_octets(octets)
            .map_err(|error| NativeSessionError::Ingress(error.to_string()))?;
        Ok(NativeMaterialIngress {
            request,
            current,
            cold_preimage: NativeMaterialColdPreimage {
                exterior_occurrence,
                exact_octets: octets.to_vec(),
            },
        })
    }
}

#[cfg(test)]
mod tests {
    use holonic_engine::{
        native_ecology::holonic_intelligence::{
            direct_source_neutral_rest, NativeInferenceAddress,
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
                emission_codec: "owned-native-grain".to_owned(),
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
    fn locator_renaming_changes_only_the_cold_preimage() {
        let session = session();
        let left = session
            .ingress_octets(request(), "application/left", &[3, 8, 2])
            .expect("left");
        let right = session
            .ingress_octets(request(), "application/right", &[3, 8, 2])
            .expect("right");
        assert_eq!(left.request(), right.request());
        assert_eq!(left.current(), right.current());
        assert_ne!(left.cold_preimage(), right.cold_preimage());
    }

    #[test]
    fn changed_octet_reopens_current_while_address_and_scalar_sum_stay_fixed() {
        let session = session();
        let left = session
            .ingress_octets(request(), "application/material", &[3, 8, 2])
            .expect("left");
        let right = session
            .ingress_octets(request(), "application/material", &[4, 8, 2])
            .expect("right");
        assert_eq!(left.request(), right.request());
        assert_eq!(left.current().integrated_current, right.current().integrated_current);
        assert_ne!(left.current().occurrences, right.current().occurrences);
        assert!(session
            .ingress_octets(request(), "application/material", &[])
            .is_err());
    }
}
