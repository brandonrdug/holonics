use crate::native_spool::{NativeSpoolBundle, NativeSpoolConductReturn, NativeSpoolRefusal};
use crate::receiver_exact_compression::{InputId, ReceiverId};
use crate::receiver_history_compression::NativeStateId;

use super::NativeEcologyProfile;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeTransportRequest {
    pub spool: String,
    pub word: Vec<InputId>,
    pub native_start: Vec<NativeStateId>,
    pub receiver: ReceiverId,
}

/// A rested ecology exposes one neutral validation, profile, conduct, and remount surface.
pub trait RestedTransportEcology {
    type Error;
    type Request;
    type Return;
    type Profile<'a>
    where
        Self: 'a;

    fn validate_rest(&self) -> Result<(), Self::Error>;
    fn intrinsic_profile(&self) -> Result<Self::Profile<'_>, Self::Error>;
    fn conduct(&self, request: &Self::Request) -> Result<Self::Return, Self::Error>;
    fn canonical_rest_bytes(&self) -> Result<Vec<u8>, Self::Error>;
}

impl RestedTransportEcology for NativeSpoolBundle {
    type Error = NativeSpoolRefusal;
    type Request = NativeTransportRequest;
    type Return = NativeSpoolConductReturn;
    type Profile<'a> = NativeEcologyProfile<'a>;

    fn validate_rest(&self) -> Result<(), Self::Error> {
        self.validate()
    }

    fn intrinsic_profile(&self) -> Result<Self::Profile<'_>, Self::Error> {
        self.intrinsic_holon_profile()
    }

    fn conduct(&self, request: &Self::Request) -> Result<Self::Return, Self::Error> {
        let mut resident = self.mount_word(&request.spool, &request.word)?;
        resident.conduct(&request.native_start, request.receiver)
    }

    fn canonical_rest_bytes(&self) -> Result<Vec<u8>, Self::Error> {
        self.canonical_bytes()
    }
}
