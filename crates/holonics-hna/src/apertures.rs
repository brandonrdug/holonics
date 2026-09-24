use holonic_engine::{
    EventId,
        native_ecology::holonic_intelligence::{NativeInferenceAddress, NativeInferenceRequest}
};
use holonics::receiver::native::ReceiverId;

/// Construct one explicit addressed ingress. No label, surface, or collection position is
/// interpreted as a native route.
pub fn addressed_ingress(
    spool: impl Into<String>,
    thread: impl Into<String>,
    occurrence: EventId,
    receiver: ReceiverId,
) -> NativeInferenceRequest {
    NativeInferenceRequest {
        address: NativeInferenceAddress {
            spool: spool.into(),
            thread: thread.into(),
            occurrence,
        },
        receiver,
    }
}
