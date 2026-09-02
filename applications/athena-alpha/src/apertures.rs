use holonic_engine::{
    native_ecology::holonic_intelligence::{NativeInferenceAddress, NativeInferenceRequest},
    receiver_exact_compression::ReceiverId,
    EventId,
};

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
