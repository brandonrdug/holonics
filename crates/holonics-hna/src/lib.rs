//! HNA application interfaces over the current native recurrent operator.
//!
//! The typed run API uses one full-operator session. Earlier alpha/circulation adapters keep their
//! distinct artifact scopes and wire names. Native laws remain owned by `holonic-engine` and `life`.
//! This crate does not supply a second learning mechanism.

pub mod alpha;
mod checkpoint;
pub mod native;
mod publication;
mod stream;

pub use holonic_engine::native_ecology::holonic_intelligence::{NativeEmissionReadout,NativeEmissionProjection};

pub use checkpoint::{
    read_checkpoint, save_checkpoint_new, CheckpointError, HnaBaseDependency, HnaCheckpointReceipt,
    HnaFileDependency, HnaInputMaterialDependency,
};
pub use checkpoint::{read_session_checkpoint, save_stream_checkpoint_new, HnaSavedSession};
pub use publication::{publish_new, PublicationError, PublicationReceipt};
pub use stream::{
    HnaStream, HnaStreamCommand, HnaStreamDisposition, HnaStreamError, HnaStreamRequest,
    HnaStreamState, HNA_STREAM_EVENT_SCHEMA, HNA_STREAM_REQUEST_SCHEMA,
};

pub const ATHENA_ALPHA_APPLICATION_SCHEMA: &str = "org.holonics.athena-alpha.application.v1";
pub const BASE_CONFIGURATION: &str = include_str!("../configurations/base.json");
