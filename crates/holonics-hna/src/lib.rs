//! HNA application interfaces over the current native recurrent operator.
//!
//! The typed run API uses one full-operator session. Earlier alpha/circulation adapters keep their
//! distinct artifact scopes and wire names. Native laws remain owned by `holonic-engine` and `life`.
//! This crate does not supply a second learning mechanism.

pub mod alpha;
mod apertures;
mod checkpoint;
mod composed_variant;
mod hna;
mod input_material;
pub mod native;
mod publication;
mod recurrent_operator;
mod session;
mod stream;
mod text_session;

pub use holonic_engine::native_ecology::holonic_intelligence::{NativeEmissionReadout,NativeEmissionProjection};

pub use apertures::addressed_ingress;
pub use checkpoint::{
    read_checkpoint, save_checkpoint_new, CheckpointError, HnaBaseDependency, HnaCheckpointReceipt,
    HnaFileDependency, HnaInputMaterialDependency,
};
pub use checkpoint::{read_session_checkpoint, save_stream_checkpoint_new, HnaSavedSession};
pub use composed_variant::{
    class_cone_roles, saturation, species_over_family, width_difference, ComposedFace,
    ComposedVariant, DeclaredDecoder, ProductVector, ReceiptDerivation, ReleaseReceipt,
    SaturationReceipt, SaturationStep, COMPOSED_DEED_SCOPE, COMPOSED_VARIANT_SCHEMA,
};
pub use hna::{
    inspect_native_restricted_rest, run_hna, HnaCultivationAperture, HnaCycleReceipt, HnaError,
    HnaOccurrence, HnaRestrictedInspection, HnaRunReceipt, HnaRunRequest, HnaSource, HnaSourceKind,
    HNA_RUN_SCHEMA,
};
pub use input_material::HnaInputAcquisitionReceipt;
pub use publication::{publish_new, PublicationError, PublicationReceipt};
pub use recurrent_operator::{
    AthenaRecurrentApplicationError, AthenaRenderedTokenFace, AthenaTextOccurrenceApplication,
    AthenaTokenApplication, AthenaVocabularyFace,
};
pub use session::{
    HnaDeclaredOccurrence, HnaModel, HnaNativeAdmission, HnaNativeCycle, HnaSession,
    HnaSessionAnatomy, HnaSessionError, HnaSessionStatus,
};
pub use stream::{
    HnaStream, HnaStreamCommand, HnaStreamDisposition, HnaStreamError, HnaStreamRequest,
    HnaStreamState, HNA_STREAM_EVENT_SCHEMA, HNA_STREAM_REQUEST_SCHEMA,
};
pub use text_session::{HnaTextApplication, HnaTextContinuation, HnaTextDisposition, HnaTextStep};

pub const ATHENA_ALPHA_APPLICATION_SCHEMA: &str = "org.holonics.athena-alpha.application.v1";
pub const BASE_CONFIGURATION: &str = include_str!("../configurations/base.json");
