//! HNA application interfaces over the current native recurrent operator.
//!
//! The typed run API uses one full-operator session. Earlier alpha/circulation adapters keep their
//! distinct artifact scopes and wire names. Native laws remain owned by `holonic-engine`, `life`,
//! and `holonics-circulation-abi`; this crate does not supply a second learning mechanism.

mod apertures;
mod application;
mod checkpoint;
mod composed_variant;
mod diffusion;
mod hna;
mod input_material;
mod material_codec;
mod publication;
mod receivers;
mod recurrent_operator;
mod session;
mod stream;
mod world_application;

pub use apertures::addressed_ingress;
pub use application::{AthenaAlphaAdmission, AthenaAlphaApplication, AthenaAlphaError};
pub use checkpoint::{
    read_checkpoint, save_checkpoint_new, CheckpointError, HnaBaseDependency, HnaCheckpointReceipt,
    HnaInputMaterialDependency,
};
pub use checkpoint::{read_session_checkpoint, save_stream_checkpoint_new, HnaSavedSession};
pub use composed_variant::{
    class_cone_roles, saturation, species_over_family, width_difference, ComposedFace,
    ComposedVariant, DeclaredDecoder, ProductVector, ReceiptDerivation, ReleaseReceipt,
    SaturationReceipt, SaturationStep, COMPOSED_DEED_SCOPE, COMPOSED_VARIANT_SCHEMA,
};
pub use diffusion::declared_diffusion_law;
pub use hna::{
    inspect_native_restricted_rest, run_hna, HnaCultivationAperture, HnaCycleReceipt, HnaError,
    HnaOccurrence, HnaRestrictedInspection, HnaRunReceipt, HnaRunRequest, HnaSource, HnaSourceKind,
    HNA_RUN_SCHEMA,
};
pub use input_material::HnaInputAcquisitionReceipt;
pub use material_codec::{
    render_material_artifact, AthenaMaterialArtifact, AthenaMaterialCodecError,
};
pub use publication::{publish_new, PublicationError, PublicationReceipt};
pub use receivers::{inspect_cycle, AthenaAlphaCycleReceipt};
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
pub use world_application::{
    ApplicationWorldError, ApplicationWorldReturn, ExactReadbackWorld, ProcessArtifactWorld,
};

pub const ATHENA_ALPHA_APPLICATION_SCHEMA: &str = "org.holonics.athena-alpha.application.v1";
pub const BASE_CONFIGURATION: &str = include_str!("../configurations/base.json");
