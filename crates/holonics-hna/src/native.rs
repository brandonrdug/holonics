//! The HNN machine: the coupled body over the constitutive field and its generator geometry.
use holonic_engine::dimensional_wave::ExactComplexWaveCurrent;
use holonic_engine::embedding_fiber::ResidentReadout;
use holonic_engine::native_ecology::constitutive_fibre::{
    ConstitutiveFibreError, ConstitutiveReading, NativeConstitutiveEcology,
    NativeCurrentOccurrence, NativeEmissionHandle, NativeJunctionSeed, NativePhaseCurrent,
};
use holonic_engine::resident_section::{ResidentSurface, TransferCensus};
use serde::{Deserialize, Serialize};
use thiserror::Error;

pub mod section_input;
pub mod field_geometry;
pub use field_geometry::GeometricFieldSpec;
mod coupled_wave;
pub use coupled_wave::{
    GeneratorIncidentFieldSpec, GeneratorPhasePort, GeneratorPhaseReceiverBinding,
    GeneratorSourceBinding, GeneratorSourceContact, GeneratorSourceContactKind,
    IncidentFieldSolver, IncidentFieldSpec, IncidentParticipationChart, NativeCoupledBody,
    NativeFieldAttachRefusal, NativeFieldFormation, NativeFieldGeneratedSection,
    NativeFieldModelRest, NativeFieldReactionPort, NativeGeneratorPhaseReception,
    NativeIncidentGenerated, NativeIncidentMaterialReturn, NativeIncidentModelRest,
    ReactionDepositRecord, ReactionLaw, SavedCoupledBody,
};

mod wire;
pub use wire::*;

#[derive(Debug, Error)]
pub enum NativeSessionError {
    #[error("native artifact I/O: {0}")]
    Io(#[from] std::io::Error),
    #[error(transparent)]
    Engine(#[from] ConstitutiveFibreError),
    #[error(transparent)]
    Codec(#[from] serde_json::Error),
    #[error("native application: {0}")]
    Application(String),
}

#[cfg(test)]
mod tests;

/// Numerical enclosure law carried by generator geometry and its saved comparisons.
pub use holonic_engine::native_ecology::constitutive_fibre::NativeEnclosurePropagation;
