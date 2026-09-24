//! The coupled HNN body: the constitutive field, its generator machine and incident reaction.

mod body;
pub use body::SavedCoupledBody;
pub use body::{
    GeneratorIncidentFieldSpec, GeneratorPhasePort, GeneratorPhaseReceiverBinding,
    GeneratorSourceBinding, GeneratorSourceContact, GeneratorSourceContactKind,
    IncidentFieldSolver, IncidentFieldSpec, IncidentParticipationChart, NativeCoupledBody,
    NativeFieldAttachRefusal, NativeFieldFormation, NativeFieldGeneratedSection,
    NativeFieldModelRest, NativeFieldReactionPort, NativeGeneratorPhaseReception,
    NativeIncidentGenerated, NativeIncidentMaterialReturn, NativeIncidentModelRest,
    ReactionDepositRecord, ReactionLaw,
};
