use super::*;
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum NativeSpoolRefusal {
    #[error("native spool wire refused: {0}")]
    Wire(String),
    #[error("unknown native spool schema {0}")]
    Schema(String),
    #[error("native thread {0} is empty or incomplete")]
    MalformedThread(String),
    #[error("native thread {0} has malformed occurrence lineage or ports")]
    Occurrence(String),
    #[error("native thread {0} does not retain its complete occurrence fibre")]
    ReconstructionFibre(String),
    #[error("native thread {0} has malformed or incomplete incidence")]
    Incidence(String),
    #[error("native thread {0} has malformed, incomplete, or empty Parametron current")]
    Parametron(String),
    #[error("native thread {0} has a malformed receiver consequence")]
    ReceiverConsequence(String),
    #[error("native thread {0} has a malformed constitutive response")]
    ConstitutiveResponse(String),
    #[error("native thread {0} has a malformed obstruction")]
    Obstruction(String),
    #[error("native object {0} has an empty open-exterior address")]
    OpenExterior(String),
    #[error("native spool {0} is empty or incomplete")]
    MalformedSpool(String),
    #[error("native thread address {0} is repeated")]
    DuplicateThread(String),
    #[error("native occurrence {0:?} is owned by more than one thread")]
    DuplicateOccurrence(EventId),
    #[error("native spool {0} has an inconsistent native population")]
    NativePopulation(String),
    #[error("serial pullback {0} -> {1} is incomplete or malformed")]
    Pullback(String, String),
    #[error("serial pullback {0} -> {1} is repeated")]
    DuplicatePullback(String, String),
    #[error("native generator {0:?} has a partial or unrealized descent")]
    GeneratorDescent(InputId),
    #[error("native spool {0} does not carry exactly its declared generator family")]
    GeneratorFamily(String),
    #[error("native spool {0} does not carry the complete receiver factor family")]
    ReceiverFactor(String),
    #[error("native spool {0} has a malformed mutual constitutive response")]
    MutualConstitutiveResponse(String),
    #[error("native spool {0} does not retain an exact occurrence-fibre partition")]
    SpoolFibre(String),
    #[error("native spool {0} has a malformed shortest separator")]
    Separator(String),
    #[error("native spool {0} has a malformed interchange receipt")]
    Interchange(String),
    #[error("native spool bundle {0} is empty or incomplete")]
    MalformedBundle(String),
    #[error("native spool address {0} is repeated")]
    DuplicateSpool(String),
    #[error("native spool composition is missing, repeated, or names the wrong owner")]
    BundleComposition,
    #[error("native spool bundle has more than one disconnected component")]
    DisconnectedBundle,
    #[error("receiver insufficiency is malformed or does not exhibit its retained fibre")]
    Insufficiency,
    #[error("native spool {0} is absent from this bundle")]
    UnknownSpool(String),
    #[error("native thread {0} is absent from this bundle")]
    UnknownThread(String),
    #[error("native occurrence {0:?} is absent from the addressed thread")]
    UnknownOccurrence(EventId),
    #[error("native addressed section at occurrence {0:?} is inconsistent with its owner")]
    AddressedSection(EventId),
    #[error("native generator {0:?} is absent from the mounted spool")]
    UnknownGenerator(InputId),
    #[error("native state {0:?} is absent from the mounted spool")]
    UnknownNative(NativeStateId),
    #[error("receiver {receiver:?} has no factor at native state {native:?}")]
    UnknownReceiver {
        native: NativeStateId,
        receiver: ReceiverId,
    },
    #[error("resident native spool apparatus refused: {0}")]
    Apparatus(String),
    #[error("the native thread withdrawal cannot restore its exact predecessor")]
    Restoration,
    #[error("native thread deposit refused: {0}")]
    ThreadDeposit(String),
    #[error("the native thread deposit receipt is malformed or does not address this successor")]
    ThreadDepositReceipt,
    #[error(
        "the native thread deposit batch receipt is malformed or does not address this successor"
    )]
    ThreadDepositBatchReceipt,
    #[error("native mixed constitutive family {0} fails exact finite-Leibniz reconstruction")]
    MixedConstitutiveFamily(String),
    #[error("native exact reconstruction fibre {0} is malformed or not incident to its thread")]
    ExactReconstructionFibre(String),
}
