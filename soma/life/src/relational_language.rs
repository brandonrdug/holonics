//! Exact relational language morphology beneath outward wording.
//!
//! Source passages remain witnesses, but they are not future output rails. This ecology receives
//! finite English clause occurrences through one explicit inherited grammar transducer, orients
//! their subject/relation/object incidence, joins clauses through shared entity faces, and may
//! realize the resulting relation current in a voice not present in any supporting passage.
//! Nothing here claims a universal grammar or semantic ontology: unsupported entity boundaries
//! remain open and no scalar score, probability, or fabricated relation enters standing.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    num::NonZeroUsize,
};

use body::num::Cog;
use holonic_engine::{
    CpuExecutionError, CpuExecutionReceipt, CpuExecutor, ExactReceiverCurrentError,
    ExactReceiverCurrentLaw, ExactReceiverCurrentPassage, ExactReceiverCurrentRadiation,
    ReceiverCurrentPassageId, ReceiverCurrentSiteId,
};
use holonic_structure::{GrowingKeyAtlas, LocalQueue, LocalRelations, LocalSequence, LocalSet};
use num_bigint::BigUint;
use soma_abi::active::{ActionCurrent, RelationAtom};
#[cfg(test)]
use soma_membrane::CpuLiveCurrentExecutor;
use soma_membrane::{
    LiveCurrentExecutor, LiveCurrentMachine, LiveMemory, ParallelCpuLiveCurrentExecutor,
    SparseStandingSurface,
};

use crate::{
    causal_language::lexical_tokens,
    morphological_language::MorphologicalLanguagePassage,
    resonance_ecology::{
        fiber_from_bytes, ResonanceEcology, ResonanceEcologyError, ResonanceGerm,
        ResonanceOccurrence, ResonanceOccurrenceConduct, ResonanceOccurrenceRead,
    },
};

const RELATIONAL_JUNCTION_SCHEMA: u64 = 0x5245_4c4a_554e_4354;
const RELATIONAL_JUNCTION_OCCURRENCE_SCHEMA: u64 = 0x5245_4c4a_4f43_4352;
/// One Resonance occurrence occupies an antecedent order and its next consequent order.
const RELATIONAL_SWING_OCCURRENCE_SPAN: u64 = 2;

mod types;
pub use types::{
    RelationalCausalChannel, RelationalCausalFrontFiber, RelationalChannelConduct,
    RelationalClause, RelationalClauseVoice, RelationalCurrentTransport, RelationalEntity,
    RelationalExecutionReceipt, RelationalHolonomyGenerator, RelationalHolonomyStep,
    RelationalJoin, RelationalLanguageError, RelationalParseFiber, RelationalQuestionFrontier,
    RelationalRealization, RelationalRealizationClause, RelationalReceiverQuotient,
    RelationalThoughtCurrent, RelationalThoughtExecution, RelationalThoughtFiber,
    RelationalTransportHand, RelationalTransportPassage,
};

mod codec;
pub use codec::{
    relational_deliberation_frontier, relational_passage_clauses, relational_question_regions,
};

mod transport;
pub use transport::realize_relational_clauses;

mod ecology;
pub use ecology::{ClausePairDelayLaw, ExactRelationalLanguageEcology};

#[cfg(test)]
mod tests;
