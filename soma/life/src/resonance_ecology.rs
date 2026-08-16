//! Structural informants over the production live-current Swing.
//!
//! Each caused occurrence supplies a finite population of receiver-local germs as a hyperedge. It
//! does not supply edges between different informants. Equal structural germs only expose possible
//! meetings; the production Swing still compares their complete paths, returns RIDE or OPEN, and
//! propagates the unpublished local front through any newly exposed germs.

use std::collections::{BTreeMap, BTreeSet};
use std::sync::Arc;

use body::incidence::IncidenceHand;
use body::num::{Cog, COG_WORDS};
use holonic_structure::{
    GrowingKeyAtlas, KeyAtlasError, LocalRelations, LocalSequence, LocalSet, LocalStructureError,
    RelationAtlasError,
};
use soma_abi::active::{ActionCurrent, RelationAtom};
#[cfg(test)]
use soma_membrane::LiveBoundaryTransition;
use soma_membrane::{
    ContemporaryRadiation, CurrentBoundaryPort, CpuLiveCurrentExecutor, InterfaceCapabilityOrigin,
    LiveConstituent, LiveCurrentError, LiveCurrentExecutor, LiveCurrentMachine,
    LiveCurrentRestImage, ReceiverCausalPassage, ReceiverFiberIdentity, RegionalRelationRadiation,
};

use crate::current_world::{
    present_native_event_with_regional, NativeEventCurrent, NativePathChart, NativeRegionalArc,
    NativeRegionalRelation, NativeRelationOrgan, NativeRelationOrganImage,
    NATIVE_RELATION_ORGAN_WORDS,
};

const GERM_RECEIVER_CHART: u64 = 0x5245_534f_4745_524d;
const CAPACITIVE_RECEIVER_CHART: u64 = 0x5245_534f_4341_5041;
const ROLE_SCHEMA: u64 = 0x5245_534f_524f_4c45;
const CONTINUATION_TARGET_SCHEMA: u64 = 0x5245_534f_4e45_5854;
const EMANATED_PATH_SCHEMA: u64 = 0x5245_534f_454d_414e;
const GERM_ROLE_WORD: u32 = 1;
const INFORMANT_ROLE_WORD: u32 = 2;
const CONTINUATION_SOURCE_ROLE_WORD: u32 = 3;
const INHERITED_ORIGIN_ROLE_WORD: u32 = 4;
const QUESTION_ORIGIN_ROLE_WORD: u32 = 5;
const EMANATED_ORIGIN_ROLE_WORD: u32 = 6;
const CAPACITY_ATOM: i64 = 1;
const GERM_RECEPTOR: u32 = 1;
const INFORMANT_MARKER_RECEPTOR: u32 = 2;
const INFORMANT_CAPACITY_RECEPTOR: u32 = 3;
const REST_MAGIC: u32 = 0x5245_534f;
const REST_VERSION: u32 = 1;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResonanceEcologyError {
    EmptyConfiguration,
    EmptyOccurrence,
    DuplicateInformant,
    Chronology,
    CarrierExtent,
    ContinuationNotExposed,
    EmanationBranchAbsent,
    MalformedRadiation,
    Live(LiveCurrentError),
}

impl From<LiveCurrentError> for ResonanceEcologyError {
    fn from(error: LiveCurrentError) -> Self {
        Self::Live(error)
    }
}

impl From<LocalStructureError> for ResonanceEcologyError {
    fn from(_: LocalStructureError) -> Self {
        Self::CarrierExtent
    }
}

impl From<RelationAtlasError> for ResonanceEcologyError {
    fn from(_: RelationAtlasError) -> Self {
        Self::CarrierExtent
    }
}

impl From<KeyAtlasError> for ResonanceEcologyError {
    fn from(_: KeyAtlasError) -> Self {
        Self::CarrierExtent
    }
}

/// An exact receiver-local pattern. `identity` is the material morphology by which separated
/// informants may become eligible to meet. `phase` is its local geometric presentation; equal
/// identity with incompatible phase remains an OPEN comparison rather than being averaged.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResonanceGerm {
    identity: ReceiverFiberIdentity,
    phase: RelationAtom,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct ResonanceReceptorKey {
    role: u32,
    identity: ReceiverFiberIdentity,
    phase: [u32; COG_WORDS],
}

impl From<&ResonanceGerm> for ResonanceReceptorKey {
    fn from(germ: &ResonanceGerm) -> Self {
        Self {
            role: GERM_RECEPTOR,
            identity: germ.identity.clone(),
            phase: germ.phase.words(),
        }
    }
}

fn informant_receptor_key(
    role: u32,
    identity: &ReceiverFiberIdentity,
    phase: RelationAtom,
) -> ResonanceReceptorKey {
    ResonanceReceptorKey {
        role,
        identity: identity.clone(),
        phase: phase.words(),
    }
}

impl ResonanceGerm {
    pub const fn new(identity: ReceiverFiberIdentity, phase: RelationAtom) -> Self {
        Self { identity, phase }
    }

    pub const fn identity(&self) -> &ReceiverFiberIdentity {
        &self.identity
    }

    pub const fn phase(&self) -> RelationAtom {
        self.phase
    }
}

/// A caused information occurrence. Its germ population is a hyperedge: the occurrence declares
/// only that these local sections belong to this informant. Cross-informant relation is absent
/// until matching boundaries actually close through the live machine.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResonanceOccurrence {
    identity: Option<ReceiverFiberIdentity>,
    source_order: u64,
    germs: Vec<ResonanceGerm>,
    required_germ_ports: LocalSet<ReceiverFiberIdentity>,
    origin: ResonanceOccurrenceOrigin,
    continuation_exposure: bool,
    path_continuations: bool,
    continuation_leaders: Vec<ResonanceGerm>,
    explicit_continuations: Vec<(ResonanceGerm, ResonanceGerm)>,
    routed_testimony: Option<ReceiverFiberIdentity>,
    routed_continuations: Vec<(ResonanceGerm, ReceiverFiberIdentity)>,
}

/// Causal provenance of material crossing the resonance membrane. Equal morphology remains
/// comparable across these roles, while the source occurrence, receiver question, and generated
/// successor never become the same lineage merely because their visible germ path agrees.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ResonanceOccurrenceOrigin {
    Inherited,
    ReceiverQuestion,
    SelfEmanated,
}

impl ResonanceOccurrence {
    pub fn informant(
        identity: ReceiverFiberIdentity,
        source_order: u64,
        germs: Vec<ResonanceGerm>,
    ) -> Result<Self, ResonanceEcologyError> {
        Self::validated(
            Some(identity),
            source_order,
            germs,
            ResonanceOccurrenceOrigin::Inherited,
            false,
            false,
            Vec::new(),
            Vec::new(),
            None,
            Vec::new(),
        )
    }

    /// An inherited ordered path which exposes each actual adjacent germ transport as a
    /// continuation boundary. No alternate continuation or target is supplied.
    pub fn continuation_informant(
        identity: ReceiverFiberIdentity,
        source_order: u64,
        germs: Vec<ResonanceGerm>,
    ) -> Result<Self, ResonanceEcologyError> {
        Self::validated(
            Some(identity),
            source_order,
            germs,
            ResonanceOccurrenceOrigin::Inherited,
            true,
            true,
            Vec::new(),
            Vec::new(),
            None,
            Vec::new(),
        )
    }

    /// A receiver question is itself an occurrence but need not claim a corpus identity. Its
    /// germs launch the same production front as inherited informants.
    pub fn probe(
        source_order: u64,
        germs: Vec<ResonanceGerm>,
    ) -> Result<Self, ResonanceEcologyError> {
        Self::validated(
            None,
            source_order,
            germs,
            ResonanceOccurrenceOrigin::ReceiverQuestion,
            false,
            false,
            Vec::new(),
            Vec::new(),
            None,
            Vec::new(),
        )
    }

    /// A receiver question whose terminal germ opens a continuation aperture. The question
    /// supplies no candidate successor; eligible branches must return through conditioned
    /// standing.
    pub fn continuation_probe(
        source_order: u64,
        germs: Vec<ResonanceGerm>,
    ) -> Result<Self, ResonanceEcologyError> {
        let leaders = germs.last().cloned().into_iter().collect();
        Self::continuation_probe_with_leaders(source_order, germs, leaders)
    }

    /// Open every receiver projection in a caused leader frontier. The plural leaders are
    /// alternative local charts of the same question, not a ranked backoff list; every supported
    /// continuation remains present with its complete supporting fibers.
    pub fn continuation_probe_with_leaders(
        source_order: u64,
        germs: Vec<ResonanceGerm>,
        leaders: Vec<ResonanceGerm>,
    ) -> Result<Self, ResonanceEcologyError> {
        if leaders.is_empty() {
            return Err(ResonanceEcologyError::ContinuationNotExposed);
        }
        Self::validated(
            None,
            source_order,
            germs,
            ResonanceOccurrenceOrigin::ReceiverQuestion,
            true,
            true,
            leaders,
            Vec::new(),
            None,
            Vec::new(),
        )
    }

    /// A continuation question whose leaders are co-present receiver projections rather than one
    /// serialized path. Every leader opens its conditioned aperture, but administrative leader
    /// order creates no leader-to-leader continuation.
    pub fn co_present_continuation_probe(
        source_order: u64,
        leaders: Vec<ResonanceGerm>,
    ) -> Result<Self, ResonanceEcologyError> {
        if leaders.is_empty() {
            return Err(ResonanceEcologyError::ContinuationNotExposed);
        }
        Self::validated(
            None,
            source_order,
            leaders.clone(),
            ResonanceOccurrenceOrigin::ReceiverQuestion,
            true,
            false,
            leaders,
            Vec::new(),
            None,
            Vec::new(),
        )
    }

    /// One inherited occurrence whose co-present leaders each expose the same caused target.
    /// The leaders have no administrative chronology among themselves: the occurrence carries
    /// exactly the declared leader-to-target relations and no pairwise feature paths.
    pub fn co_present_continuation_informant(
        identity: ReceiverFiberIdentity,
        source_order: u64,
        leaders: Vec<ResonanceGerm>,
        target: ResonanceGerm,
    ) -> Result<Self, ResonanceEcologyError> {
        if leaders.is_empty() {
            return Err(ResonanceEcologyError::ContinuationNotExposed);
        }
        let leader_count = leaders.len();
        let mut germs = leaders;
        let target_at = if let Some(at) = germs.iter().position(|germ| germ == &target) {
            at
        } else {
            germs.push(target);
            germs.len() - 1
        };
        let explicit_continuations = germs[..leader_count]
            .iter()
            .cloned()
            .map(|leader| (leader, germs[target_at].clone()))
            .collect();
        Self::validated(
            Some(identity),
            source_order,
            germs,
            ResonanceOccurrenceOrigin::Inherited,
            true,
            false,
            Vec::new(),
            explicit_continuations,
            None,
            Vec::new(),
        )
    }

    /// One local routing section restricted from an inherited occurrence. The source testimony
    /// remains explicit, while only the leader receptor persists; the target is an emitted fiber
    /// on that receptor rather than another current which would spuriously glue unrelated
    /// leaders through a shared source node.
    pub fn routed_informant(
        testimony: ReceiverFiberIdentity,
        source_order: u64,
        leader: ResonanceGerm,
        target: ReceiverFiberIdentity,
    ) -> Result<Self, ResonanceEcologyError> {
        Self::validated(
            None,
            source_order,
            vec![leader.clone()],
            ResonanceOccurrenceOrigin::Inherited,
            true,
            false,
            Vec::new(),
            Vec::new(),
            Some(testimony),
            vec![(leader, target)],
        )
    }

    /// Re-enter a path which production itself emanated. Its identity is the complete exact path
    /// fiber rather than a hash or an inherited corpus identity.
    pub fn self_emanated(
        source_order: u64,
        germs: Vec<ResonanceGerm>,
    ) -> Result<Self, ResonanceEcologyError> {
        let leaders = germs.last().cloned().into_iter().collect();
        Self::self_emanated_with_leaders(source_order, germs, leaders)
    }

    pub fn self_emanated_with_leaders(
        source_order: u64,
        germs: Vec<ResonanceGerm>,
        leaders: Vec<ResonanceGerm>,
    ) -> Result<Self, ResonanceEcologyError> {
        if leaders.is_empty() {
            return Err(ResonanceEcologyError::ContinuationNotExposed);
        }
        let identity = path_fiber(EMANATED_PATH_SCHEMA, &germs)?;
        Self::validated(
            Some(identity),
            source_order,
            germs,
            ResonanceOccurrenceOrigin::SelfEmanated,
            true,
            true,
            leaders,
            Vec::new(),
            None,
            Vec::new(),
        )
    }

    fn validated(
        identity: Option<ReceiverFiberIdentity>,
        source_order: u64,
        germs: Vec<ResonanceGerm>,
        origin: ResonanceOccurrenceOrigin,
        continuation_exposure: bool,
        path_continuations: bool,
        continuation_leaders: Vec<ResonanceGerm>,
        explicit_continuations: Vec<(ResonanceGerm, ResonanceGerm)>,
        routed_testimony: Option<ReceiverFiberIdentity>,
        routed_continuations: Vec<(ResonanceGerm, ReceiverFiberIdentity)>,
    ) -> Result<Self, ResonanceEcologyError> {
        if germs.is_empty() || source_order == u64::MAX {
            return Err(if germs.is_empty() {
                ResonanceEcologyError::EmptyOccurrence
            } else {
                ResonanceEcologyError::Chronology
            });
        }
        let mut required_germ_ports = LocalSet::new();
        for germ in &germs {
            required_germ_ports.try_insert(germ.identity().clone())?;
        }
        Ok(Self {
            identity,
            source_order,
            germs,
            required_germ_ports,
            origin,
            continuation_exposure,
            path_continuations,
            continuation_leaders,
            explicit_continuations,
            routed_testimony,
            routed_continuations,
        })
    }

    /// Restrict occurrence completion to an exact declared germ-port aperture. This is a typed
    /// constitutive boundary, not a threshold: every supplied identity must be one of this
    /// occurrence's actual germ ports and every declared port must return Riding.
    pub fn with_required_germ_ports(
        mut self,
        required: LocalSet<ReceiverFiberIdentity>,
    ) -> Result<Self, ResonanceEcologyError> {
        if required.is_empty()
            || required
                .iter()
                .any(|identity| !self.germs.iter().any(|germ| germ.identity() == identity))
        {
            return Err(ResonanceEcologyError::MalformedRadiation);
        }
        self.required_germ_ports = required;
        Ok(self)
    }

    pub const fn identity(&self) -> Option<&ReceiverFiberIdentity> {
        self.identity.as_ref()
    }

    pub const fn source_order(&self) -> u64 {
        self.source_order
    }

    pub fn germs(&self) -> &[ResonanceGerm] {
        &self.germs
    }

    pub const fn origin(&self) -> ResonanceOccurrenceOrigin {
        self.origin
    }

    pub const fn exposes_continuations(&self) -> bool {
        self.continuation_exposure
    }

    pub fn continuation_leaders(&self) -> &[ResonanceGerm] {
        &self.continuation_leaders
    }
}

/// Immediate testimony of one informant or probe crossing.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResonanceRadiation {
    source: ContemporaryRadiation,
    read: ResonanceConstituentRead,
}

impl ResonanceRadiation {
    pub const fn source(&self) -> &ContemporaryRadiation {
        &self.source
    }

    pub fn regional(&self) -> &RegionalRelationRadiation {
        &self.source.regional()[0]
    }

    pub const fn read(&self) -> &ResonanceConstituentRead {
        &self.read
    }
}

/// A successor germ emitted from the conditioned continuation aperture. The branch is not an
/// inherited target row: it is a structural germ already carried by the ecology, newly composed
/// with the receiver question as a possible later occurrence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResonanceEmanatedBranch {
    germ: ResonanceGerm,
    supporting_leaders: Arc<BTreeSet<ReceiverFiberIdentity>>,
}

impl ResonanceEmanatedBranch {
    pub const fn germ(&self) -> &ResonanceGerm {
        &self.germ
    }

    pub fn supporting_leaders(&self) -> &BTreeSet<ReceiverFiberIdentity> {
        &self.supporting_leaders
    }
}

/// Plural generative return for a receiver question. No branch is privileged by a scalar score
/// or canonical token order. Every branch can be enacted from the same pre-emanation rest and
/// compared by its complete returned topology or by a genuinely later consequence.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResonanceEmanation {
    radiation: ResonanceRadiation,
    prefix: Vec<ResonanceGerm>,
    branches: Vec<ResonanceEmanatedBranch>,
}

impl ResonanceEmanation {
    pub const fn radiation(&self) -> &ResonanceRadiation {
        &self.radiation
    }

    pub fn prefix(&self) -> &[ResonanceGerm] {
        &self.prefix
    }

    pub fn branches(&self) -> &[ResonanceEmanatedBranch] {
        &self.branches
    }

    /// Form a later self-emanated path from one returned branch. This changes provenance, not
    /// morphology: inherited and generated paths can recur through equal germ boundaries without
    /// becoming the same occurrence.
    pub fn branch_occurrence(
        &self,
        branch: usize,
        source_order: u64,
    ) -> Result<ResonanceOccurrence, ResonanceEcologyError> {
        let branch = self
            .branches
            .get(branch)
            .ok_or(ResonanceEcologyError::EmanationBranchAbsent)?;
        let mut germs = Vec::new();
        germs
            .try_reserve_exact(
                self.prefix
                    .len()
                    .checked_add(1)
                    .ok_or(ResonanceEcologyError::CarrierExtent)?,
            )
            .map_err(|_| ResonanceEcologyError::CarrierExtent)?;
        germs.extend(self.prefix.iter().cloned());
        germs.push(branch.germ.clone());
        ResonanceOccurrence::self_emanated(source_order, germs)
    }
}

/// Immediate testimony for one co-present configuration of independently delivered informants.
/// Vector order is an administrative address only. Each occurrence retains its own internal
/// boundary order and chronology, while the live machine closes shared germs as one antichain.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResonanceConfigurationRadiation {
    source: ContemporaryRadiation,
    reads: LocalSequence<ResonanceOccurrenceRead>,
}

impl ResonanceConfigurationRadiation {
    pub const fn source(&self) -> &ContemporaryRadiation {
        &self.source
    }

    pub fn regional(&self) -> &[RegionalRelationRadiation] {
        self.source.regional()
    }

    pub fn reads(&self) -> &[ResonanceOccurrenceRead] {
        &self.reads
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub enum ResonancePinConduct {
    Open,
    Riding,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ResonancePinWitness {
    antecedent: ReceiverFiberIdentity,
    consequent: ReceiverFiberIdentity,
    conduct: ResonancePinConduct,
}

/// One exact occurrence port whose returned interface conduct is constitutive for the
/// occurrence. This contains no scalar quotient and no delivery position.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct ResonancePinPort {
    antecedent: ReceiverFiberIdentity,
    consequent: ReceiverFiberIdentity,
}

impl ResonancePinPort {
    pub const fn new(antecedent: ReceiverFiberIdentity, consequent: ReceiverFiberIdentity) -> Self {
        Self {
            antecedent,
            consequent,
        }
    }

    pub const fn antecedent(&self) -> &ReceiverFiberIdentity {
        &self.antecedent
    }

    pub const fn consequent(&self) -> &ReceiverFiberIdentity {
        &self.consequent
    }
}

impl ResonancePinWitness {
    pub const fn antecedent(&self) -> &ReceiverFiberIdentity {
        &self.antecedent
    }

    pub const fn consequent(&self) -> &ReceiverFiberIdentity {
        &self.consequent
    }

    pub const fn conduct(&self) -> ResonancePinConduct {
        self.conduct
    }
}

/// Exact structural conduct returned for one identified source occurrence. A Riding return owns
/// its closed interface witnesses; Open retains every unresolved interface. Neither alternative
/// is inferred by an application-side count threshold.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResonanceOccurrenceConduct {
    Open {
        required: LocalSet<ResonancePinPort>,
        returned: LocalSet<ResonancePinWitness>,
    },
    Complete {
        required: LocalSet<ResonancePinPort>,
        returned: LocalSet<ResonancePinWitness>,
    },
}

impl ResonanceOccurrenceConduct {
    pub const fn required(&self) -> &LocalSet<ResonancePinPort> {
        match self {
            Self::Open { required, .. } | Self::Complete { required, .. } => required,
        }
    }

    pub const fn returned(&self) -> &LocalSet<ResonancePinWitness> {
        match self {
            Self::Open { returned, .. } | Self::Complete { returned, .. } => returned,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ResonanceOccurrenceRead {
    occurrence: Option<ReceiverFiberIdentity>,
    constituent: ResonanceConstituentRead,
    conduct: ResonanceOccurrenceConduct,
}

impl ResonanceOccurrenceRead {
    pub const fn occurrence(&self) -> Option<&ReceiverFiberIdentity> {
        self.occurrence.as_ref()
    }

    pub const fn constituent(&self) -> &ResonanceConstituentRead {
        &self.constituent
    }

    pub const fn conduct(&self) -> &ResonanceOccurrenceConduct {
        &self.conduct
    }
}

/// Structural receiver view of a returned resonance component. Informant identities and germ
/// identities are complete fibers, not hashes or observer-assigned scalar labels.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ResonanceConstituentRead {
    informants: LocalSet<ReceiverFiberIdentity>,
    germs: LocalSet<ReceiverFiberIdentity>,
    continuations: LocalRelations<ReceiverFiberIdentity, LocalSet<ReceiverFiberIdentity>>,
    origins: LocalSet<ResonanceOccurrenceOrigin>,
    interfaces: LocalSet<ResonancePinWitness>,
}

impl ResonanceConstituentRead {
    pub const fn informants(&self) -> &LocalSet<ReceiverFiberIdentity> {
        &self.informants
    }

    pub const fn germs(&self) -> &LocalSet<ReceiverFiberIdentity> {
        &self.germs
    }

    pub fn continuations_after(
        &self,
        source: &ReceiverFiberIdentity,
    ) -> Option<&LocalSet<ReceiverFiberIdentity>> {
        self.continuations.get(source)
    }

    pub const fn origins(&self) -> &LocalSet<ResonanceOccurrenceOrigin> {
        &self.origins
    }

    pub const fn interfaces(&self) -> &LocalSet<ResonancePinWitness> {
        &self.interfaces
    }

    pub fn open_pins(&self) -> usize {
        self.interfaces
            .iter()
            .filter(|witness| witness.conduct == ResonancePinConduct::Open)
            .count()
    }

    pub fn riding_pins(&self) -> usize {
        self.interfaces
            .iter()
            .filter(|witness| witness.conduct == ResonancePinConduct::Riding)
            .count()
    }

    pub fn from_constituent(constituent: &LiveConstituent) -> Result<Self, ResonanceEcologyError> {
        let germ_role = role_fiber(GERM_ROLE_WORD);
        let informant_role = role_fiber(INFORMANT_ROLE_WORD);
        let inherited_origin = role_fiber(INHERITED_ORIGIN_ROLE_WORD);
        let question_origin = role_fiber(QUESTION_ORIGIN_ROLE_WORD);
        let emanated_origin = role_fiber(EMANATED_ORIGIN_ROLE_WORD);
        let mut read = Self::default();
        for pin in constituent.pins() {
            let Some(interface) = pin.interface() else {
                continue;
            };
            if interface.origin() != InterfaceCapabilityOrigin::ReceiverCaused {
                continue;
            }
            let Some((antecedent, consequent)) = interface.receiver_fiber() else {
                continue;
            };
            if consequent == &germ_role {
                read.germs.try_insert(antecedent.clone())?;
            } else if consequent == &informant_role {
                read.informants.try_insert(antecedent.clone())?;
            } else if consequent == &inherited_origin {
                read.origins
                    .try_insert(ResonanceOccurrenceOrigin::Inherited)?;
            } else if consequent == &question_origin {
                read.origins
                    .try_insert(ResonanceOccurrenceOrigin::ReceiverQuestion)?;
            } else if consequent == &emanated_origin {
                read.origins
                    .try_insert(ResonanceOccurrenceOrigin::SelfEmanated)?;
            } else if let Some(source) = continuation_source_from_target_role(consequent) {
                if let Some(targets) = read.continuations.get_mut(&source) {
                    targets.try_insert(antecedent.clone())?;
                } else {
                    read.continuations
                        .try_insert(source, LocalSet::from([antecedent.clone()]))?;
                }
            } else {
                continue;
            }
            read.interfaces.try_insert(ResonancePinWitness {
                antecedent: antecedent.clone(),
                consequent: consequent.clone(),
                conduct: if pin.is_open() {
                    ResonancePinConduct::Open
                } else {
                    ResonancePinConduct::Riding
                },
            })?;
        }
        Ok(read)
    }
}

/// Exact rest of the conditioned world membrane. The machine owns every live carrier; this image
/// retains only the exact structural receptor-to-lineage capabilities needed to continue them.
#[derive(Debug, PartialEq, Eq)]
pub struct ResonanceEcologyRestImage {
    machine: LiveCurrentRestImage,
    receptors: BTreeMap<ResonanceReceptorKey, NativeRelationOrganImage>,
}

impl ResonanceEcologyRestImage {
    pub const fn machine(&self) -> &LiveCurrentRestImage {
        &self.machine
    }

    pub fn receptor_count(&self) -> usize {
        self.receptors.len()
    }

    pub fn encode_native_bytes(&self) -> Result<Vec<u8>, ResonanceEcologyError> {
        let machine = self.machine.encode_native_bytes()?;
        let receptor_count = u64::try_from(self.receptors.len())
            .map_err(|_| ResonanceEcologyError::CarrierExtent)?;
        let machine_extent =
            u64::try_from(machine.len()).map_err(|_| ResonanceEcologyError::CarrierExtent)?;
        let mut words = vec![
            REST_MAGIC,
            REST_VERSION,
            machine_extent as u32,
            (machine_extent >> 32) as u32,
            receptor_count as u32,
            (receptor_count >> 32) as u32,
        ];
        for (key, organ) in &self.receptors {
            let identity_extent = u64::try_from(key.identity.words().len())
                .map_err(|_| ResonanceEcologyError::CarrierExtent)?;
            words.extend([
                key.role,
                key.identity.schema() as u32,
                (key.identity.schema() >> 32) as u32,
                identity_extent as u32,
                (identity_extent >> 32) as u32,
            ]);
            words.extend_from_slice(key.identity.words());
            words.extend(key.phase);
            words.extend(organ.encode_native_words());
        }
        let word_bytes = words
            .len()
            .checked_mul(4)
            .ok_or(ResonanceEcologyError::CarrierExtent)?;
        let mut bytes = Vec::new();
        bytes
            .try_reserve_exact(
                word_bytes
                    .checked_add(machine.len())
                    .ok_or(ResonanceEcologyError::CarrierExtent)?,
            )
            .map_err(|_| ResonanceEcologyError::CarrierExtent)?;
        for word in words {
            bytes.extend_from_slice(&word.to_le_bytes());
        }
        bytes.extend_from_slice(&machine);
        Ok(bytes)
    }

    /// Reopen the complete conditioned ecology rest face from its durable little-endian wire.
    /// The receptor rows are accepted only after the enclosed live machine has remounted and each
    /// organ capability names a lineage that machine actually carries.
    pub fn from_native_bytes(bytes: &[u8]) -> Result<Self, ResonanceEcologyError> {
        const HEADER_WORDS: usize = 6;
        const RECEPTOR_HEADER_WORDS: usize = 5;

        let invalid = || ResonanceEcologyError::Live(LiveCurrentError::InvalidRestWire);
        if bytes.len() % core::mem::size_of::<u32>() != 0
            || bytes.len() < HEADER_WORDS * core::mem::size_of::<u32>()
        {
            return Err(invalid());
        }
        let word = |at: usize| {
            let start = at
                .checked_mul(core::mem::size_of::<u32>())
                .ok_or_else(invalid)?;
            let end = start
                .checked_add(core::mem::size_of::<u32>())
                .filter(|end| *end <= bytes.len())
                .ok_or_else(invalid)?;
            let row: [u8; 4] = bytes[start..end].try_into().map_err(|_| invalid())?;
            Ok::<u32, ResonanceEcologyError>(u32::from_le_bytes(row))
        };
        if word(0)? != REST_MAGIC || word(1)? != REST_VERSION {
            return Err(invalid());
        }
        let machine_extent = u64::from(word(2)?) | (u64::from(word(3)?) << 32);
        let receptor_count = u64::from(word(4)?) | (u64::from(word(5)?) << 32);
        let machine_extent = usize::try_from(machine_extent).map_err(|_| invalid())?;
        let receptor_count = usize::try_from(receptor_count).map_err(|_| invalid())?;
        let machine_start = bytes
            .len()
            .checked_sub(machine_extent)
            .filter(|start| {
                *start >= HEADER_WORDS * core::mem::size_of::<u32>()
                    && *start % core::mem::size_of::<u32>() == 0
            })
            .ok_or_else(invalid)?;
        let machine_image = LiveCurrentRestImage::from_native_bytes(&bytes[machine_start..])?;
        let machine = LiveCurrentMachine::from_rest_image(machine_image)?;

        let receptor_bytes = &bytes[..machine_start];
        let mut words = Vec::new();
        words
            .try_reserve_exact(receptor_bytes.len() / core::mem::size_of::<u32>())
            .map_err(|_| ResonanceEcologyError::CarrierExtent)?;
        for row in receptor_bytes.chunks_exact(core::mem::size_of::<u32>()) {
            words.push(u32::from_le_bytes([row[0], row[1], row[2], row[3]]));
        }
        let minimum_receptor_words = RECEPTOR_HEADER_WORDS
            .checked_add(COG_WORDS)
            .and_then(|extent| extent.checked_add(NATIVE_RELATION_ORGAN_WORDS))
            .ok_or(ResonanceEcologyError::CarrierExtent)?;
        if receptor_count
            > words
                .len()
                .saturating_sub(HEADER_WORDS)
                .checked_div(minimum_receptor_words)
                .unwrap_or(0)
        {
            return Err(invalid());
        }

        let capacity_phase = RelationAtom::new(Cog::lit(CAPACITY_ATOM))
            .ok_or(ResonanceEcologyError::CarrierExtent)?
            .words();
        let mut receptors = BTreeMap::new();
        let mut cursor = HEADER_WORDS;
        for _ in 0..receptor_count {
            let header_end = cursor
                .checked_add(RECEPTOR_HEADER_WORDS)
                .filter(|end| *end <= words.len())
                .ok_or_else(invalid)?;
            let role = words[cursor];
            let schema = u64::from(words[cursor + 1]) | (u64::from(words[cursor + 2]) << 32);
            let identity_extent =
                u64::from(words[cursor + 3]) | (u64::from(words[cursor + 4]) << 32);
            let identity_extent = usize::try_from(identity_extent).map_err(|_| invalid())?;
            cursor = header_end;
            let identity_end = cursor
                .checked_add(identity_extent)
                .filter(|end| *end <= words.len())
                .ok_or_else(invalid)?;
            let identity = ReceiverFiberIdentity::new(schema, words[cursor..identity_end].to_vec());
            cursor = identity_end;
            let phase_end = cursor
                .checked_add(COG_WORDS)
                .filter(|end| *end <= words.len())
                .ok_or_else(invalid)?;
            let phase: [u32; COG_WORDS] =
                words[cursor..phase_end].try_into().map_err(|_| invalid())?;
            if RelationAtom::from_words(phase).is_none()
                || !matches!(
                    role,
                    GERM_RECEPTOR | INFORMANT_MARKER_RECEPTOR | INFORMANT_CAPACITY_RECEPTOR
                )
                || (role != GERM_RECEPTOR && phase != capacity_phase)
            {
                return Err(invalid());
            }
            cursor = phase_end;
            let organ_end = cursor
                .checked_add(NATIVE_RELATION_ORGAN_WORDS)
                .filter(|end| *end <= words.len())
                .ok_or_else(invalid)?;
            let organ =
                NativeRelationOrganImage::from_native_words(&words[cursor..organ_end], &machine)?;
            cursor = organ_end;
            let key = ResonanceReceptorKey {
                role,
                identity,
                phase,
            };
            if receptors.insert(key, organ).is_some() {
                return Err(invalid());
            }
        }
        if cursor != words.len() {
            return Err(invalid());
        }
        Ok(Self {
            machine: machine.rest_image()?,
            receptors,
        })
    }
}

mod ecology;
#[cfg(test)]
mod tests;

pub use self::ecology::ResonanceEcology;

fn origin_role_word(origin: ResonanceOccurrenceOrigin) -> u32 {
    match origin {
        ResonanceOccurrenceOrigin::Inherited => INHERITED_ORIGIN_ROLE_WORD,
        ResonanceOccurrenceOrigin::ReceiverQuestion => QUESTION_ORIGIN_ROLE_WORD,
        ResonanceOccurrenceOrigin::SelfEmanated => EMANATED_ORIGIN_ROLE_WORD,
    }
}

fn continuation_target_role(
    source: &ReceiverFiberIdentity,
) -> Result<ReceiverFiberIdentity, ResonanceEcologyError> {
    let extent =
        u64::try_from(source.words().len()).map_err(|_| ResonanceEcologyError::CarrierExtent)?;
    let mut words = Vec::new();
    words
        .try_reserve_exact(
            4usize
                .checked_add(source.words().len())
                .ok_or(ResonanceEcologyError::CarrierExtent)?,
        )
        .map_err(|_| ResonanceEcologyError::CarrierExtent)?;
    words.extend([
        source.schema() as u32,
        (source.schema() >> 32) as u32,
        extent as u32,
        (extent >> 32) as u32,
    ]);
    words.extend_from_slice(source.words());
    Ok(ReceiverFiberIdentity::new(
        CONTINUATION_TARGET_SCHEMA,
        words,
    ))
}

fn continuation_source_from_target_role(
    role: &ReceiverFiberIdentity,
) -> Option<ReceiverFiberIdentity> {
    if role.schema() != CONTINUATION_TARGET_SCHEMA || role.words().len() < 4 {
        return None;
    }
    let words = role.words();
    let schema = u64::from(words[0]) | (u64::from(words[1]) << 32);
    let extent = u64::from(words[2]) | (u64::from(words[3]) << 32);
    let extent = usize::try_from(extent).ok()?;
    (words.len() == 4usize.checked_add(extent)?)
        .then(|| ReceiverFiberIdentity::new(schema, words[4..].to_vec()))
}

fn path_fiber(
    schema: u64,
    germs: &[ResonanceGerm],
) -> Result<ReceiverFiberIdentity, ResonanceEcologyError> {
    let count = u64::try_from(germs.len()).map_err(|_| ResonanceEcologyError::CarrierExtent)?;
    let mut extent = 2usize;
    for germ in germs {
        extent = extent
            .checked_add(4)
            .and_then(|extent| extent.checked_add(germ.identity.words().len()))
            .and_then(|extent| extent.checked_add(COG_WORDS))
            .ok_or(ResonanceEcologyError::CarrierExtent)?;
    }
    let mut words = Vec::new();
    words
        .try_reserve_exact(extent)
        .map_err(|_| ResonanceEcologyError::CarrierExtent)?;
    words.extend([count as u32, (count >> 32) as u32]);
    for germ in germs {
        let identity_extent = u64::try_from(germ.identity.words().len())
            .map_err(|_| ResonanceEcologyError::CarrierExtent)?;
        words.extend([
            germ.identity.schema() as u32,
            (germ.identity.schema() >> 32) as u32,
            identity_extent as u32,
            (identity_extent >> 32) as u32,
        ]);
        words.extend_from_slice(germ.identity.words());
        words.extend(germ.phase.words());
    }
    Ok(ReceiverFiberIdentity::new(schema, words))
}

pub fn fiber_from_bytes(schema: u64, bytes: &[u8]) -> ReceiverFiberIdentity {
    let mut words = Vec::with_capacity(2 + bytes.len().div_ceil(4));
    let length = bytes.len() as u64;
    words.extend([length as u32, (length >> 32) as u32]);
    for chunk in bytes.chunks(4) {
        let mut word = [0u8; 4];
        word[..chunk.len()].copy_from_slice(chunk);
        words.push(u32::from_le_bytes(word));
    }
    ReceiverFiberIdentity::new(schema, words)
}

fn role_fiber(role: u32) -> ReceiverFiberIdentity {
    ReceiverFiberIdentity::new(ROLE_SCHEMA, [role])
}
