//! W2's pure structural condensation owner.
//!
//! This is an example-local helper rather than a new engine cabinet.  W1 authenticates the
//! foreign occurrence and its native correspondence; this owner only asks whether a *declared*
//! future/intervention receiver family can factor a finite operation population.  It does not
//! inspect weights, run a sensitivity census, launch CUDA, or quote a byte ratio.  A quotient is
//! lawful only when its successor conduct factors, and every collapsed pair keeps its shortest
//! separating word as a reconstruction fibre.
//!
//! The QK/OV/KV declarations are H3 structural receipts.  They are carried verbatim and checked
//! against W1 bindings; they are never rediscovered from names, counts, or file size.

use std::collections::{BTreeMap, BTreeSet};

use holonic_engine::operation_correspondence::{
    NativeOperationBinding, OperationCorrespondenceSeal, OperationResolution,
};
use holonic_engine::receiver_exact_compression::{
    CollapsedPair, InputId, ItemId, Observation, ObservedSystem, Partition,
    ReceiverExactCompression, ReceiverId, compress,
};

/// A receiver face declared before condensation.  A missing value is refused: a receiver must
/// answer every admitted state, rather than silently turning an unknown into an equal value.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiverSignature {
    pub name: String,
    pub values: BTreeMap<String, u64>,
}

/// One named successor relation.  Missing entries mean a declared terminus, not an implicit
/// self-loop.  Every present target must belong to the admitted state closure.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SuccessorSignature {
    pub input: String,
    pub next: BTreeMap<String, String>,
}

/// A state in the finite operation closure. `id` is the declared deed/family state, while
/// `source_members` is its complete source-operation fibre.  State identity is therefore not
/// inferred from an ordinal and a deed is never mistaken for one isolated operation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CondensationState {
    pub id: String,
    pub source_members: Vec<String>,
}

/// H3's preserved sharing/transport declaration.  The members are source operation ids, and the
/// kind is a receiver-facing label only; the native correspondence remains the authority.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, serde::Serialize)]
pub enum StructureKind {
    Qk,
    Ov,
    Kv,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SharingDeclaration {
    pub family: String,
    pub kind: StructureKind,
    /// Deed states whose receiver/factor status is being reported.
    pub states: Vec<String>,
    /// Exact source-operation subset carrying this declared structure. The owner never expands
    /// a state into every operation merely because the state is named.
    pub source_members: Vec<String>,
}

/// Input to the W2 pure owner.  `seal` is authenticated W1 standing; all other fields are
/// declarations of the receiver family and its causal successor face.
pub struct CondensationInput<'a> {
    pub seal: &'a OperationCorrespondenceSeal,
    pub states: Vec<CondensationState>,
    pub receivers: Vec<ReceiverSignature>,
    pub successors: Vec<SuccessorSignature>,
    pub sharing: Vec<SharingDeclaration>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct SeparationWitness {
    pub left: String,
    pub right: String,
    pub word: Vec<String>,
    pub receiver: Option<String>,
    pub left_observation: Option<u64>,
    pub right_observation: Option<u64>,
    pub separated_by_terminus: bool,
}

/// The retained fibre for one one-shot quotient candidate.  `members` is never replaced by a
/// cardinality; `conduct_blocks` gives the exact refinement and `separators` reopens every known
/// split.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct ReconstructionFiber {
    pub candidate: Vec<String>,
    pub conduct_blocks: Vec<Vec<String>>,
    pub separators: Vec<SeparationWitness>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct FactorizationDefect {
    pub block: Vec<String>,
    pub input: String,
    pub left: String,
    pub right: String,
    pub left_target: Option<String>,
    pub right_target: Option<String>,
}

/// A deterministic transition factors through a partition when equal members have equal target
/// blocks and equal termination status for every declared input.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct DynamicFactorization {
    pub partition: String,
    pub holds: bool,
    pub checked_members: usize,
    pub defects: Vec<FactorizationDefect>,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub enum CandidateStatus {
    Exact,
    RequiresRefinement,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct QuotientCandidate {
    pub members: Vec<String>,
    pub conduct_blocks: Vec<Vec<String>>,
    pub status: CandidateStatus,
    pub factorization: DynamicFactorization,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub enum SharingStatus {
    Preserved { conduct_block: Vec<String> },
    Separated { witnesses: Vec<SeparationWitness> },
    Open { reason: String },
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct PreservedStructure {
    pub family: String,
    pub kind: StructureKind,
    pub state_members: Vec<String>,
    pub source_members: Vec<String>,
    pub bindings: Vec<NativeBindingFace>,
    pub status: SharingStatus,
}

/// The binding face retained with a QK/OV/KV structure.  It is a complete W1 relation, not a
/// guessed equivalence of resident law names.
#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct NativeBindingFace {
    pub source_id: String,
    pub resident_law: String,
    pub native_population: Option<String>,
    pub graph_key: String,
}

#[derive(Clone, Debug, PartialEq, Eq, serde::Serialize)]
pub struct NoFactorRemainder {
    pub candidate: Vec<String>,
    pub reason: String,
    pub witnesses: Vec<SeparationWitness>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CondensationResult {
    pub schema: String,
    pub source_operations: usize,
    pub candidates: Vec<QuotientCandidate>,
    pub reconstruction: Vec<ReconstructionFiber>,
    pub no_factor: Vec<NoFactorRemainder>,
    pub structures: Vec<PreservedStructure>,
    pub open_source_operations: Vec<String>,
    pub compression: ReceiverExactCompression,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CondensationRefusal {
    Correspondence(String),
    EmptyStateClosure,
    DuplicateState(String),
    ForeignState(String),
    EmptyStateMembers(String),
    DuplicateSourceMember(String),
    MissingSourceMember(String),
    ForeignSourceMember {
        state: String,
        member: String,
    },
    EmptyReceiver,
    DuplicateReceiver(String),
    MissingObservation {
        receiver: String,
        state: String,
    },
    EmptyInput,
    DuplicateInput(String),
    ForeignSuccessor {
        input: String,
        state: String,
        target: String,
    },
    DuplicateStructure(String),
    EmptyStructureStates(String),
    DuplicateStructureState {
        family: String,
        state: String,
    },
    EmptyStructureSourceMembers(String),
    DuplicateStructureSourceMember {
        family: String,
        member: String,
    },
    StructureSourceMemberOutsideState {
        family: String,
        member: String,
    },
    ForeignStructureMember {
        family: String,
        member: String,
    },
}

impl std::fmt::Display for CondensationRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Correspondence(e) => write!(f, "authenticated W1 correspondence refused: {e}"),
            Self::EmptyStateClosure => f.write_str("condensation state closure is empty"),
            Self::DuplicateState(id) => write!(f, "duplicate condensation state {id:?}"),
            Self::ForeignState(id) => write!(f, "state is foreign to W1 source closure {id:?}"),
            Self::EmptyStateMembers(id) => write!(f, "state {id:?} has no source members"),
            Self::DuplicateSourceMember(id) => {
                write!(f, "source operation occurs in more than one state {id:?}")
            }
            Self::MissingSourceMember(id) => {
                write!(f, "W1 source operation has no containing state {id:?}")
            }
            Self::ForeignSourceMember { state, member } => write!(
                f,
                "state {state:?} names a source operation outside W1 {member:?}"
            ),
            Self::EmptyReceiver => f.write_str("receiver name is empty"),
            Self::DuplicateReceiver(id) => write!(f, "duplicate receiver {id:?}"),
            Self::MissingObservation { receiver, state } => {
                write!(f, "receiver {receiver:?} has no observation for {state:?}")
            }
            Self::EmptyInput => f.write_str("successor input name is empty"),
            Self::DuplicateInput(id) => write!(f, "duplicate successor input {id:?}"),
            Self::ForeignSuccessor {
                input,
                state,
                target,
            } => write!(
                f,
                "input {input:?} from {state:?} names foreign target {target:?}"
            ),
            Self::DuplicateStructure(id) => write!(f, "duplicate sharing family {id:?}"),
            Self::EmptyStructureStates(id) => write!(f, "sharing family {id:?} has no states"),
            Self::DuplicateStructureState { family, state } => {
                write!(f, "sharing family {family:?} repeats state {state:?}")
            }
            Self::EmptyStructureSourceMembers(id) => {
                write!(f, "sharing family {id:?} has no source members")
            }
            Self::DuplicateStructureSourceMember { family, member } => write!(
                f,
                "sharing family {family:?} repeats source member {member:?}"
            ),
            Self::StructureSourceMemberOutsideState { family, member } => write!(
                f,
                "sharing family {family:?} selects source member outside its declared states {member:?}"
            ),
            Self::ForeignStructureMember { family, member } => {
                write!(
                    f,
                    "sharing family {family:?} names foreign member {member:?}"
                )
            }
        }
    }
}

impl std::error::Error for CondensationRefusal {}

struct FiniteSystem {
    ids: Vec<String>,
    observations: Vec<Vec<u64>>,
    inputs: Vec<String>,
    successors: Vec<Vec<Option<usize>>>,
}

impl ObservedSystem for FiniteSystem {
    fn items(&self) -> Vec<ItemId> {
        (0..self.ids.len()).map(|id| ItemId(id as u64)).collect()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        (0..self.observations.first().map_or(0, Vec::len))
            .map(|id| ReceiverId(id as u64))
            .collect()
    }

    fn inputs(&self) -> Vec<InputId> {
        (0..self.inputs.len())
            .map(|id| InputId(id as u64))
            .collect()
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        Observation(self.observations[item.0 as usize][receiver.0 as usize])
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        self.successors[input.0 as usize][item.0 as usize].map(|id| ItemId(id as u64))
    }

    fn admitted(&self, input: InputId) -> Option<Vec<(ItemId, ItemId)>> {
        Some(
            self.successors[input.0 as usize]
                .iter()
                .enumerate()
                .filter_map(|(state, next)| {
                    next.map(|next| (ItemId(state as u64), ItemId(next as u64)))
                })
                .collect(),
        )
    }
}

/// Perform W2's structural return.  This is intentionally pure and finite: W1's complete seal is
/// authenticated first, and all later values are supplied receiver faces or exact successor
/// addresses.  No byte size, weight norm, or census can produce a condensation here.
pub fn condense(input: CondensationInput<'_>) -> Result<CondensationResult, CondensationRefusal> {
    input
        .seal
        .validate()
        .map_err(|error| CondensationRefusal::Correspondence(error.to_string()))?;
    let source_ids = input
        .seal
        .source_operations
        .iter()
        .map(|operation| operation.id.clone())
        .collect::<BTreeSet<_>>();
    if input.states.is_empty() {
        return Err(CondensationRefusal::EmptyStateClosure);
    }
    let mut state_ids = Vec::with_capacity(input.states.len());
    let mut positions = BTreeMap::new();
    let mut source_membership = BTreeMap::<String, String>::new();
    for state in &input.states {
        if state.id.is_empty() {
            return Err(CondensationRefusal::ForeignState(state.id.clone()));
        }
        if state.source_members.is_empty() {
            return Err(CondensationRefusal::EmptyStateMembers(state.id.clone()));
        }
        if positions
            .insert(state.id.clone(), state_ids.len())
            .is_some()
        {
            return Err(CondensationRefusal::DuplicateState(state.id.clone()));
        }
        state_ids.push(state.id.clone());
        for member in &state.source_members {
            if !source_ids.contains(member) {
                return Err(CondensationRefusal::ForeignSourceMember {
                    state: state.id.clone(),
                    member: member.clone(),
                });
            }
            if source_membership
                .insert(member.clone(), state.id.clone())
                .is_some()
            {
                return Err(CondensationRefusal::DuplicateSourceMember(member.clone()));
            }
        }
    }
    for source_id in &source_ids {
        if !source_membership.contains_key(source_id) {
            return Err(CondensationRefusal::MissingSourceMember(source_id.clone()));
        }
    }

    let mut receiver_positions = BTreeMap::new();
    let mut observations = vec![Vec::with_capacity(input.receivers.len()); state_ids.len()];
    for receiver in &input.receivers {
        if receiver.name.is_empty() {
            return Err(CondensationRefusal::EmptyReceiver);
        }
        if receiver_positions
            .insert(receiver.name.clone(), receiver_positions.len())
            .is_some()
        {
            return Err(CondensationRefusal::DuplicateReceiver(
                receiver.name.clone(),
            ));
        }
        for (index, state) in state_ids.iter().enumerate() {
            let value = receiver.values.get(state).ok_or_else(|| {
                CondensationRefusal::MissingObservation {
                    receiver: receiver.name.clone(),
                    state: state.clone(),
                }
            })?;
            observations[index].push(*value);
        }
    }
    if input.receivers.is_empty() {
        return Err(CondensationRefusal::EmptyReceiver);
    }

    let mut input_positions = BTreeMap::new();
    let mut successors = Vec::with_capacity(input.successors.len());
    for transition in &input.successors {
        if transition.input.is_empty() {
            return Err(CondensationRefusal::EmptyInput);
        }
        if input_positions
            .insert(transition.input.clone(), input_positions.len())
            .is_some()
        {
            return Err(CondensationRefusal::DuplicateInput(
                transition.input.clone(),
            ));
        }
        let mut row = vec![None; state_ids.len()];
        for (source, target) in &transition.next {
            let Some(&source_at) = positions.get(source) else {
                return Err(CondensationRefusal::ForeignSuccessor {
                    input: transition.input.clone(),
                    state: source.clone(),
                    target: target.clone(),
                });
            };
            let Some(&target_at) = positions.get(target) else {
                return Err(CondensationRefusal::ForeignSuccessor {
                    input: transition.input.clone(),
                    state: source.clone(),
                    target: target.clone(),
                });
            };
            row[source_at] = Some(target_at);
        }
        successors.push(row);
    }
    if input.successors.is_empty() {
        return Err(CondensationRefusal::EmptyInput);
    }

    let system = FiniteSystem {
        ids: state_ids.clone(),
        observations,
        inputs: input
            .successors
            .iter()
            .map(|transition| transition.input.clone())
            .collect(),
        successors,
    };
    let compression = compress(&system);
    let conduct_index = compression.conduct.index();
    let one_shot_index = compression.one_shot.index();
    let mut candidate_rows = Vec::new();
    let mut reconstruction = Vec::new();
    let mut no_factor = Vec::new();
    for block in &compression.one_shot.blocks {
        let members = block
            .iter()
            .map(|item| state_ids[item.0 as usize].clone())
            .collect::<Vec<_>>();
        let mut conduct_blocks = BTreeMap::<usize, Vec<String>>::new();
        for item in block {
            let conduct_block = conduct_index
                .block_of(*item)
                .expect("compression contains every item");
            conduct_blocks
                .entry(conduct_block)
                .or_default()
                .push(state_ids[item.0 as usize].clone());
        }
        let conduct_blocks = conduct_blocks.into_values().collect::<Vec<_>>();
        let factorization = factorization(
            &system,
            block,
            &compression.one_shot,
            "one-shot",
            &input.successors,
        );
        // A local one-step factorization is necessary but not sufficient: another one-shot block
        // can split later and feed that distinction back through this block. The complete
        // Moore/Nerode conduct partition is the future-family answer.
        let conduct_exact = conduct_blocks.len() == 1;
        let status = if conduct_exact {
            CandidateStatus::Exact
        } else {
            CandidateStatus::RequiresRefinement
        };
        if !conduct_exact {
            let witnesses = witnesses_for_block(
                &compression.collapsed,
                block,
                &state_ids,
                &input.receivers,
                &input.successors,
            );
            no_factor.push(NoFactorRemainder {
                candidate: members.clone(),
                reason: if factorization.holds {
                    "the one-step target block agrees, but the complete successor history reopens this candidate after another block refines"
                        .to_owned()
                } else {
                    "the declared successor already reaches distinct one-shot target blocks"
                        .to_owned()
                },
                witnesses,
            });
        }
        if members.len() > 1 {
            reconstruction.push(ReconstructionFiber {
                candidate: members.clone(),
                conduct_blocks: conduct_blocks.clone(),
                separators: witnesses_for_block(
                    &compression.collapsed,
                    block,
                    &state_ids,
                    &input.receivers,
                    &input.successors,
                ),
            });
        }
        candidate_rows.push(QuotientCandidate {
            members,
            conduct_blocks,
            status,
            factorization,
        });
    }

    let mut structures = Vec::new();
    let mut seen_structures = BTreeSet::new();
    let operation_by_id = input
        .seal
        .operations
        .iter()
        .map(|operation| (operation.source_id.as_str(), operation))
        .collect::<BTreeMap<_, _>>();
    for declaration in &input.sharing {
        if declaration.family.is_empty() {
            return Err(CondensationRefusal::DuplicateStructure(
                declaration.family.clone(),
            ));
        }
        if !seen_structures.insert(declaration.family.clone()) {
            return Err(CondensationRefusal::DuplicateStructure(
                declaration.family.clone(),
            ));
        }
        if declaration.states.is_empty() {
            return Err(CondensationRefusal::EmptyStructureStates(
                declaration.family.clone(),
            ));
        }
        let mut structure_states = BTreeSet::new();
        for state in &declaration.states {
            if !positions.contains_key(state) {
                return Err(CondensationRefusal::ForeignStructureMember {
                    family: declaration.family.clone(),
                    member: state.clone(),
                });
            }
            if !structure_states.insert(state.clone()) {
                return Err(CondensationRefusal::DuplicateStructureState {
                    family: declaration.family.clone(),
                    state: state.clone(),
                });
            }
        }
        if declaration.source_members.is_empty() {
            return Err(CondensationRefusal::EmptyStructureSourceMembers(
                declaration.family.clone(),
            ));
        }
        let mut bindings = Vec::new();
        let mut item_ids = Vec::new();
        let mut open = None;
        let mut selected_sources = BTreeSet::new();
        for member in &declaration.states {
            let Some(&state_at) = positions.get(member) else {
                return Err(CondensationRefusal::ForeignStructureMember {
                    family: declaration.family.clone(),
                    member: member.clone(),
                });
            };
            item_ids.push(ItemId(state_at as u64));
        }
        for source_member in &declaration.source_members {
            let Some(state) = source_membership.get(source_member) else {
                return Err(CondensationRefusal::ForeignStructureMember {
                    family: declaration.family.clone(),
                    member: source_member.clone(),
                });
            };
            if !structure_states.contains(state) {
                return Err(CondensationRefusal::StructureSourceMemberOutsideState {
                    family: declaration.family.clone(),
                    member: source_member.clone(),
                });
            }
            if !selected_sources.insert(source_member.clone()) {
                return Err(CondensationRefusal::DuplicateStructureSourceMember {
                    family: declaration.family.clone(),
                    member: source_member.clone(),
                });
            }
            match operation_by_id
                .get(source_member.as_str())
                .map(|operation| &operation.resolution)
            {
                Some(OperationResolution::Native(binding)) => bindings.push(binding_face(binding)),
                Some(OperationResolution::Open(remainder)) => open = Some(remainder.reason.clone()),
                None => open = Some("W1 operation disposition is absent".to_owned()),
            }
        }
        let status = if let Some(reason) = open {
            SharingStatus::Open { reason }
        } else if item_ids
            .iter()
            .map(|item| one_shot_index.block_of(*item))
            .collect::<BTreeSet<_>>()
            .len()
            > 1
        {
            SharingStatus::Separated {
                witnesses: direct_witnesses(&item_ids, &system, &input.receivers),
            }
        } else {
            let block = one_shot_index
                .block_of(item_ids[0])
                .expect("state belongs to one-shot partition");
            let members = compression.one_shot.blocks[block]
                .iter()
                .map(|item| state_ids[item.0 as usize].clone())
                .collect();
            let witnesses = witnesses_for_items(
                &compression.collapsed,
                &item_ids,
                &state_ids,
                &input.receivers,
                &input.successors,
            );
            if witnesses.is_empty() {
                SharingStatus::Preserved {
                    conduct_block: members,
                }
            } else {
                SharingStatus::Separated { witnesses }
            }
        };
        structures.push(PreservedStructure {
            family: declaration.family.clone(),
            kind: declaration.kind,
            state_members: declaration.states.clone(),
            source_members: declaration.source_members.clone(),
            bindings,
            status,
        });
    }

    let open_source_operations = input
        .seal
        .operations
        .iter()
        .filter_map(|operation| {
            matches!(operation.resolution, OperationResolution::Open(_))
                .then_some(operation.source_id.clone())
        })
        .collect();
    Ok(CondensationResult {
        schema: "holonic-engine.phoenix.w2-structural-condensation.v1".to_owned(),
        source_operations: source_ids.len(),
        candidates: candidate_rows,
        reconstruction,
        no_factor,
        structures,
        open_source_operations,
        compression,
    })
}

fn binding_face(binding: &NativeOperationBinding) -> NativeBindingFace {
    NativeBindingFace {
        source_id: binding.source_id.clone(),
        resident_law: binding.resident_law.clone(),
        native_population: binding.native_population.clone(),
        graph_key: binding.graph_key.clone(),
    }
}

fn factorization(
    system: &FiniteSystem,
    block: &BTreeSet<ItemId>,
    partition: &Partition,
    name: &str,
    inputs: &[SuccessorSignature],
) -> DynamicFactorization {
    let mut defects = Vec::new();
    let mut members = block.iter();
    let Some(&first) = members.next() else {
        return DynamicFactorization {
            partition: name.to_owned(),
            holds: true,
            checked_members: 0,
            defects,
        };
    };
    for &other in members {
        for (input_at, declaration) in inputs.iter().enumerate() {
            let left = system.successors[input_at][first.0 as usize]
                .map(|target| partition.block_of(ItemId(target as u64)).unwrap());
            let right = system.successors[input_at][other.0 as usize]
                .map(|target| partition.block_of(ItemId(target as u64)).unwrap());
            if left != right {
                defects.push(FactorizationDefect {
                    block: block
                        .iter()
                        .map(|item| system.ids[item.0 as usize].clone())
                        .collect(),
                    input: declaration.input.clone(),
                    left: system.ids[first.0 as usize].clone(),
                    right: system.ids[other.0 as usize].clone(),
                    left_target: system.successors[input_at][first.0 as usize]
                        .map(|target| system.ids[target].clone()),
                    right_target: system.successors[input_at][other.0 as usize]
                        .map(|target| system.ids[target].clone()),
                });
            }
        }
    }
    DynamicFactorization {
        partition: name.to_owned(),
        holds: defects.is_empty(),
        checked_members: block.len(),
        defects,
    }
}

fn witnesses_for_block(
    collapsed: &[CollapsedPair],
    block: &BTreeSet<ItemId>,
    ids: &[String],
    receivers: &[ReceiverSignature],
    inputs: &[SuccessorSignature],
) -> Vec<SeparationWitness> {
    let allowed = block.iter().copied().collect::<BTreeSet<_>>();
    collapsed
        .iter()
        .filter(|pair| allowed.contains(&pair.left) && allowed.contains(&pair.right))
        .map(|pair| witness(pair, ids, receivers, inputs))
        .collect()
}

fn witnesses_for_items(
    collapsed: &[CollapsedPair],
    items: &[ItemId],
    ids: &[String],
    receivers: &[ReceiverSignature],
    inputs: &[SuccessorSignature],
) -> Vec<SeparationWitness> {
    let allowed = items.iter().copied().collect::<BTreeSet<_>>();
    collapsed
        .iter()
        .filter(|pair| allowed.contains(&pair.left) && allowed.contains(&pair.right))
        .map(|pair| witness(pair, ids, receivers, inputs))
        .collect()
}

fn witness(
    pair: &CollapsedPair,
    ids: &[String],
    receivers: &[ReceiverSignature],
    inputs: &[SuccessorSignature],
) -> SeparationWitness {
    SeparationWitness {
        left: ids[pair.left.0 as usize].clone(),
        right: ids[pair.right.0 as usize].clone(),
        word: pair
            .distinguishing_word
            .iter()
            .map(|input| inputs[input.0 as usize].input.clone())
            .collect(),
        receiver: pair.witness.and_then(|(receiver, _, _)| {
            receivers
                .get(receiver.0 as usize)
                .map(|receiver| receiver.name.clone())
        }),
        left_observation: pair.witness.map(|(_, left, _)| left.0),
        right_observation: pair.witness.map(|(_, _, right)| right.0),
        separated_by_terminus: pair.separated_by_terminus,
    }
}

fn direct_witnesses(
    items: &[ItemId],
    system: &FiniteSystem,
    receivers: &[ReceiverSignature],
) -> Vec<SeparationWitness> {
    let mut witnesses = Vec::new();
    for (left_at, left) in items.iter().enumerate() {
        for right in &items[left_at + 1..] {
            for (receiver_at, receiver) in receivers.iter().enumerate() {
                let left_value = system.observations[left.0 as usize][receiver_at];
                let right_value = system.observations[right.0 as usize][receiver_at];
                if left_value != right_value {
                    witnesses.push(SeparationWitness {
                        left: system.ids[left.0 as usize].clone(),
                        right: system.ids[right.0 as usize].clone(),
                        word: Vec::new(),
                        receiver: Some(receiver.name.clone()),
                        left_observation: Some(left_value),
                        right_observation: Some(right_value),
                        separated_by_terminus: false,
                    });
                    break;
                }
            }
        }
    }
    witnesses
}

#[cfg(test)]
#[path = "lifted_condensation_tests.rs"]
mod tests;
