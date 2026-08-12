//! Carrier-neutral causal sections and their exact receiver/history quotient.
//!
//! A section owns an oriented incidence complex and a finite exact consequence graph. Surface,
//! codec lineage, and declared contact faces remain inspectable, but none participates in the
//! quotient. The only classifier is `receiver_exact_compression`: two root presentations share a
//! reaction fiber exactly while every admitted receiver and successor history agrees.

use std::collections::{BTreeMap, BTreeSet};

#[cfg(test)]
use holonic_engine::receiver_exact_compression::compress;
use holonic_engine::{
    cuda_refine::CudaRefineExecutor,
    receiver_exact_compression::{
        compress_on_device, InputId, ItemId, Observation, ObservedSystem, ReceiverExactCompression,
        ReceiverId,
    },
};
use num_bigint::BigUint;

use crate::incidence_production::IncidenceComplex;

/// One exact state of a presented construction. Receiver and intervention names are exterior port
/// faces; their values are exact opaque inscriptions and are never ordered or scored.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SectionState {
    pub observations: BTreeMap<String, String>,
    pub successors: BTreeMap<String, usize>,
}

/// One presentation of a causal law. It is intentionally not `Clone`: the ecology takes ownership
/// of the presentation rather than duplicating one world for alternative readings.
#[derive(Debug)]
pub struct CausalSection {
    pub identity: String,
    pub lineage: String,
    pub incidence: IncidenceComplex,
    pub states: Vec<SectionState>,
    pub root: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CausalSectionError {
    EmptyEcology,
    EmptyIdentity,
    DuplicateIdentity(String),
    EmptyLineage(String),
    EmptyStateFamily(String),
    RootOutsideStateFamily(String),
    ReceiverFamilyDisagrees(String),
    EmptyReceiverFamily,
    UnknownReceiver(String),
    SuccessorOutsideStateFamily {
        section: String,
        state: usize,
        successor: usize,
    },
    ContactFaceWasErased(String),
    DeviceRefused(String),
    Extent,
}

impl std::fmt::Display for CausalSectionError {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::EmptyEcology => write!(formatter, "no causal section was supplied"),
            Self::EmptyIdentity => write!(formatter, "a causal section has no identity"),
            Self::DuplicateIdentity(identity) => {
                write!(formatter, "two causal sections share {identity}")
            }
            Self::EmptyLineage(identity) => write!(formatter, "section {identity} has no lineage"),
            Self::EmptyStateFamily(identity) => {
                write!(formatter, "section {identity} has no consequence states")
            }
            Self::RootOutsideStateFamily(identity) => {
                write!(
                    formatter,
                    "section {identity}'s root is outside its state family"
                )
            }
            Self::ReceiverFamilyDisagrees(identity) => {
                write!(
                    formatter,
                    "section {identity} changes receiver family between states"
                )
            }
            Self::EmptyReceiverFamily => write!(formatter, "the receiver family is empty"),
            Self::UnknownReceiver(receiver) => write!(formatter, "unknown receiver {receiver}"),
            Self::SuccessorOutsideStateFamily {
                section,
                state,
                successor,
            } => write!(
                formatter,
                "section {section} state {state} points outside its family to {successor}"
            ),
            Self::ContactFaceWasErased(identity) => {
                write!(
                    formatter,
                    "section {identity} contains a bond with no contact face"
                )
            }
            Self::DeviceRefused(refusal) => {
                write!(
                    formatter,
                    "the resident quotient refused the section front: {refusal}"
                )
            }
            Self::Extent => write!(formatter, "the causal-section carrier extent overflowed"),
        }
    }
}

impl std::error::Error for CausalSectionError {}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SectionPresentationReading {
    pub identity: String,
    pub lineage: String,
    pub states: usize,
    pub sites: usize,
    pub bonds: usize,
    pub compounds: usize,
    pub contact_faces: BTreeSet<String>,
}

/// The complete root preimage of one stable conduct block. No representative is selected.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SectionReconstructionFiber {
    pub presentations: BTreeSet<String>,
    pub outside_declared_population_open: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SectionSeparator {
    pub left: String,
    pub right: String,
    pub interventions: Vec<String>,
    pub receiver: Option<String>,
    pub left_observation: Option<String>,
    pub right_observation: Option<String>,
    pub separated_by_terminus: bool,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SectionWork {
    pub presentations: u64,
    pub states: u64,
    pub contacts: u64,
    pub transitions: u64,
    pub observations: u64,
    pub complete_state_pair_chart: BigUint,
}

#[derive(Debug, PartialEq, Eq)]
pub struct CausalSectionReading {
    pub schema: String,
    pub receivers: BTreeSet<String>,
    pub presentations: Vec<SectionPresentationReading>,
    pub root_one_shot_blocks: Vec<BTreeSet<String>>,
    pub root_conduct_blocks: Vec<BTreeSet<String>>,
    pub reconstruction_fibers: Vec<SectionReconstructionFiber>,
    pub shortest_separators: Vec<SectionSeparator>,
    pub compression: ReceiverExactCompression,
    pub work: SectionWork,
}

/// One continuing owner of a declared finite section population.
#[derive(Debug)]
pub struct CausalSectionEcology {
    sections: Vec<CausalSection>,
    locations: Vec<(usize, usize)>,
    offsets: Vec<usize>,
    receiver_names: Vec<String>,
    receiver_index: BTreeMap<String, ReceiverId>,
    input_names: Vec<String>,
    observation_names: Vec<String>,
    observation_index: BTreeMap<String, Observation>,
    work: SectionWork,
}

impl CausalSectionEcology {
    pub fn found(sections: Vec<CausalSection>) -> Result<Self, CausalSectionError> {
        if sections.is_empty() {
            return Err(CausalSectionError::EmptyEcology);
        }
        let mut identities = BTreeSet::new();
        let mut receiver_family: Option<BTreeSet<String>> = None;
        let mut inputs = BTreeSet::new();
        let mut observations = BTreeSet::new();
        let mut locations = Vec::new();
        let mut offsets = Vec::with_capacity(sections.len());
        let mut contacts = 0u64;
        let mut transitions = 0u64;
        let mut observation_count = 0u64;

        for (section_at, section) in sections.iter().enumerate() {
            if section.identity.is_empty() {
                return Err(CausalSectionError::EmptyIdentity);
            }
            if !identities.insert(section.identity.clone()) {
                return Err(CausalSectionError::DuplicateIdentity(
                    section.identity.clone(),
                ));
            }
            if section.lineage.is_empty() {
                return Err(CausalSectionError::EmptyLineage(section.identity.clone()));
            }
            if section.states.is_empty() {
                return Err(CausalSectionError::EmptyStateFamily(
                    section.identity.clone(),
                ));
            }
            if section.root >= section.states.len() {
                return Err(CausalSectionError::RootOutsideStateFamily(
                    section.identity.clone(),
                ));
            }
            if section
                .incidence
                .bonds()
                .iter()
                .any(|bond| bond.contact_faces.is_empty())
            {
                return Err(CausalSectionError::ContactFaceWasErased(
                    section.identity.clone(),
                ));
            }
            contacts = contacts
                .checked_add(
                    u64::try_from(section.incidence.bonds().len())
                        .map_err(|_| CausalSectionError::Extent)?,
                )
                .ok_or(CausalSectionError::Extent)?;
            offsets.push(locations.len());
            for (state_at, state) in section.states.iter().enumerate() {
                let state_receivers = state.observations.keys().cloned().collect::<BTreeSet<_>>();
                match &receiver_family {
                    Some(family) if family != &state_receivers => {
                        return Err(CausalSectionError::ReceiverFamilyDisagrees(
                            section.identity.clone(),
                        ));
                    }
                    None => receiver_family = Some(state_receivers),
                    _ => {}
                }
                for (input, successor) in &state.successors {
                    if *successor >= section.states.len() {
                        return Err(CausalSectionError::SuccessorOutsideStateFamily {
                            section: section.identity.clone(),
                            state: state_at,
                            successor: *successor,
                        });
                    }
                    inputs.insert(input.clone());
                }
                transitions = transitions
                    .checked_add(
                        u64::try_from(state.successors.len())
                            .map_err(|_| CausalSectionError::Extent)?,
                    )
                    .ok_or(CausalSectionError::Extent)?;
                observation_count = observation_count
                    .checked_add(
                        u64::try_from(state.observations.len())
                            .map_err(|_| CausalSectionError::Extent)?,
                    )
                    .ok_or(CausalSectionError::Extent)?;
                observations.extend(state.observations.values().cloned());
                locations.push((section_at, state_at));
            }
        }

        let receiver_names = receiver_family
            .ok_or(CausalSectionError::EmptyReceiverFamily)?
            .into_iter()
            .collect::<Vec<_>>();
        if receiver_names.is_empty() {
            return Err(CausalSectionError::EmptyReceiverFamily);
        }
        let receiver_index = receiver_names
            .iter()
            .cloned()
            .enumerate()
            .map(|(at, name)| {
                u64::try_from(at)
                    .map(ReceiverId)
                    .map(|id| (name, id))
                    .map_err(|_| CausalSectionError::Extent)
            })
            .collect::<Result<BTreeMap<_, _>, _>>()?;
        let input_names = inputs.into_iter().collect::<Vec<_>>();
        let observation_names = observations.into_iter().collect::<Vec<_>>();
        let observation_index = observation_names
            .iter()
            .cloned()
            .enumerate()
            .map(|(at, name)| {
                u64::try_from(at)
                    .map(Observation)
                    .map(|observation| (name, observation))
                    .map_err(|_| CausalSectionError::Extent)
            })
            .collect::<Result<BTreeMap<_, _>, _>>()?;
        let states = u64::try_from(locations.len()).map_err(|_| CausalSectionError::Extent)?;
        let pair_chart = if states < 2 {
            BigUint::from(0u8)
        } else {
            BigUint::from(states) * BigUint::from(states - 1) / BigUint::from(2u8)
        };
        let work = SectionWork {
            presentations: u64::try_from(sections.len()).map_err(|_| CausalSectionError::Extent)?,
            states,
            contacts,
            transitions,
            observations: observation_count,
            complete_state_pair_chart: pair_chart,
        };
        Ok(Self {
            sections,
            locations,
            offsets,
            receiver_names,
            receiver_index,
            input_names,
            observation_names,
            observation_index,
            work,
        })
    }

    pub fn sections(&self) -> &[CausalSection] {
        &self.sections
    }

    pub fn receiver_faces(&self) -> BTreeSet<String> {
        self.receiver_names.iter().cloned().collect()
    }

    /// Read the complete section population through the resident exact quotient. There is no
    /// production host default: a caller must supply the already-mounted card owner.
    pub fn read(
        &self,
        executor: &mut CudaRefineExecutor,
    ) -> Result<CausalSectionReading, CausalSectionError> {
        self.read_with_device(self.receiver_index.values().copied().collect(), executor)
    }

    /// Remove one receiver. The return may only coarsen if compression is lawful.
    pub fn read_without(
        &self,
        receiver: &str,
        executor: &mut CudaRefineExecutor,
    ) -> Result<CausalSectionReading, CausalSectionError> {
        let removed = self
            .receiver_index
            .get(receiver)
            .copied()
            .ok_or_else(|| CausalSectionError::UnknownReceiver(receiver.to_owned()))?;
        let active = self
            .receiver_index
            .values()
            .copied()
            .filter(|candidate| *candidate != removed)
            .collect::<Vec<_>>();
        if active.is_empty() {
            return Err(CausalSectionError::EmptyReceiverFamily);
        }
        self.read_with_device(active, executor)
    }

    fn read_with_device(
        &self,
        active_receivers: Vec<ReceiverId>,
        executor: &mut CudaRefineExecutor,
    ) -> Result<CausalSectionReading, CausalSectionError> {
        let system = SectionObservedSystem {
            ecology: self,
            active_receivers,
        };
        let compression = compress_on_device(&system, executor)
            .map_err(|refusal| CausalSectionError::DeviceRefused(refusal.to_string()))?;
        self.read_from_compression(system, compression)
    }

    /// Host construction retained only as the admission reference used by unit tests. Production
    /// source cannot call it, so omitting the card is not a runtime choice.
    #[cfg(test)]
    fn read_on_host_for_admission(&self) -> Result<CausalSectionReading, CausalSectionError> {
        self.read_with_host(self.receiver_index.values().copied().collect())
    }

    #[cfg(test)]
    fn read_without_on_host_for_admission(
        &self,
        receiver: &str,
    ) -> Result<CausalSectionReading, CausalSectionError> {
        let removed = self
            .receiver_index
            .get(receiver)
            .copied()
            .ok_or_else(|| CausalSectionError::UnknownReceiver(receiver.to_owned()))?;
        let active = self
            .receiver_index
            .values()
            .copied()
            .filter(|candidate| *candidate != removed)
            .collect::<Vec<_>>();
        if active.is_empty() {
            return Err(CausalSectionError::EmptyReceiverFamily);
        }
        self.read_with_host(active)
    }

    #[cfg(test)]
    fn read_with_host(
        &self,
        active_receivers: Vec<ReceiverId>,
    ) -> Result<CausalSectionReading, CausalSectionError> {
        let system = SectionObservedSystem {
            ecology: self,
            active_receivers,
        };
        let compression = compress(&system);
        self.read_from_compression(system, compression)
    }

    fn read_from_compression(
        &self,
        system: SectionObservedSystem<'_>,
        compression: ReceiverExactCompression,
    ) -> Result<CausalSectionReading, CausalSectionError> {
        let root_one_shot_blocks = self.root_blocks(&compression.one_shot.blocks);
        let root_conduct_blocks = self.root_blocks(&compression.conduct.blocks);
        let reconstruction_fibers = root_conduct_blocks
            .iter()
            .cloned()
            .map(|presentations| SectionReconstructionFiber {
                presentations,
                outside_declared_population_open: true,
            })
            .collect();
        let root_names = self
            .sections
            .iter()
            .enumerate()
            .map(|(at, section)| (self.root_item(at), section.identity.clone()))
            .collect::<BTreeMap<_, _>>();
        let shortest_separators = compression
            .collapsed
            .iter()
            .filter_map(|pair| {
                let left = root_names.get(&pair.left)?.clone();
                let right = root_names.get(&pair.right)?.clone();
                let (receiver, left_observation, right_observation) = pair
                    .witness
                    .map(|(receiver, left, right)| {
                        (
                            self.receiver_names.get(receiver.0 as usize).cloned(),
                            self.observation_names.get(left.0 as usize).cloned(),
                            self.observation_names.get(right.0 as usize).cloned(),
                        )
                    })
                    .unwrap_or((None, None, None));
                Some(SectionSeparator {
                    left,
                    right,
                    interventions: pair
                        .distinguishing_word
                        .iter()
                        .filter_map(|input| self.input_names.get(input.0 as usize).cloned())
                        .collect(),
                    receiver,
                    left_observation,
                    right_observation,
                    separated_by_terminus: pair.separated_by_terminus,
                })
            })
            .collect();
        let presentations = self
            .sections
            .iter()
            .map(|section| SectionPresentationReading {
                identity: section.identity.clone(),
                lineage: section.lineage.clone(),
                states: section.states.len(),
                sites: section.incidence.sites().len(),
                bonds: section.incidence.bonds().len(),
                compounds: section.incidence.compounds().len(),
                contact_faces: section
                    .incidence
                    .bonds()
                    .iter()
                    .flat_map(|bond| bond.contact_faces.iter().map(|face| face.name().to_owned()))
                    .collect(),
            })
            .collect();
        let receivers = system
            .active_receivers
            .iter()
            .filter_map(|receiver| self.receiver_names.get(receiver.0 as usize).cloned())
            .collect();
        Ok(CausalSectionReading {
            schema: "life.causal-section-reading.v1".to_owned(),
            receivers,
            presentations,
            root_one_shot_blocks,
            root_conduct_blocks,
            reconstruction_fibers,
            shortest_separators,
            compression,
            work: self.work.clone(),
        })
    }

    fn root_item(&self, section: usize) -> ItemId {
        ItemId(
            u64::try_from(self.offsets[section] + self.sections[section].root)
                .expect("found() established that every state address fits ItemId"),
        )
    }

    fn root_blocks(&self, blocks: &[BTreeSet<ItemId>]) -> Vec<BTreeSet<String>> {
        let roots = self
            .sections
            .iter()
            .enumerate()
            .map(|(at, section)| (self.root_item(at), section.identity.as_str()))
            .collect::<BTreeMap<_, _>>();
        blocks
            .iter()
            .filter_map(|block| {
                let held = block
                    .iter()
                    .filter_map(|item| roots.get(item).map(|identity| (*identity).to_owned()))
                    .collect::<BTreeSet<_>>();
                (!held.is_empty()).then_some(held)
            })
            .collect()
    }
}

struct SectionObservedSystem<'a> {
    ecology: &'a CausalSectionEcology,
    active_receivers: Vec<ReceiverId>,
}

impl ObservedSystem for SectionObservedSystem<'_> {
    fn items(&self) -> Vec<ItemId> {
        (0..self.ecology.work.states).map(ItemId).collect()
    }

    fn receivers(&self) -> Vec<ReceiverId> {
        self.active_receivers.clone()
    }

    fn inputs(&self) -> Vec<InputId> {
        (0..u64::try_from(self.ecology.input_names.len())
            .expect("found() established that the input family fits InputId"))
            .map(InputId)
            .collect()
    }

    fn observation(&self, item: ItemId, receiver: ReceiverId) -> Observation {
        let item = usize::try_from(item.0).expect("the ecology issued this item");
        let receiver = usize::try_from(receiver.0).expect("the ecology issued this receiver");
        let (section, state) = self.ecology.locations[item];
        let receiver = &self.ecology.receiver_names[receiver];
        let face = &self.ecology.sections[section].states[state].observations[receiver];
        self.ecology.observation_index[face]
    }

    fn successor(&self, item: ItemId, input: InputId) -> Option<ItemId> {
        let item = usize::try_from(item.0).ok()?;
        let input = usize::try_from(input.0).ok()?;
        let (section, state) = *self.ecology.locations.get(item)?;
        let input = self.ecology.input_names.get(input)?;
        let successor = self.ecology.sections[section].states[state]
            .successors
            .get(input)?;
        Some(ItemId(
            u64::try_from(self.ecology.offsets[section] + successor)
                .expect("found() established that every successor fits ItemId"),
        ))
    }
}

#[cfg(test)]
mod tests;
