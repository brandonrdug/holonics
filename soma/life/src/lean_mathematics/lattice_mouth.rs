//! The Lean material mouth.
//!
//! Declaration organs found carriers, in-corpus references found occurrences, and each referring
//! declaration's proof founds the generator that transports its premises into it.  The grain is
//! the recurring transformation the material itself exposes: one proof applied to its premises.
//! Whitespace, bytes, and identifier surfaces found nothing here.
//!
//! Jurisdiction: the Lean reader is observer apparatus.  The hot scaffold this mouth returns
//! carries only native state, occurrence, generator, and receiver addresses with exact currents.
//! Every declaration name, source path, and relation label departs into the physically separate
//! [`LeanLatticeColdWitness`], which hot conduct cannot read.

use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

use holonic_engine::{
    native_spool::{
        NativeCollapsedFibre, NativeConstitutiveResponse, NativeGeneratorDescent,
        NativeGeneratorStep, NativeIncidenceTerm, NativeOccurrenceSection, NativeParametronCell,
        NativeReceiverConsequence, NativeSpool, NativeSpoolRefusal, NativeThread,
        NativeThreadHand, NativeThreadOccurrence, NativeTransportScaffold, NATIVE_SPOOL_SCHEMA,
        NATIVE_THREAD_SCHEMA, NATIVE_TRANSPORT_SCAFFOLD_SCHEMA,
    },
    receiver_exact_compression::{InputId, Observation, ReceiverId},
    receiver_history_compression::{NativeStateId, ReceiverFactor},
    BoundaryId, EventId, ExactComplexWaveCurrent, ExactUnitConicPhase, OccurrencePort,
};
use num_bigint::BigInt;
use num_rational::BigRational as Rat;
use serde::{Deserialize, Serialize};

use super::{LeanDeclarationOrgan, LeanMathematicsEcology};

pub const LEAN_LATTICE_WITNESS_SCHEMA: &str = "life.lean-lattice-cold-witness.v1";
pub const LEAN_LATTICE_SPOOL_ADDRESS: &str = "lean/declaration-lattice";
pub const LEAN_LATTICE_SCAFFOLD_ADDRESS: &str = "lean/declaration-scaffold";

/// The one declared face every carrier presents and receives: a declaration's conclusion is the
/// premise face of whatever later proof carries it.
const DECLARATION_FACE: BoundaryId = BoundaryId(0);

/// One in-corpus reference: the referenced declaration's face crossed into the referring proof.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LeanReferenceWitness {
    pub referenced: String,
    pub referring: String,
}

/// The exterior correspondence between native addresses and Lean declarations.  It departs
/// from the hot scaffold and is consulted only by the cold render and the world return.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct LeanLatticeColdWitness {
    pub schema: String,
    pub receiver: u64,
    pub declaration_by_state: BTreeMap<u64, String>,
    pub reference_by_occurrence: BTreeMap<u64, LeanReferenceWitness>,
    pub declaration_by_generator: BTreeMap<u64, String>,
    pub relation_by_observation: BTreeMap<u64, String>,
    pub unresolved_references: BTreeSet<String>,
}

impl LeanLatticeColdWitness {
    pub fn state_of(&self, declaration: &str) -> Option<NativeStateId> {
        self.declaration_by_state
            .iter()
            .find_map(|(state, name)| (name == declaration).then_some(NativeStateId(*state)))
    }

    pub fn declaration_of(&self, state: NativeStateId) -> Option<&str> {
        self.declaration_by_state.get(&state.0).map(String::as_str)
    }

    pub fn generator_of(&self, declaration: &str) -> Option<InputId> {
        self.declaration_by_generator
            .iter()
            .find_map(|(generator, name)| (name == declaration).then_some(InputId(*generator)))
    }

    pub fn declaration_of_generator(&self, generator: InputId) -> Option<&str> {
        self.declaration_by_generator
            .get(&generator.0)
            .map(String::as_str)
    }

    pub fn reference_of(&self, occurrence: EventId) -> Option<&LeanReferenceWitness> {
        self.reference_by_occurrence.get(&occurrence.0)
    }

    /// The occurrence carrying one reference, if the corpus admitted it.
    pub fn occurrence_of(&self, referenced: &str, referring: &str) -> Option<EventId> {
        self.reference_by_occurrence
            .iter()
            .find_map(|(occurrence, reference)| {
                (reference.referenced == referenced && reference.referring == referring)
                    .then_some(EventId(*occurrence))
            })
    }
}

/// The two lanes the mouth returns.  They are separate values so the witness can depart.
#[derive(Debug)]
pub struct LeanLatticeReturn {
    pub native: NativeTransportScaffold,
    pub witness: LeanLatticeColdWitness,
}

#[derive(Debug)]
pub enum LeanLatticeRefusal {
    NoDeclarations,
    NoReferences,
    Native(NativeSpoolRefusal),
}

impl fmt::Display for LeanLatticeRefusal {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoDeclarations => write!(formatter, "the conditioned corpus exposes no declaration"),
            Self::NoReferences => {
                write!(formatter, "no declaration references another inside the corpus")
            }
            Self::Native(refusal) => write!(formatter, "native scaffold refused: {refusal}"),
        }
    }
}

impl std::error::Error for LeanLatticeRefusal {}

impl From<NativeSpoolRefusal> for LeanLatticeRefusal {
    fn from(refusal: NativeSpoolRefusal) -> Self {
        Self::Native(refusal)
    }
}

/// The address of the thread carrying one referring declaration's generator.
pub fn generator_thread_address(generator: InputId) -> String {
    format!("thread/lean-generator-{}", generator.0)
}

fn resolve(index: &BTreeMap<&str, usize>, referenced: &str) -> Option<usize> {
    if let Some(at) = index.get(referenced) {
        return Some(*at);
    }
    let suffix = format!(".{referenced}");
    let mut found = index.iter().filter(|(name, _)| name.ends_with(&suffix));
    let candidate = found.next().map(|(_, at)| *at)?;
    found.next().is_none().then_some(candidate)
}

fn exact(count: u64) -> Rat {
    Rat::from_integer(BigInt::from(count))
}

/// Found one source-neutral carrier population from a conditioned Lean corpus.
pub fn found_lean_lattice(
    ecology: &LeanMathematicsEcology,
    receiver: ReceiverId,
) -> Result<LeanLatticeReturn, LeanLatticeRefusal> {
    let mut organs: Vec<&LeanDeclarationOrgan> = ecology.declarations().collect();
    organs.sort_by(|left, right| left.name.cmp(&right.name));
    organs.dedup_by(|left, right| left.name == right.name);
    if organs.is_empty() {
        return Err(LeanLatticeRefusal::NoDeclarations);
    }
    let index = organs
        .iter()
        .enumerate()
        .map(|(at, organ)| (organ.name.as_str(), at))
        .collect::<BTreeMap<_, _>>();

    let mut references = Vec::new();
    let mut unresolved = BTreeSet::new();
    for (to, organ) in organs.iter().enumerate() {
        for referenced in &organ.referenced_declarations {
            match resolve(&index, referenced) {
                Some(from) if from != to => references.push((from, to)),
                Some(_) => {}
                None => {
                    unresolved.insert(referenced.clone());
                }
            }
        }
    }
    references.sort_unstable();
    references.dedup();
    if references.is_empty() {
        return Err(LeanLatticeRefusal::NoReferences);
    }

    let participating = references
        .iter()
        .flat_map(|(from, to)| [*from, *to])
        .collect::<BTreeSet<_>>();
    let state_of = participating
        .iter()
        .enumerate()
        .map(|(at, organ)| (*organ, NativeStateId(at as u64)))
        .collect::<BTreeMap<_, _>>();
    let mut labels = participating
        .iter()
        .map(|organ| organs[*organ].relation_label())
        .collect::<Vec<_>>();
    labels.sort_unstable();
    labels.dedup();
    let observation_of = |organ: usize| {
        let label = organs[organ].relation_label();
        Observation(labels.binary_search(&label).expect("every label is indexed") as u64)
    };
    let mut departures = BTreeMap::<usize, u64>::new();
    let mut arrivals = BTreeMap::<usize, u64>::new();
    for (from, to) in &references {
        *departures.entry(*from).or_default() += 1;
        *arrivals.entry(*to).or_default() += 1;
    }
    let current_of = |organ: usize| {
        ExactComplexWaveCurrent::new(
            exact(departures.get(&organ).copied().unwrap_or(0)),
            exact(arrivals.get(&organ).copied().unwrap_or(0)),
        )
    };
    let referring = references.iter().map(|(_, to)| *to).collect::<BTreeSet<_>>();
    let generator_of = referring
        .iter()
        .enumerate()
        .map(|(at, organ)| (*organ, InputId(at as u64)))
        .collect::<BTreeMap<_, _>>();
    let mut first_into = BTreeMap::<usize, usize>::new();
    for (at, (_, to)) in references.iter().enumerate() {
        first_into.entry(*to).or_insert(at);
    }

    let mut threads = Vec::with_capacity(referring.len());
    let mut generator_descents = Vec::with_capacity(referring.len());
    for (to, generator) in &generator_of {
        let address = generator_thread_address(*generator);
        let members = references
            .iter()
            .enumerate()
            .filter(|(_, (_, target))| target == to)
            .map(|(at, (from, _))| (at, *from))
            .collect::<Vec<_>>();
        let occurrences = members
            .iter()
            .map(|(at, from)| NativeThreadOccurrence {
                occurrence: EventId(*at as u64),
                predecessor: first_into.get(from).map(|prior| EventId(*prior as u64)),
                entering_port: OccurrencePort::input(EventId(*at as u64), 0),
                emitting_port: OccurrencePort::output(EventId(*at as u64), 0),
                entering_native: state_of[from],
                emitting_native: state_of[to],
            })
            .collect::<Vec<_>>();
        let native_support = occurrences
            .iter()
            .flat_map(|occurrence| [occurrence.entering_native, occurrence.emitting_native])
            .collect::<BTreeSet<_>>();
        let organ_of_state = participating
            .iter()
            .map(|organ| (state_of[organ], *organ))
            .collect::<BTreeMap<_, _>>();
        let parametrons = native_support
            .iter()
            .map(|native| {
                let current = current_of(organ_of_state[native]);
                NativeParametronCell {
                    native: *native,
                    section: current.clone(),
                    current,
                    relative_phase: ExactUnitConicPhase::identity(),
                    hand: NativeThreadHand::Along,
                }
            })
            .collect::<Vec<_>>();
        let constitutive_responses = parametrons
            .iter()
            .map(|cell| NativeConstitutiveResponse {
                native: cell.native,
                receiver,
                presented: cell.section.clone(),
                stored: cell.current.clone(),
            })
            .collect();
        let receiver_consequences = native_support
            .iter()
            .map(|native| NativeReceiverConsequence {
                native: *native,
                receiver,
                observation: observation_of(organ_of_state[native]),
            })
            .collect();
        generator_descents.push(NativeGeneratorDescent {
            generator: *generator,
            steps: members
                .iter()
                .map(|(_, from)| NativeGeneratorStep {
                    from: state_of[from],
                    to: state_of[to],
                    thread: address.clone(),
                })
                .collect(),
            open_domain: state_of
                .iter()
                .filter(|(organ, _)| !members.iter().any(|(_, from)| from == *organ))
                .map(|(_, state)| *state)
                .collect(),
        });
        threads.push(NativeThread {
            schema: NATIVE_THREAD_SCHEMA.to_owned(),
            address,
            entering_boundary: DECLARATION_FACE,
            emitting_boundary: DECLARATION_FACE,
            entering_carrier: "exact-declaration-incidence-current".to_owned(),
            emitting_carrier: "exact-declaration-incidence-current".to_owned(),
            incidence: occurrences
                .iter()
                .map(|occurrence| NativeIncidenceTerm {
                    occurrence: occurrence.occurrence,
                    from: occurrence.entering_native,
                    to: occurrence.emitting_native,
                    coefficient: 1,
                })
                .collect(),
            sections: members
                .iter()
                .map(|(at, from)| {
                    NativeOccurrenceSection::from_currents(
                        EventId(*at as u64),
                        current_of(*from),
                        current_of(*to),
                    )
                })
                .collect(),
            reconstruction_fibre: occurrences.iter().map(|item| item.occurrence).collect(),
            occurrences,
            native_support,
            parametrons,
            constitutive_responses,
            chronology: vec![*generator],
            receiver_consequences,
            obstruction: None,
            open_exterior: vec![
                "premises outside the conditioned corpus and later proofs remain open".to_owned(),
            ],
        });
    }

    let native_population = state_of.values().copied().collect::<BTreeSet<_>>();
    let receiver_factors = participating
        .iter()
        .map(|organ| ReceiverFactor {
            native: state_of[organ],
            receiver,
            observation: observation_of(*organ),
        })
        .collect();
    let reconstruction_fibres = referring
        .iter()
        .map(|to| NativeCollapsedFibre {
            native: state_of[to],
            occurrences: references
                .iter()
                .enumerate()
                .filter(|(_, (_, target))| target == to)
                .map(|(at, _)| EventId(at as u64))
                .collect(),
        })
        .collect();
    let spool = NativeSpool {
        schema: NATIVE_SPOOL_SCHEMA.to_owned(),
        address: LEAN_LATTICE_SPOOL_ADDRESS.to_owned(),
        native_population,
        receiver_family: BTreeSet::from([receiver]),
        generator_family: generator_of.values().copied().collect(),
        threads,
        serial_pullbacks: Vec::new(),
        generator_descents,
        receiver_factors,
        mutual_constitutive_responses: Vec::new(),
        reconstruction_fibres,
        shortest_separators: Vec::new(),
        interchanges: Vec::new(),
        open_exterior: vec![
            "serial pullbacks between proofs and mutual responses are founded by later returns"
                .to_owned(),
        ],
    };
    spool.validate()?;
    let native = NativeTransportScaffold {
        schema: NATIVE_TRANSPORT_SCAFFOLD_SCHEMA.to_owned(),
        address: LEAN_LATTICE_SCAFFOLD_ADDRESS.to_owned(),
        spools: vec![spool],
        compositions: Vec::new(),
        open_exterior: vec!["additional compatible native organs".to_owned()],
    };
    native.validate()?;

    let witness = LeanLatticeColdWitness {
        schema: LEAN_LATTICE_WITNESS_SCHEMA.to_owned(),
        receiver: receiver.0,
        declaration_by_state: state_of
            .iter()
            .map(|(organ, state)| (state.0, organs[*organ].name.clone()))
            .collect(),
        reference_by_occurrence: references
            .iter()
            .enumerate()
            .map(|(at, (from, to))| {
                (
                    at as u64,
                    LeanReferenceWitness {
                        referenced: organs[*from].name.clone(),
                        referring: organs[*to].name.clone(),
                    },
                )
            })
            .collect(),
        declaration_by_generator: generator_of
            .iter()
            .map(|(organ, generator)| (generator.0, organs[*organ].name.clone()))
            .collect(),
        relation_by_observation: labels
            .iter()
            .enumerate()
            .map(|(at, label)| (at as u64, (*label).to_owned()))
            .collect(),
        unresolved_references: unresolved,
    };
    Ok(LeanLatticeReturn { native, witness })
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::lean_mathematics::LeanSourceDocument;

    const CORPUS: &str = "theorem alpha (n : Nat) : n + 0 = n := by\n  simp\n\n\
theorem beta (n : Nat) : 0 + n = n := by\n  rw [Nat.zero_add]\n\n\
theorem gamma (n : Nat) : n + 0 = 0 + n := by\n  rw [alpha, beta]\n\n\
theorem delta (n : Nat) : 0 + n = n + 0 := by\n  rw [gamma]\n";

    fn contains(haystack: &[u8], needle: &[u8]) -> bool {
        haystack.windows(needle.len()).any(|window| window == needle)
    }

    #[test]
    fn declarations_found_a_valid_lattice_and_the_hot_wire_carries_no_names() {
        let documents = vec![LeanSourceDocument::new("Test/Lattice.lean", CORPUS)];
        let ecology = LeanMathematicsEcology::condition(&documents).expect("conditions");
        let returned = found_lean_lattice(&ecology, ReceiverId(7)).expect("lattice");
        returned.native.validate().expect("valid scaffold");
        let wire = returned.native.canonical_bytes().expect("wire");
        for surface in ["alpha", "beta", "gamma", "delta", "Lattice.lean", "simp", "rw", "="] {
            assert!(
                !contains(&wire, surface.as_bytes()),
                "the hot wire must not carry {surface}"
            );
        }
        let witness = &returned.witness;
        assert_eq!(witness.declaration_by_state.len(), 4);
        let alpha_gamma = witness.occurrence_of("alpha", "gamma").expect("alpha crosses gamma");
        let gamma_delta = witness.occurrence_of("gamma", "delta").expect("gamma crosses delta");
        let gamma = witness.generator_of("gamma").expect("gamma founds a generator");
        let thread = returned.native.spools[0]
            .threads
            .iter()
            .find(|thread| thread.address == generator_thread_address(gamma))
            .expect("gamma's thread");
        assert_eq!(thread.occurrences.len(), 2, "gamma carries two premises");
        let later = returned.native.spools[0]
            .threads
            .iter()
            .flat_map(|thread| &thread.occurrences)
            .find(|occurrence| occurrence.occurrence == gamma_delta)
            .expect("delta's occurrence");
        assert_eq!(later.predecessor, Some(alpha_gamma), "chronology follows incidence");
    }
}
