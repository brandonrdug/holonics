//! Record: research/records/2026-08-12_THE_RECURRENT_LAW_CROSSES_THE_CORPUS_DEPARTURE_THE_UNSEEN_SECTION_RIDES_ITS_DEPOSIT.md
//! Source-detached recurrent transformation morphology for causal sections.
//!
//! The rest carries no section identity, source occurrence, sample coordinate, or sample answer.
//! Each anonymous exact material-conduct key addresses one card-founded bi-affine law. After the
//! founding world departs, a later presentation supplies its own conduct witness and previously
//! unseen coordinates. The resident conduct join attaches the witness to the deposited law and a
//! second resident entry evaluates that law. The returned consequence graph is then classified by
//! `causal_section`; no operation label or material kind enters the quotient.

use std::collections::{BTreeMap, BTreeSet};

use holonic_structure::LocalSequence;
use serde::Serialize;

use crate::{
    causal_section::{CausalSection, SectionState},
    incidence_production::{DeclaredContactFace, DeclaredOccurrence, IncidenceComplex},
    morphological_language::{
        CudaMorphologicalConductExecutor, MorphologicalConductCandidate,
        MorphologicalConductCandidateKey, MorphologicalConductCudaFront,
        MorphologicalConductCudaReceipt, MorphologicalConductDepositRow,
    },
    recurrent_section_cuda::{
        BiaffineEvaluation, BiaffineLaw, BiaffineQuery, BiaffineSampleGrid,
        CudaRecurrentLawExecutor, RecurrentLawCudaReceipt,
    },
};

const REST_MAGIC: &[u8; 8] = b"RLAW\0\0\0\x01";

/// Anonymous exact testimony that one presentation crossed recurring material conduct.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct SectionMorphologyWitness {
    key_words: usize,
    keys: Vec<Vec<u32>>,
    distinct_sources: u64,
}

impl SectionMorphologyWitness {
    pub fn new(
        key_words: usize,
        keys: Vec<Vec<u32>>,
        distinct_sources: u64,
    ) -> Result<Self, String> {
        if key_words == 0 || keys.is_empty() {
            return Err("a recurrent section has no deposited conduct witness".to_owned());
        }
        if distinct_sources < 2 {
            return Err("a recurrent section did not cross two distinct source wholes".to_owned());
        }
        if keys.iter().any(|key| key.len() != key_words) {
            return Err("a recurrent-section conduct witness changes key width".to_owned());
        }
        if keys.windows(2).any(|pair| pair[0] >= pair[1]) {
            return Err(
                "a recurrent-section conduct witness is repeated or noncanonical".to_owned(),
            );
        }
        Ok(Self {
            key_words,
            keys,
            distinct_sources,
        })
    }

    pub const fn key_words(&self) -> usize {
        self.key_words
    }

    pub fn keys(&self) -> &[Vec<u32>] {
        &self.keys
    }

    pub const fn distinct_sources(&self) -> u64 {
        self.distinct_sources
    }
}

/// One complete founding return. Identity and codec lineage deliberately do not enter this port.
#[derive(Clone, Debug)]
pub struct ReturnedTransformationLaw {
    pub witness: SectionMorphologyWitness,
    pub samples: BiaffineSampleGrid,
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct RecurrentLawDeposit {
    conduct_key: Vec<u32>,
    law: BiaffineLaw,
}

/// The smallest continuing object crossing suspension/remount.
#[derive(Debug, PartialEq, Eq)]
pub struct RecurrentSectionMorphology {
    conduct_key_words: usize,
    deposits: Vec<RecurrentLawDeposit>,
}

#[derive(Clone, Debug)]
pub struct PresentedSectionState {
    pub coordinate: [i64; 2],
    pub successors: BTreeMap<String, usize>,
}

/// A genuinely later exterior presentation. These chart fields never enter native rest.
#[derive(Clone, Debug)]
pub struct SectionPresentation {
    pub identity: String,
    pub lineage: String,
    pub incidence_text: String,
    pub contact_faces: Vec<String>,
    pub witness: SectionMorphologyWitness,
    pub states: Vec<PresentedSectionState>,
    pub root: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SectionStateFormation {
    pub state: usize,
    pub coordinate: [i64; 2],
    pub candidate_values: Vec<String>,
    pub path_population: usize,
    pub open: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SectionFormationReading {
    pub identity: String,
    pub active: bool,
    pub states: Vec<SectionStateFormation>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RecurrentSectionFormationReceipt {
    pub schema: String,
    pub presented_sections: usize,
    pub deposited_conducts: usize,
    pub active_conducts: usize,
    pub distinct_transformation_laws: usize,
    pub riding_state_laws: usize,
    pub causal_front_distribution: BTreeMap<usize, usize>,
    pub interaction_arity_distribution: BTreeMap<usize, usize>,
    pub phase_current_distribution: BTreeMap<usize, usize>,
    pub mixed_phase_distribution: BTreeMap<i64, usize>,
    pub reconvergent_diamonds: usize,
    pub flat_reconvergent_diamonds: usize,
    pub readings: Vec<SectionFormationReading>,
    pub attachment_apparatus: MorphologicalConductCudaReceipt,
    pub evaluation_apparatus: Option<RecurrentLawCudaReceipt>,
}

#[derive(Debug)]
pub struct RecurrentSectionFormation {
    pub sections: Vec<CausalSection>,
    pub receipt: RecurrentSectionFormationReceipt,
}

impl RecurrentSectionMorphology {
    /// Found exact laws on the card, bind them to anonymous recurring conduct, and forget every
    /// sample before returning the owner.
    pub fn found(
        returned: Vec<ReturnedTransformationLaw>,
        executor: &mut CudaRecurrentLawExecutor,
    ) -> Result<(Self, RecurrentLawCudaReceipt), String> {
        if returned.is_empty() {
            return Err("no returned transformation law was supplied".to_owned());
        }
        let raw_key_words = returned[0].witness.key_words;
        if returned
            .iter()
            .any(|law| law.witness.key_words != raw_key_words)
        {
            return Err("returned conduct witnesses do not share one exact key width".to_owned());
        }
        let maximum_keys = returned
            .iter()
            .map(|law| law.witness.keys.len())
            .max()
            .unwrap();
        let conduct_key_words = composite_key_words(raw_key_words, maximum_keys)?;
        let grids = returned.iter().map(|law| law.samples).collect::<Vec<_>>();
        let (laws, apparatus) = executor.found(&grids)?;
        let mut deposits = returned
            .into_iter()
            .zip(laws)
            .map(|(returned, law)| {
                Ok(RecurrentLawDeposit {
                    conduct_key: composite_key(&returned.witness, maximum_keys)?,
                    law,
                })
            })
            .collect::<Result<Vec<_>, String>>()?;
        deposits.sort_by(|left, right| left.conduct_key.cmp(&right.conduct_key));
        if deposits
            .windows(2)
            .any(|pair| pair[0].conduct_key == pair[1].conduct_key)
        {
            return Err(
                "two founding returns carry one indistinguishable conduct witness".to_owned(),
            );
        }
        let morphology = Self {
            conduct_key_words,
            deposits,
        };
        morphology.validate()?;
        Ok((morphology, apparatus))
    }

    pub fn deposited_conducts(&self) -> usize {
        self.deposits.len()
    }

    pub fn distinct_transformation_laws(&self) -> usize {
        self.deposits
            .iter()
            .map(|deposit| deposit.law)
            .collect::<BTreeSet<_>>()
            .len()
    }

    pub fn form_sections(
        &self,
        presentations: &[SectionPresentation],
        conduct: &mut CudaMorphologicalConductExecutor,
        laws: &mut CudaRecurrentLawExecutor,
    ) -> Result<RecurrentSectionFormation, String> {
        self.form(presentations, &BTreeSet::new(), false, conduct, laws)
    }

    pub fn form_unconditioned_sections(
        &self,
        presentations: &[SectionPresentation],
        conduct: &mut CudaMorphologicalConductExecutor,
        laws: &mut CudaRecurrentLawExecutor,
    ) -> Result<RecurrentSectionFormation, String> {
        self.form(presentations, &BTreeSet::new(), true, conduct, laws)
    }

    pub fn form_without_witness(
        &self,
        presentations: &[SectionPresentation],
        target: &SectionMorphologyWitness,
        conduct: &mut CudaMorphologicalConductExecutor,
        laws: &mut CudaRecurrentLawExecutor,
    ) -> Result<RecurrentSectionFormation, String> {
        let target_key = self.candidate_key(target)?;
        let ablated = BTreeSet::from([target_key]);
        if !self
            .deposits
            .iter()
            .any(|deposit| ablated.contains(&deposit.conduct_key))
        {
            return Err("the target witness names no deposited conduct".to_owned());
        }
        self.form(presentations, &ablated, false, conduct, laws)
    }

    fn form(
        &self,
        presentations: &[SectionPresentation],
        ablated: &BTreeSet<Vec<u32>>,
        unconditioned: bool,
        conduct: &mut CudaMorphologicalConductExecutor,
        laws: &mut CudaRecurrentLawExecutor,
    ) -> Result<RecurrentSectionFormation, String> {
        self.validate()?;
        validate_presentations(presentations)?;
        let candidate_keys = presentations
            .iter()
            .map(|presentation| self.candidate_key(&presentation.witness))
            .collect::<Result<Vec<_>, _>>()?;
        let candidates = (0..presentations.len())
            .map(|at| {
                MorphologicalConductCandidate::new(
                    u32::try_from(at)
                        .map_err(|_| "the presentation population exceeds u32".to_owned())?,
                )
                .ok_or_else(|| "a presentation used the reserved open face".to_owned())
            })
            .collect::<Result<LocalSequence<_>, _>>()?;
        let deposits = self
            .deposits
            .iter()
            .map(|deposit| {
                MorphologicalConductDepositRow::new(
                    !unconditioned && !ablated.contains(&deposit.conduct_key),
                    deposit.conduct_key.iter().copied().collect(),
                )
            })
            .collect::<LocalSequence<_>>();
        let key_rows = candidate_keys
            .iter()
            .enumerate()
            .map(|(at, key)| {
                Ok(MorphologicalConductCandidateKey::new(
                    u32::try_from(at)
                        .map_err(|_| "the presentation key population exceeds u32".to_owned())?,
                    key.iter().copied().collect(),
                ))
            })
            .collect::<Result<LocalSequence<_>, String>>()?;
        let front = if unconditioned
            || self
                .deposits
                .iter()
                .all(|deposit| ablated.contains(&deposit.conduct_key))
        {
            MorphologicalConductCudaFront::explicit_zero_active_ablation(
                self.conduct_key_words,
                candidates,
                deposits,
                key_rows,
            )
        } else {
            MorphologicalConductCudaFront::new(
                self.conduct_key_words,
                candidates,
                deposits,
                key_rows,
            )
        }
        .map_err(|error| format!("found recurrent-section attachment front: {error}"))?;
        let attached = conduct
            .enact(&front)
            .map_err(|error| format!("attach remounted transformation conduct: {error}"))?;

        let mut queries = Vec::new();
        let mut query_destinations = Vec::new();
        let mut presentation_laws = Vec::with_capacity(presentations.len());
        for (presentation_at, candidate) in attached.semantic.candidates.iter().enumerate() {
            if candidate.candidate as usize != presentation_at {
                return Err("the card reordered later presentations".to_owned());
            }
            let mut carried = Vec::new();
            for deposit_at in &candidate.active_deposits {
                let deposit = self
                    .deposits
                    .get(*deposit_at as usize)
                    .ok_or_else(|| "the card attached outside recurrent law rest".to_owned())?;
                carried.push(deposit.law);
                for (state_at, state) in presentations[presentation_at].states.iter().enumerate() {
                    query_destinations.push((presentation_at, state_at));
                    queries.push(BiaffineQuery {
                        law: deposit.law,
                        point: state.coordinate,
                    });
                }
            }
            presentation_laws.push(carried);
        }
        let (evaluations, evaluation_apparatus) = if queries.is_empty() {
            (Vec::new(), None)
        } else {
            let (evaluations, receipt) = laws.evaluate(&queries)?;
            (evaluations, Some(receipt))
        };
        if evaluations.len() != query_destinations.len() {
            return Err(
                "the card returned a different transformation-law query population".to_owned(),
            );
        }
        let mut state_values = presentations
            .iter()
            .map(|presentation| vec![BTreeSet::<i64>::new(); presentation.states.len()])
            .collect::<Vec<_>>();
        let mut state_obstructions = presentations
            .iter()
            .map(|presentation| vec![false; presentation.states.len()])
            .collect::<Vec<_>>();
        for ((presentation, state), evaluation) in query_destinations.into_iter().zip(evaluations) {
            match evaluation {
                BiaffineEvaluation::Value(value) => {
                    state_values[presentation][state].insert(value);
                }
                BiaffineEvaluation::OutsideLattice | BiaffineEvaluation::FiniteCarrierOverflow => {
                    state_obstructions[presentation][state] = true;
                }
            }
        }

        let mut causal_front_distribution = BTreeMap::new();
        let mut interaction_arity_distribution = BTreeMap::new();
        let mut phase_current_distribution = BTreeMap::new();
        let mut mixed_phase_distribution = BTreeMap::new();
        let mut reconvergent_diamonds = 0usize;
        let mut sections = Vec::with_capacity(presentations.len());
        let mut readings = Vec::with_capacity(presentations.len());
        for (presentation_at, presentation) in presentations.iter().enumerate() {
            for law in &presentation_laws[presentation_at] {
                *mixed_phase_distribution
                    .entry(law.coefficients[3])
                    .or_insert(0) += 1;
            }
            for depth in causal_depths(&presentation.states, presentation.root)? {
                *causal_front_distribution.entry(depth).or_insert(0) += 1;
            }
            for state in &presentation.states {
                *interaction_arity_distribution
                    .entry(state.successors.len())
                    .or_insert(0) += 1;
            }
            reconvergent_diamonds = reconvergent_diamonds
                .checked_add(count_reconvergent_diamonds(
                    &presentation.states,
                    presentation.root,
                )?)
                .ok_or_else(|| "the recurrent-section diamond population overflowed".to_owned())?;
            let mut states = Vec::with_capacity(presentation.states.len());
            let mut state_readings = Vec::with_capacity(presentation.states.len());
            for (state_at, state) in presentation.states.iter().enumerate() {
                let values = &state_values[presentation_at][state_at];
                let path_population = values.len();
                let open = values.is_empty();
                *phase_current_distribution
                    .entry(path_population)
                    .or_insert(0) += 1;
                let value_face = if open {
                    if state_obstructions[presentation_at][state_at] {
                        "OBSTRUCTED".to_owned()
                    } else {
                        "OPEN".to_owned()
                    }
                } else {
                    values
                        .iter()
                        .map(i64::to_string)
                        .collect::<Vec<_>>()
                        .join("|")
                };
                states.push(SectionState {
                    observations: BTreeMap::from([
                        (
                            "defined".to_owned(),
                            if open { "no" } else { "yes" }.to_owned(),
                        ),
                        ("value".to_owned(), value_face),
                    ]),
                    successors: state.successors.clone(),
                });
                state_readings.push(SectionStateFormation {
                    state: state_at,
                    coordinate: state.coordinate,
                    candidate_values: values.iter().map(i64::to_string).collect(),
                    path_population,
                    open,
                });
            }
            sections.push(CausalSection {
                identity: presentation.identity.clone(),
                lineage: presentation.lineage.clone(),
                incidence: found_incidence(presentation)?,
                states,
                root: presentation.root,
            });
            readings.push(SectionFormationReading {
                identity: presentation.identity.clone(),
                active: !presentation_laws[presentation_at].is_empty(),
                states: state_readings,
            });
        }
        Ok(RecurrentSectionFormation {
            sections,
            receipt: RecurrentSectionFormationReceipt {
                schema: "soma-life.recurrent-section-formation.v2".to_owned(),
                presented_sections: presentations.len(),
                deposited_conducts: self.deposits.len(),
                active_conducts: self
                    .deposits
                    .iter()
                    .filter(|deposit| !unconditioned && !ablated.contains(&deposit.conduct_key))
                    .count(),
                distinct_transformation_laws: self.distinct_transformation_laws(),
                riding_state_laws: queries.len(),
                causal_front_distribution,
                interaction_arity_distribution,
                phase_current_distribution,
                mixed_phase_distribution,
                reconvergent_diamonds,
                flat_reconvergent_diamonds: reconvergent_diamonds,
                readings,
                attachment_apparatus: attached.apparatus,
                evaluation_apparatus,
            },
        })
    }

    fn candidate_key(&self, witness: &SectionMorphologyWitness) -> Result<Vec<u32>, String> {
        let residual = self
            .conduct_key_words
            .checked_sub(2)
            .ok_or_else(|| "the recurrent conduct key lost its header".to_owned())?;
        if residual % witness.key_words != 0 {
            return Err("a later witness does not inhabit the deposited conduct chart".to_owned());
        }
        composite_key(witness, residual / witness.key_words)
    }

    pub fn encode_native_bytes(&self) -> Result<Vec<u8>, String> {
        self.validate()?;
        let mut bytes = Vec::new();
        bytes.extend_from_slice(REST_MAGIC);
        put_u64(
            &mut bytes,
            usize_u64(self.conduct_key_words, "conduct key width")?,
        );
        put_u64(
            &mut bytes,
            usize_u64(self.deposits.len(), "deposit population")?,
        );
        for deposit in &self.deposits {
            for word in &deposit.conduct_key {
                put_u32(&mut bytes, *word);
            }
            for value in deposit.law.words() {
                put_i64(&mut bytes, value);
            }
        }
        Ok(bytes)
    }

    pub fn decode_native_bytes(bytes: &[u8]) -> Result<Self, String> {
        let mut cursor = ByteCursor::new(bytes);
        if cursor.take(REST_MAGIC.len())? != REST_MAGIC {
            return Err("recurrent-section rest schema changed".to_owned());
        }
        let conduct_key_words = cursor.usize("conduct key width")?;
        let count = cursor.usize("deposit population")?;
        let mut deposits = Vec::with_capacity(count);
        for _ in 0..count {
            let mut conduct_key = Vec::with_capacity(conduct_key_words);
            for _ in 0..conduct_key_words {
                conduct_key.push(cursor.u32()?);
            }
            let mut values = [0i64; 8];
            for value in &mut values {
                *value = cursor.i64()?;
            }
            deposits.push(RecurrentLawDeposit {
                conduct_key,
                law: BiaffineLaw {
                    origin: [values[0], values[1]],
                    step: [values[2], values[3]],
                    coefficients: [values[4], values[5], values[6], values[7]],
                },
            });
        }
        if !cursor.finished() {
            return Err("recurrent-section rest has trailing material".to_owned());
        }
        let morphology = Self {
            conduct_key_words,
            deposits,
        };
        morphology.validate()?;
        Ok(morphology)
    }

    fn validate(&self) -> Result<(), String> {
        if self.conduct_key_words < 3 || self.deposits.is_empty() {
            return Err("recurrent-section rest has no complete conduct".to_owned());
        }
        if self.deposits.iter().any(|deposit| {
            deposit.conduct_key.len() != self.conduct_key_words
                || deposit.law.step[0] == 0
                || deposit.law.step[1] == 0
        }) {
            return Err("recurrent-section rest carries a malformed law deposit".to_owned());
        }
        if self
            .deposits
            .windows(2)
            .any(|pair| pair[0].conduct_key >= pair[1].conduct_key)
        {
            return Err("recurrent-section law deposits are repeated or noncanonical".to_owned());
        }
        Ok(())
    }
}

fn composite_key_words(raw_key_words: usize, maximum_keys: usize) -> Result<usize, String> {
    raw_key_words
        .checked_mul(maximum_keys)
        .and_then(|words| words.checked_add(2))
        .ok_or_else(|| "the recurrent conduct key width overflowed".to_owned())
}

fn composite_key(
    witness: &SectionMorphologyWitness,
    maximum_keys: usize,
) -> Result<Vec<u32>, String> {
    if witness.keys.len() > maximum_keys {
        return Err("a later conduct witness exceeds the deposited aperture".to_owned());
    }
    let mut key = Vec::with_capacity(composite_key_words(witness.key_words, maximum_keys)?);
    key.push(
        u32::try_from(witness.key_words)
            .map_err(|_| "the raw conduct key width exceeds u32".to_owned())?,
    );
    key.push(
        u32::try_from(witness.keys.len())
            .map_err(|_| "the conduct witness population exceeds u32".to_owned())?,
    );
    for row in &witness.keys {
        key.extend_from_slice(row);
    }
    key.resize(composite_key_words(witness.key_words, maximum_keys)?, 0);
    Ok(key)
}

fn validate_presentations(presentations: &[SectionPresentation]) -> Result<(), String> {
    if presentations.is_empty() {
        return Err("no later causal-section presentation was supplied".to_owned());
    }
    let mut identities = BTreeSet::new();
    for presentation in presentations {
        if presentation.identity.is_empty()
            || presentation.lineage.is_empty()
            || !identities.insert(presentation.identity.clone())
            || presentation.states.is_empty()
            || presentation.root >= presentation.states.len()
        {
            return Err("a later causal-section presentation is malformed".to_owned());
        }
        for state in &presentation.states {
            if state.successors.keys().any(String::is_empty)
                || state
                    .successors
                    .values()
                    .any(|successor| *successor >= presentation.states.len())
            {
                return Err("a later causal-section successor face is malformed".to_owned());
            }
        }
        causal_depths(&presentation.states, presentation.root)?;
    }
    Ok(())
}

fn found_incidence(presentation: &SectionPresentation) -> Result<IncidenceComplex, String> {
    let occurrence = DeclaredOccurrence::from_text(
        format!("{}:later-incidence", presentation.identity),
        0,
        BTreeSet::new(),
        &presentation.incidence_text,
    )
    .map_err(|error| format!("declare section incidence: {error:?}"))?;
    let patches = occurrence.inscription.len();
    let faces = presentation
        .contact_faces
        .iter()
        .map(|face| {
            DeclaredContactFace::new(face.clone())
                .map_err(|error| format!("found later contact face: {error:?}"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    IncidenceComplex::found_with_contact_faces(&[occurrence], patches, &[faces])
        .map_err(|error| format!("found later section incidence: {error:?}"))
}

fn causal_depths(states: &[PresentedSectionState], root: usize) -> Result<Vec<usize>, String> {
    let mut depths = vec![usize::MAX; states.len()];
    depths[root] = 0;
    let mut front = vec![root];
    while let Some(state) = front.pop() {
        let next = depths[state]
            .checked_add(1)
            .ok_or_else(|| "the recurrent-section causal depth overflowed".to_owned())?;
        for successor in states[state].successors.values() {
            if depths[*successor] > next {
                depths[*successor] = next;
                front.push(*successor);
            }
        }
    }
    if depths.contains(&usize::MAX) {
        return Err("a later section state is outside its causal root front".to_owned());
    }
    Ok(depths)
}

fn count_reconvergent_diamonds(
    states: &[PresentedSectionState],
    root: usize,
) -> Result<usize, String> {
    let first = states
        .get(root)
        .ok_or_else(|| "the later section root is outside its states".to_owned())?
        .successors
        .values()
        .copied()
        .collect::<BTreeSet<_>>();
    let mut population = 0usize;
    for (at, left) in first.iter().enumerate() {
        for right in first.iter().skip(at + 1) {
            let left_tips = states[*left]
                .successors
                .values()
                .copied()
                .collect::<BTreeSet<_>>();
            let right_tips = states[*right]
                .successors
                .values()
                .copied()
                .collect::<BTreeSet<_>>();
            population = population
                .checked_add(left_tips.intersection(&right_tips).count())
                .ok_or_else(|| "the recurrent-section diamond population overflowed".to_owned())?;
        }
    }
    Ok(population)
}

fn usize_u64(value: usize, field: &str) -> Result<u64, String> {
    u64::try_from(value).map_err(|_| format!("recurrent-section {field} exceeds u64"))
}

fn put_u32(bytes: &mut Vec<u8>, value: u32) {
    bytes.extend_from_slice(&value.to_le_bytes());
}

fn put_u64(bytes: &mut Vec<u8>, value: u64) {
    bytes.extend_from_slice(&value.to_le_bytes());
}

fn put_i64(bytes: &mut Vec<u8>, value: i64) {
    bytes.extend_from_slice(&value.to_le_bytes());
}

struct ByteCursor<'a> {
    bytes: &'a [u8],
    at: usize,
}

impl<'a> ByteCursor<'a> {
    fn new(bytes: &'a [u8]) -> Self {
        Self { bytes, at: 0 }
    }

    fn take(&mut self, extent: usize) -> Result<&'a [u8], String> {
        let end = self
            .at
            .checked_add(extent)
            .ok_or_else(|| "recurrent-section rest cursor overflowed".to_owned())?;
        let value = self
            .bytes
            .get(self.at..end)
            .ok_or_else(|| "recurrent-section rest ended inside a field".to_owned())?;
        self.at = end;
        Ok(value)
    }

    fn u32(&mut self) -> Result<u32, String> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
    }

    fn u64(&mut self) -> Result<u64, String> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }

    fn i64(&mut self) -> Result<i64, String> {
        Ok(i64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }

    fn usize(&mut self, field: &str) -> Result<usize, String> {
        usize::try_from(self.u64()?).map_err(|_| format!("recurrent-section {field} exceeds usize"))
    }

    fn finished(&self) -> bool {
        self.at == self.bytes.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn witness(key: u32) -> SectionMorphologyWitness {
        SectionMorphologyWitness::new(2, vec![vec![0, key]], 2).unwrap()
    }

    #[test]
    fn native_rest_carries_anonymous_generative_laws_not_samples_or_sections() {
        let first = RecurrentLawDeposit {
            conduct_key: composite_key(&witness(1), 1).unwrap(),
            law: BiaffineLaw {
                origin: [2, 2],
                step: [1, 1],
                coefficients: [4, 1, 1, 0],
            },
        };
        let morphology = RecurrentSectionMorphology {
            conduct_key_words: first.conduct_key.len(),
            deposits: vec![first],
        };
        let bytes = morphology.encode_native_bytes().unwrap();
        for forbidden in ["infix-sum", "2 + 2", "founding/source/path"] {
            assert!(!bytes
                .windows(forbidden.len())
                .any(|window| window == forbidden.as_bytes()));
        }
        let remounted = RecurrentSectionMorphology::decode_native_bytes(&bytes).unwrap();
        assert_eq!(remounted, morphology);
        assert_eq!(remounted.encode_native_bytes().unwrap(), bytes);
        assert_eq!(remounted.distinct_transformation_laws(), 1);
    }

    #[test]
    fn malformed_or_nonrecurrent_witness_refuses_before_founding() {
        assert!(SectionMorphologyWitness::new(2, vec![vec![0, 1]], 1).is_err());
        assert!(SectionMorphologyWitness::new(2, vec![vec![0]], 2).is_err());
        assert!(SectionMorphologyWitness::new(2, vec![vec![0, 1], vec![0, 1]], 2).is_err());
    }
}
