//! Interpreter-free code material as recurrent causal world-lines.
//!
//! Raw source is read only through the resident material-shadow mouth. A caused transition return
//! may found an exact local law only when the source also crossed plural recurrent material
//! conduct. Native rest retains the anonymous shadow key and law, never source, parser state,
//! presentation identity, sample coordinates, or sample answers. A later passage is attached on
//! the card, folded on the card, and handed to `causal_section` as its complete state world-line.

use std::collections::{BTreeMap, BTreeSet};

use holonic_structure::LocalSequence;
use serde::Serialize;

use crate::{
    causal_section::{CausalSection, SectionState},
    incidence_production::{DeclaredOccurrence, IncidenceComplex},
    material_shadow_cuda::{
        CudaMaterialShadowExecutor, MaterialShadowCudaReceipt, MaterialShadowKey,
        MaterialShadowReading,
    },
    morphological_language::{
        CudaMorphologicalConductExecutor, MorphologicalConductCandidate,
        MorphologicalConductCandidateKey, MorphologicalConductCudaFront,
        MorphologicalConductCudaReceipt, MorphologicalConductDepositRow,
    },
    recurrent_section::SectionMorphologyWitness,
    recurrent_section_cuda::{
        BiaffineLaw, BiaffineSampleGrid, CudaRecurrentLawExecutor, RecurrentFoldEvaluation,
        RecurrentFoldQuery, RecurrentLawCudaReceipt,
    },
};

const REST_MAGIC: &[u8; 8] = b"ALGM\0\0\0\x01";

#[derive(Clone, Debug)]
pub struct ReturnedCodeTransition {
    pub shadow: MaterialShadowKey,
    pub recurrent_material: SectionMorphologyWitness,
    pub samples: BiaffineSampleGrid,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct AlgorithmicDeposit {
    shadow: MaterialShadowKey,
    law: BiaffineLaw,
}

#[derive(Debug, PartialEq, Eq)]
pub struct AlgorithmicMaterialMorphology {
    deposits: Vec<AlgorithmicDeposit>,
}

#[derive(Clone, Debug)]
pub struct CodeMaterialPresentation {
    pub identity: String,
    pub lineage: String,
    pub source: Vec<u8>,
    pub initial: i64,
    pub currents: Vec<i64>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct MaterialShadowGeometry {
    pub prior_equal_distance: Vec<u32>,
    pub recurrence_phase_distribution: BTreeMap<u32, usize>,
    pub recurrence_arcs: Vec<[usize; 2]>,
    pub path_edges: usize,
    pub recurrence_edges: usize,
    pub cycle_rank: usize,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AlgorithmicCandidateWorldLine {
    pub newton_coefficients: [i64; 4],
    pub trace: Vec<i64>,
    pub terminus: Option<i64>,
    pub obstruction: Option<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AlgorithmicPassageReading {
    pub identity: String,
    pub active: bool,
    pub material_shadow: MaterialShadowGeometry,
    pub candidate_world_lines: Vec<AlgorithmicCandidateWorldLine>,
    pub open: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AlgorithmicMaterialReceipt {
    pub schema: String,
    pub presentations: usize,
    pub deposits: usize,
    pub active_deposits: usize,
    pub distinct_laws: usize,
    pub complete_world_lines: usize,
    pub open_passages: usize,
    pub recurrence_phase_distribution: BTreeMap<u32, usize>,
    pub material_shadow_apparatus: MaterialShadowCudaReceipt,
    pub attachment_apparatus: MorphologicalConductCudaReceipt,
    pub fold_apparatus: Option<RecurrentLawCudaReceipt>,
    pub readings: Vec<AlgorithmicPassageReading>,
}

#[derive(Debug)]
pub struct AlgorithmicMaterialFormation {
    pub sections: Vec<CausalSection>,
    pub receipt: AlgorithmicMaterialReceipt,
}

impl AlgorithmicMaterialMorphology {
    pub fn found(
        returned: Vec<ReturnedCodeTransition>,
        laws: &mut CudaRecurrentLawExecutor,
    ) -> Result<(Self, RecurrentLawCudaReceipt), String> {
        if returned.is_empty() {
            return Err("no code-material transition return reached the body".to_owned());
        }
        if returned.iter().any(|passage| {
            passage.recurrent_material.distinct_sources() < 2
                || passage.recurrent_material.keys().is_empty()
        }) {
            return Err(
                "a code-material transition did not cross plural recurrent conduct".to_owned(),
            );
        }
        let grids = returned
            .iter()
            .map(|passage| passage.samples)
            .collect::<Vec<_>>();
        let (founded, apparatus) = laws.found(&grids)?;
        let mut deposits = returned
            .into_iter()
            .zip(founded)
            .map(|(passage, law)| AlgorithmicDeposit {
                shadow: passage.shadow,
                law,
            })
            .collect::<Vec<_>>();
        deposits.sort();
        deposits.dedup();
        let morphology = Self { deposits };
        morphology.validate()?;
        Ok((morphology, apparatus))
    }

    pub fn deposits(&self) -> usize {
        self.deposits.len()
    }

    pub fn distinct_laws(&self) -> usize {
        self.deposits
            .iter()
            .map(|deposit| deposit.law)
            .collect::<BTreeSet<_>>()
            .len()
    }

    pub fn form(
        &self,
        presentations: &[CodeMaterialPresentation],
        shadows: &mut CudaMaterialShadowExecutor,
        conduct: &mut CudaMorphologicalConductExecutor,
        laws: &mut CudaRecurrentLawExecutor,
    ) -> Result<AlgorithmicMaterialFormation, String> {
        self.form_inner(presentations, None, shadows, conduct, laws)
    }

    pub fn form_without_shadow(
        &self,
        presentations: &[CodeMaterialPresentation],
        ablated: &MaterialShadowKey,
        shadows: &mut CudaMaterialShadowExecutor,
        conduct: &mut CudaMorphologicalConductExecutor,
        laws: &mut CudaRecurrentLawExecutor,
    ) -> Result<AlgorithmicMaterialFormation, String> {
        if !self
            .deposits
            .iter()
            .any(|deposit| deposit.shadow == *ablated)
        {
            return Err("the requested material shadow names no deposit".to_owned());
        }
        self.form_inner(presentations, Some(ablated), shadows, conduct, laws)
    }

    fn form_inner(
        &self,
        presentations: &[CodeMaterialPresentation],
        ablated: Option<&MaterialShadowKey>,
        shadows: &mut CudaMaterialShadowExecutor,
        conduct: &mut CudaMorphologicalConductExecutor,
        laws: &mut CudaRecurrentLawExecutor,
    ) -> Result<AlgorithmicMaterialFormation, String> {
        self.validate()?;
        validate_presentations(presentations)?;
        let source = presentations
            .iter()
            .map(|presentation| presentation.source.as_slice())
            .collect::<Vec<_>>();
        let (shadow_readings, shadow_apparatus) = shadows.read(&source)?;
        let candidates = (0..presentations.len())
            .map(|at| {
                MorphologicalConductCandidate::new(
                    u32::try_from(at)
                        .map_err(|_| "the code-material population exceeds u32".to_owned())?,
                )
                .ok_or_else(|| "a code-material passage used the reserved open face".to_owned())
            })
            .collect::<Result<LocalSequence<_>, _>>()?;
        let deposited_shadows = self
            .deposits
            .iter()
            .map(|deposit| deposit.shadow.clone())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect::<Vec<_>>();
        let key_words = deposited_shadows
            .iter()
            .map(|shadow| shadow.words().len())
            .chain(
                shadow_readings
                    .iter()
                    .map(|reading| reading.key.words().len()),
            )
            .max()
            .ok_or_else(|| "the code-material front has no exact shadow width".to_owned())?;
        let deposit_rows = deposited_shadows
            .iter()
            .map(|shadow| {
                Ok(MorphologicalConductDepositRow::new(
                    ablated != Some(shadow),
                    shadow.padded_words(key_words)?.into_iter().collect(),
                ))
            })
            .collect::<Result<LocalSequence<_>, String>>()?;
        let candidate_rows = shadow_readings
            .iter()
            .enumerate()
            .map(|(at, reading)| {
                Ok(MorphologicalConductCandidateKey::new(
                    u32::try_from(at).map_err(|_| {
                        "the code-material candidate population exceeds u32".to_owned()
                    })?,
                    reading.key.padded_words(key_words)?.into_iter().collect(),
                ))
            })
            .collect::<Result<LocalSequence<_>, String>>()?;
        let front =
            MorphologicalConductCudaFront::new(key_words, candidates, deposit_rows, candidate_rows)
                .map_err(|error| format!("found code-material attachment front: {error}"))?;
        let attached = conduct
            .enact(&front)
            .map_err(|error| format!("attach code-material shadow: {error}"))?;

        let mut queries = Vec::new();
        let mut destinations = Vec::new();
        let mut presentation_laws = vec![Vec::<BiaffineLaw>::new(); presentations.len()];
        for (presentation_at, candidate) in attached.semantic.candidates.iter().enumerate() {
            if candidate.candidate as usize != presentation_at {
                return Err("the card reordered code-material passages".to_owned());
            }
            for deposit_at in &candidate.active_deposits {
                let shadow = deposited_shadows
                    .get(*deposit_at as usize)
                    .ok_or_else(|| "the card attached outside algorithmic rest".to_owned())?;
                for law in self
                    .deposits
                    .iter()
                    .filter(|deposit| deposit.shadow == *shadow)
                    .map(|deposit| deposit.law)
                {
                    presentation_laws[presentation_at].push(law);
                    destinations.push(presentation_at);
                    queries.push(RecurrentFoldQuery {
                        law,
                        initial: presentations[presentation_at].initial,
                        currents: presentations[presentation_at].currents.clone(),
                    });
                }
            }
        }
        let (folded, fold_apparatus) = if queries.is_empty() {
            (Vec::new(), None)
        } else {
            let (returned, apparatus) = laws.fold(&queries)?;
            (returned, Some(apparatus))
        };
        if folded.len() != destinations.len() {
            return Err("the card changed the recurrent world-line population".to_owned());
        }
        let mut candidates_by_presentation =
            vec![Vec::<AlgorithmicCandidateWorldLine>::new(); presentations.len()];
        for ((presentation_at, law), evaluation) in destinations
            .into_iter()
            .zip(queries.iter().map(|query| query.law))
            .zip(folded)
        {
            let reading = match evaluation {
                RecurrentFoldEvaluation::Complete { trace, terminus } => {
                    AlgorithmicCandidateWorldLine {
                        newton_coefficients: law.coefficients,
                        trace,
                        terminus: Some(terminus),
                        obstruction: None,
                    }
                }
                RecurrentFoldEvaluation::OutsideLattice => AlgorithmicCandidateWorldLine {
                    newton_coefficients: law.coefficients,
                    trace: Vec::new(),
                    terminus: None,
                    obstruction: Some("outside-founded-lattice".to_owned()),
                },
                RecurrentFoldEvaluation::FiniteCarrierOverflow => AlgorithmicCandidateWorldLine {
                    newton_coefficients: law.coefficients,
                    trace: Vec::new(),
                    terminus: None,
                    obstruction: Some("finite-carrier-overflow".to_owned()),
                },
            };
            candidates_by_presentation[presentation_at].push(reading);
        }

        let mut recurrence_phase_distribution = BTreeMap::new();
        let mut readings = Vec::with_capacity(presentations.len());
        let mut sections = Vec::with_capacity(presentations.len());
        let mut complete_world_lines = 0usize;
        let mut open_passages = 0usize;
        for (at, presentation) in presentations.iter().enumerate() {
            let geometry = shadow_geometry(&shadow_readings[at]);
            for (gap, population) in &geometry.recurrence_phase_distribution {
                *recurrence_phase_distribution.entry(*gap).or_insert(0) += *population;
            }
            let candidates = &candidates_by_presentation[at];
            complete_world_lines = complete_world_lines
                .checked_add(
                    candidates
                        .iter()
                        .filter(|candidate| candidate.terminus.is_some())
                        .count(),
                )
                .ok_or_else(|| "the complete world-line population overflowed".to_owned())?;
            let open = candidates.is_empty()
                || candidates
                    .iter()
                    .all(|candidate| candidate.terminus.is_none());
            if open {
                open_passages = open_passages
                    .checked_add(1)
                    .ok_or_else(|| "the open passage population overflowed".to_owned())?;
            }
            sections.push(world_line_section(presentation, candidates)?);
            readings.push(AlgorithmicPassageReading {
                identity: presentation.identity.clone(),
                active: !presentation_laws[at].is_empty(),
                material_shadow: geometry,
                candidate_world_lines: candidates.clone(),
                open,
            });
        }
        Ok(AlgorithmicMaterialFormation {
            sections,
            receipt: AlgorithmicMaterialReceipt {
                schema: "soma-life.algorithmic-material-return.v1".to_owned(),
                presentations: presentations.len(),
                deposits: self.deposits.len(),
                active_deposits: deposited_shadows
                    .iter()
                    .filter(|shadow| ablated != Some(*shadow))
                    .count(),
                distinct_laws: self.distinct_laws(),
                complete_world_lines,
                open_passages,
                recurrence_phase_distribution,
                material_shadow_apparatus: shadow_apparatus,
                attachment_apparatus: attached.apparatus,
                fold_apparatus,
                readings,
            },
        })
    }

    pub fn encode_native_bytes(&self) -> Result<Vec<u8>, String> {
        self.validate()?;
        let mut bytes = Vec::new();
        bytes.extend_from_slice(REST_MAGIC);
        put_u64(
            &mut bytes,
            usize_u64(self.deposits.len(), "deposit population")?,
        );
        for deposit in &self.deposits {
            put_u64(
                &mut bytes,
                usize_u64(deposit.shadow.words().len(), "shadow key width")?,
            );
            for word in deposit.shadow.words() {
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
            return Err("algorithmic-material rest schema changed".to_owned());
        }
        let count = cursor.usize("deposit population")?;
        let mut deposits = Vec::with_capacity(count);
        for _ in 0..count {
            let width = cursor.usize("shadow key width")?;
            let mut key = Vec::with_capacity(width);
            for _ in 0..width {
                key.push(cursor.u32()?);
            }
            let mut values = [0i64; 8];
            for value in &mut values {
                *value = cursor.i64()?;
            }
            deposits.push(AlgorithmicDeposit {
                shadow: MaterialShadowKey::from_words(key)?,
                law: BiaffineLaw {
                    origin: [values[0], values[1]],
                    step: [values[2], values[3]],
                    coefficients: [values[4], values[5], values[6], values[7]],
                },
            });
        }
        if !cursor.finished() {
            return Err("algorithmic-material rest has trailing material".to_owned());
        }
        let morphology = Self { deposits };
        morphology.validate()?;
        Ok(morphology)
    }

    fn validate(&self) -> Result<(), String> {
        if self.deposits.is_empty()
            || self
                .deposits
                .iter()
                .any(|deposit| deposit.law.step.contains(&0))
            || self.deposits.windows(2).any(|pair| pair[0] >= pair[1])
        {
            return Err(
                "algorithmic-material rest is empty, malformed, or noncanonical".to_owned(),
            );
        }
        Ok(())
    }
}

fn validate_presentations(presentations: &[CodeMaterialPresentation]) -> Result<(), String> {
    if presentations.is_empty() {
        return Err("no later code material was supplied".to_owned());
    }
    let mut identities = BTreeSet::new();
    for presentation in presentations {
        if presentation.identity.is_empty()
            || presentation.lineage.is_empty()
            || presentation.source.is_empty()
            || presentation.currents.is_empty()
            || !identities.insert(presentation.identity.clone())
        {
            return Err("a later code-material presentation is malformed".to_owned());
        }
    }
    Ok(())
}

fn shadow_geometry(reading: &MaterialShadowReading) -> MaterialShadowGeometry {
    let mut recurrence_phase_distribution = BTreeMap::new();
    let mut recurrence_arcs = Vec::new();
    let mut edges = BTreeSet::new();
    for position in 1..reading.prior_equal_distance.len() {
        edges.insert((position - 1, position));
    }
    for (position, gap) in reading.prior_equal_distance.iter().copied().enumerate() {
        *recurrence_phase_distribution.entry(gap).or_insert(0) += 1;
        if gap != 0 {
            let prior = position - gap as usize;
            recurrence_arcs.push([prior, position]);
            edges.insert((prior, position));
        }
    }
    let vertices = reading.prior_equal_distance.len();
    let cycle_rank = edges.len().saturating_add(1).saturating_sub(vertices);
    MaterialShadowGeometry {
        prior_equal_distance: reading.prior_equal_distance.clone(),
        recurrence_phase_distribution,
        recurrence_arcs,
        path_edges: vertices.saturating_sub(1),
        recurrence_edges: reading
            .prior_equal_distance
            .iter()
            .filter(|gap| **gap != 0)
            .count(),
        cycle_rank,
    }
}

fn world_line_section(
    presentation: &CodeMaterialPresentation,
    candidates: &[AlgorithmicCandidateWorldLine],
) -> Result<CausalSection, String> {
    let source = String::from_utf8(presentation.source.clone())
        .map_err(|_| "code material is not an exterior UTF-8 presentation".to_owned())?;
    let occurrence = DeclaredOccurrence::from_text(
        format!("{}:later-material", presentation.identity),
        0,
        BTreeSet::new(),
        &source,
    )
    .map_err(|error| format!("declare code material: {error:?}"))?;
    let patches = occurrence.inscription.len();
    let incidence = IncidenceComplex::found(&[occurrence], patches)
        .map_err(|error| format!("found code-material incidence: {error:?}"))?;
    let complete = candidates
        .iter()
        .filter(|candidate| candidate.terminus.is_some())
        .collect::<Vec<_>>();
    let states = if complete.is_empty() {
        vec![SectionState {
            observations: BTreeMap::from([
                ("current".to_owned(), "OPEN".to_owned()),
                ("standing".to_owned(), "OPEN".to_owned()),
                ("terminus".to_owned(), "yes".to_owned()),
            ]),
            successors: BTreeMap::new(),
        }]
    } else {
        let extent = complete[0].trace.len();
        if complete
            .iter()
            .any(|candidate| candidate.trace.len() != extent)
        {
            return Err("candidate world-lines change causal extent".to_owned());
        }
        (0..extent)
            .map(|at| {
                let standing = complete
                    .iter()
                    .map(|candidate| candidate.trace[at])
                    .collect::<BTreeSet<_>>()
                    .into_iter()
                    .map(|value| value.to_string())
                    .collect::<Vec<_>>()
                    .join("|");
                let current = if at == 0 {
                    "INGRESS".to_owned()
                } else {
                    presentation.currents[at - 1].to_string()
                };
                Ok(SectionState {
                    observations: BTreeMap::from([
                        ("current".to_owned(), current),
                        ("standing".to_owned(), standing),
                        (
                            "terminus".to_owned(),
                            if at + 1 == extent { "yes" } else { "no" }.to_owned(),
                        ),
                    ]),
                    successors: if at + 1 == extent {
                        BTreeMap::new()
                    } else {
                        BTreeMap::from([("advance".to_owned(), at + 1)])
                    },
                })
            })
            .collect::<Result<Vec<_>, String>>()?
    };
    Ok(CausalSection {
        identity: presentation.identity.clone(),
        lineage: presentation.lineage.clone(),
        incidence,
        states,
        root: 0,
    })
}

fn usize_u64(value: usize, field: &str) -> Result<u64, String> {
    u64::try_from(value).map_err(|_| format!("algorithmic-material {field} exceeds u64"))
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
            .ok_or_else(|| "algorithmic-material rest cursor overflowed".to_owned())?;
        let value = self
            .bytes
            .get(self.at..end)
            .ok_or_else(|| "algorithmic-material rest ended inside a field".to_owned())?;
        self.at = end;
        Ok(value)
    }

    fn u32(&mut self) -> Result<u32, String> {
        Ok(u32::from_le_bytes(self.take(4)?.try_into().unwrap()))
    }

    fn u64(&mut self) -> Result<u64, String> {
        Ok(u64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }

    fn usize(&mut self, field: &str) -> Result<usize, String> {
        usize::try_from(self.u64()?)
            .map_err(|_| format!("algorithmic-material {field} exceeds usize"))
    }

    fn i64(&mut self) -> Result<i64, String> {
        Ok(i64::from_le_bytes(self.take(8)?.try_into().unwrap()))
    }

    fn finished(&self) -> bool {
        self.at == self.bytes.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn law(coefficients: [i64; 4]) -> BiaffineLaw {
        BiaffineLaw {
            origin: [0, 0],
            step: [1, 1],
            coefficients,
        }
    }

    #[test]
    fn native_rest_retains_a_plural_law_fiber_without_source() {
        let shadow = MaterialShadowKey::from_words(vec![3, 0, 1, 2]).unwrap();
        let morphology = AlgorithmicMaterialMorphology {
            deposits: vec![
                AlgorithmicDeposit {
                    shadow: shadow.clone(),
                    law: law([0, 0, 0, 1]),
                },
                AlgorithmicDeposit {
                    shadow,
                    law: law([0, 1, 1, 0]),
                },
            ],
        };
        let bytes = morphology.encode_native_bytes().unwrap();
        let remounted = AlgorithmicMaterialMorphology::decode_native_bytes(&bytes).unwrap();
        assert_eq!(remounted, morphology);
        assert_eq!(remounted.deposits(), 2);
        assert_eq!(remounted.distinct_laws(), 2);
        assert!(!bytes.windows(6).any(|window| window == b"source"));
    }
}
