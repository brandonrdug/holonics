//! Source-detached relational potential carried by native Athena factors.
//!
//! Text is accepted only at the boundary.  During cultivation the inherited relational codec
//! transduces each delivered occurrence into oriented subject--relation--object incidence and the
//! passage is dropped immediately.  The rested complex owns exact causal occurrence signatures,
//! factor support, and triangular incidence.  A separate codec chart relates exterior surfaces to
//! those signatures; no word, glyph, source sentence, or prompt becomes a native address.

use std::collections::{BTreeMap, BTreeSet, HashMap};

use serde::{Deserialize, Serialize};
use sha2::{Digest, Sha256};

use crate::{
    morphological_language::MorphologicalLanguagePassage,
    relational_language::{
        relational_deliberation_frontier, relational_passage_clauses, RelationalClause,
        RelationalClauseVoice, RelationalEntity,
    },
};

use super::NativeCirculationError;

const POTENTIAL_SCHEMA: &str = "soma-life.native-relational-potential.v4";
const CODEC_SCHEMA: &str = "soma-life.native-relational-boundary-codec.v2";
const FACE_ADDRESS_DOMAIN: &[u8] = b"soma-life.native-relational-face.v4";
const CELL_ADDRESS_DOMAIN: &[u8] = b"soma-life.native-relational-cell.v4";
const SOURCE_OCCURRENCE_DOMAIN: &[u8] = b"soma-life.native-relational-source-occurrence.v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(super) enum NativeRelationalFaceKind {
    Entity,
    /// The addressed participant port founded by dialogue lineage. `I`, `you`, and `user` are
    /// exterior variants of this port in their respective delivery orientations.
    Participant,
    Relation,
    Modality,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(super) enum NativeRelationalRole {
    Subject,
    Relation,
    Modality,
    Object,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub(super) enum NativeDeliveryPhase {
    Ingress,
    Emanation,
    Return,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct NativeRelationalFaceOccurrence {
    pub factor: u32,
    pub phase: NativeDeliveryPhase,
    pub role: NativeRelationalRole,
    /// Content-addressed exterior occurrence lineage.  The surface does not become native
    /// identity, but changing one caused source occurrence must change the descended section even
    /// when every global count and grammatical role is unchanged.
    pub source_occurrence_identity_sha256: String,
    pub first_delivery_order: u64,
    pub last_delivery_order: u64,
    pub occurrence_population: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct NativeRelationalFace {
    pub address: String,
    pub kind: NativeRelationalFaceKind,
    pub founding_delivery_order: u64,
    pub founding_clause_order: u64,
    /// Descended receiver sections plus their retained population fibre. Equality also preserves
    /// the founding caused occurrence; it is never inferred from the address digest alone.
    pub occurrences: Vec<NativeRelationalFaceOccurrence>,
    pub factor_support: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct NativeRelationalCellOccurrence {
    pub factor: u32,
    pub phase: NativeDeliveryPhase,
    pub source_occurrence_identity_sha256: String,
    pub first_delivery_order: u64,
    pub last_delivery_order: u64,
    pub occurrence_population: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct TempFaceOccurrence {
    factor: u32,
    phase: NativeDeliveryPhase,
    delivery_order: u64,
    clause_order: u64,
    role: NativeRelationalRole,
    source_occurrence_identity_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
struct TempCellOccurrence {
    factor: u32,
    phase: NativeDeliveryPhase,
    pub delivery_order: u64,
    pub clause_order: u64,
    source_occurrence_identity_sha256: String,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
struct NativeCellKey {
    subject: u32,
    relation: u32,
    modality: Option<u32>,
    object: u32,
    copular: bool,
}

/// One oriented 2-simplex. Its boundary is the exact cycle
/// `subject -> relation -> object -> subject`; this is the native close, not punctuation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct NativeRelationalCell {
    pub address: String,
    pub subject: u32,
    pub relation: u32,
    pub modality: Option<u32>,
    pub object: u32,
    pub copular: bool,
    pub occurrences: Vec<NativeRelationalCellOccurrence>,
    pub factor_support: Vec<u32>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct NativeRelationalPotentialComplex {
    schema: String,
    pub factor_addresses: Vec<String>,
    /// Source-neutral joins between adjacent continuation factors on one addressed world-line.
    pub factor_adjacency: Vec<(u32, u32)>,
    pub faces: Vec<NativeRelationalFace>,
    pub cells: Vec<NativeRelationalCell>,
    pub obstructed_delivery_population: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct BoundaryFaceKey {
    kind: NativeRelationalFaceKind,
    identity: Vec<String>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
struct NativeBoundaryFace {
    key: BoundaryFaceKey,
    surface_variants: Vec<Vec<String>>,
    native_face: u32,
}

/// Exterior ingress/egress chart. It is a separately addressed rest component and never a native
/// potential coordinate.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub(super) struct NativeRelationalCodec {
    schema: String,
    faces: Vec<NativeBoundaryFace>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) struct NativeRelationalContact {
    pub required_regions: Vec<Vec<String>>,
    pub faces: Vec<u32>,
    pub factor_support: Vec<u32>,
    pub participant_alias: Option<(u32, u32)>,
}

#[derive(Clone, Debug)]
struct TempFace {
    key: BoundaryFaceKey,
    variants: BTreeSet<Vec<String>>,
    occurrences: Vec<TempFaceOccurrence>,
}

#[derive(Clone, Debug)]
struct TempCell {
    key: (u32, u32, Option<u32>, u32, bool),
    occurrences: Vec<TempCellOccurrence>,
}

/// Streaming cultivation owner. At most one delivered source passage is materialized at a time.
pub(super) struct NativeRelationalPotentialBuilder {
    factor_addresses: Vec<String>,
    factor_adjacency: BTreeSet<(u32, u32)>,
    face_index: HashMap<BoundaryFaceKey, u32>,
    faces: Vec<TempFace>,
    cell_index: HashMap<(u32, u32, Option<u32>, u32, bool), u32>,
    cells: Vec<TempCell>,
    delivery_order: u64,
    clause_population: u64,
    obstructed_delivery_population: u64,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct NativeRelationalConditionReceipt {
    pub delivered_occurrence_population: u64,
    pub relational_clause_population: u64,
    pub obstructed_delivery_population: u64,
    pub native_face_population: usize,
    pub native_cell_population: usize,
    pub factor_world_line_join_population: usize,
    pub descended_face_section_population: usize,
    pub descended_cell_section_population: usize,
    pub retained_face_occurrence_population: u64,
    pub retained_cell_occurrence_population: u64,
    pub source_clause_ledger_retained: bool,
    pub triangular_boundary_defect_population: usize,
}

impl NativeRelationalPotentialBuilder {
    pub fn new(factor_addresses: Vec<String>) -> Result<Self, NativeCirculationError> {
        if factor_addresses.is_empty()
            || factor_addresses.iter().any(String::is_empty)
            || factor_addresses.iter().collect::<BTreeSet<_>>().len() != factor_addresses.len()
        {
            return Err(NativeCirculationError::Standing);
        }
        Ok(Self {
            factor_addresses,
            factor_adjacency: BTreeSet::new(),
            face_index: HashMap::new(),
            faces: Vec::new(),
            cell_index: HashMap::new(),
            cells: Vec::new(),
            delivery_order: 0,
            clause_population: 0,
            obstructed_delivery_population: 0,
        })
    }

    pub fn join_factors(
        &mut self,
        left: usize,
        right: usize,
    ) -> Result<(), NativeCirculationError> {
        if left >= self.factor_addresses.len()
            || right >= self.factor_addresses.len()
            || left == right
        {
            return Err(NativeCirculationError::Standing);
        }
        let left = u32::try_from(left).map_err(|_| NativeCirculationError::Standing)?;
        let right = u32::try_from(right).map_err(|_| NativeCirculationError::Standing)?;
        self.factor_adjacency
            .insert((left.min(right), left.max(right)));
        Ok(())
    }

    pub fn receive(
        &mut self,
        factor: usize,
        phase: NativeDeliveryPhase,
        source_occurrence: &str,
        text: &str,
    ) -> Result<(), NativeCirculationError> {
        if factor >= self.factor_addresses.len() || source_occurrence.is_empty() {
            return Err(NativeCirculationError::Standing);
        }
        let source_occurrence_identity_sha256 = digest(&(
            SOURCE_OCCURRENCE_DOMAIN,
            source_occurrence,
            Sha256::digest(text.as_bytes()).as_slice(),
        ))?;
        let delivery_order = self.delivery_order;
        self.delivery_order = self
            .delivery_order
            .checked_add(1)
            .ok_or(NativeCirculationError::Standing)?;
        let passage = MorphologicalLanguagePassage::new(
            format!("delivery-{delivery_order}"),
            format!("factor-{factor}"),
            0,
            text,
        )
        .with_source_order(u128::from(delivery_order));
        let clauses = match relational_passage_clauses(&passage) {
            Ok(clauses) => clauses,
            Err(_) => {
                self.obstructed_delivery_population = self
                    .obstructed_delivery_population
                    .checked_add(1)
                    .ok_or(NativeCirculationError::Standing)?;
                return Ok(());
            }
        };
        for clause in clauses {
            self.receive_clause(
                factor,
                phase,
                delivery_order,
                &source_occurrence_identity_sha256,
                clause,
            )?;
        }
        Ok(())
    }

    fn receive_clause(
        &mut self,
        factor: usize,
        phase: NativeDeliveryPhase,
        delivery_order: u64,
        source_occurrence_identity_sha256: &str,
        clause: RelationalClause,
    ) -> Result<(), NativeCirculationError> {
        let factor = u32::try_from(factor).map_err(|_| NativeCirculationError::Standing)?;
        let clause_order = self.clause_population;
        self.clause_population = self
            .clause_population
            .checked_add(1)
            .ok_or(NativeCirculationError::Standing)?;
        let subject = self.receive_face(
            situated_entity_key(&clause.subject, phase),
            clause.subject.surface,
            TempFaceOccurrence {
                factor,
                phase,
                delivery_order,
                clause_order,
                role: NativeRelationalRole::Subject,
                source_occurrence_identity_sha256: source_occurrence_identity_sha256.to_owned(),
            },
        )?;
        let relation_surface = vec![clause.relation.clone()];
        let relation = self.receive_face(
            BoundaryFaceKey {
                kind: NativeRelationalFaceKind::Relation,
                identity: relation_surface.clone(),
            },
            relation_surface,
            TempFaceOccurrence {
                factor,
                phase,
                delivery_order,
                clause_order,
                role: NativeRelationalRole::Relation,
                source_occurrence_identity_sha256: source_occurrence_identity_sha256.to_owned(),
            },
        )?;
        let modality = clause
            .modality
            .map(|modality| {
                self.receive_face(
                    BoundaryFaceKey {
                        kind: NativeRelationalFaceKind::Modality,
                        identity: vec![modality.clone()],
                    },
                    vec![modality],
                    TempFaceOccurrence {
                        factor,
                        phase,
                        delivery_order,
                        clause_order,
                        role: NativeRelationalRole::Modality,
                        source_occurrence_identity_sha256: source_occurrence_identity_sha256
                            .to_owned(),
                    },
                )
            })
            .transpose()?;
        let object = self.receive_face(
            situated_entity_key(&clause.object, phase),
            clause.object.surface,
            TempFaceOccurrence {
                factor,
                phase,
                delivery_order,
                clause_order,
                role: NativeRelationalRole::Object,
                source_occurrence_identity_sha256: source_occurrence_identity_sha256.to_owned(),
            },
        )?;
        let key = (
            subject,
            relation,
            modality,
            object,
            clause.witnessed_voice == RelationalClauseVoice::Copular,
        );
        let occurrence = TempCellOccurrence {
            factor,
            phase,
            delivery_order,
            clause_order,
            source_occurrence_identity_sha256: source_occurrence_identity_sha256.to_owned(),
        };
        if let Some(cell) = self.cell_index.get(&key).copied() {
            self.cells[cell as usize].occurrences.push(occurrence);
        } else {
            let cell =
                u32::try_from(self.cells.len()).map_err(|_| NativeCirculationError::Standing)?;
            self.cell_index.insert(key, cell);
            self.cells.push(TempCell {
                key,
                occurrences: vec![occurrence],
            });
        }
        Ok(())
    }

    fn receive_face(
        &mut self,
        key: BoundaryFaceKey,
        surface: Vec<String>,
        occurrence: TempFaceOccurrence,
    ) -> Result<u32, NativeCirculationError> {
        if key.identity.is_empty() || surface.is_empty() {
            return Err(NativeCirculationError::Standing);
        }
        if let Some(face) = self.face_index.get(&key).copied() {
            let held = &mut self.faces[face as usize];
            held.variants.insert(surface);
            held.occurrences.push(occurrence);
            return Ok(face);
        }
        let face = u32::try_from(self.faces.len()).map_err(|_| NativeCirculationError::Standing)?;
        self.face_index.insert(key.clone(), face);
        self.faces.push(TempFace {
            key,
            variants: BTreeSet::from([surface]),
            occurrences: vec![occurrence],
        });
        Ok(face)
    }

    pub fn finish(
        self,
    ) -> Result<
        (
            NativeRelationalCodec,
            NativeRelationalPotentialComplex,
            NativeRelationalConditionReceipt,
        ),
        NativeCirculationError,
    > {
        if self.clause_population == 0 || self.faces.is_empty() || self.cells.is_empty() {
            return Err(NativeCirculationError::Standing);
        }

        // Native face equality preserves the founding caused occurrence and the complete descended
        // receiver-section population. Boundary spelling is absent from this quotient and survives
        // only in the codec chart assembled below. The source clause ledger is deliberately not a
        // rested coordinate.
        let face_signatures = self
            .faces
            .iter()
            .map(|face| aggregate_face_occurrences(&face.occurrences))
            .collect::<Result<Vec<_>, _>>()?;
        let face_foundings = self
            .faces
            .iter()
            .map(|face| {
                face.occurrences
                    .iter()
                    .map(|occurrence| (occurrence.delivery_order, occurrence.clause_order))
                    .min()
                    .ok_or(NativeCirculationError::Standing)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let mut order = (0..self.faces.len()).collect::<Vec<_>>();
        order.sort_by(|left_at, right_at| {
            let left = &self.faces[*left_at];
            let right = &self.faces[*right_at];
            (
                left.key.kind,
                face_foundings[*left_at],
                &face_signatures[*left_at],
            )
                .cmp(&(
                    right.key.kind,
                    face_foundings[*right_at],
                    &face_signatures[*right_at],
                ))
        });
        let mut temp_to_native = vec![0u32; self.faces.len()];
        let mut native_faces = Vec::<NativeRelationalFace>::new();
        let mut prior_signature: Option<(
            NativeRelationalFaceKind,
            u64,
            u64,
            Vec<NativeRelationalFaceOccurrence>,
        )> = None;
        for temp_at in order {
            let temp = &self.faces[temp_at];
            let founding = face_foundings[temp_at];
            let signature = (
                temp.key.kind,
                founding.0,
                founding.1,
                face_signatures[temp_at].clone(),
            );
            let native_at = if prior_signature.as_ref() == Some(&signature) {
                native_faces.len() - 1
            } else {
                let factor_support = occurrence_factor_support(&signature.3);
                let address = digest(&(FACE_ADDRESS_DOMAIN, &signature))?;
                native_faces.push(NativeRelationalFace {
                    address,
                    kind: temp.key.kind,
                    founding_delivery_order: signature.1,
                    founding_clause_order: signature.2,
                    occurrences: signature.3.clone(),
                    factor_support,
                });
                prior_signature = Some(signature);
                native_faces.len() - 1
            };
            temp_to_native[temp_at] =
                u32::try_from(native_at).map_err(|_| NativeCirculationError::Standing)?;
        }

        let mut merged_cells = BTreeMap::<NativeCellKey, Vec<TempCellOccurrence>>::new();
        for temp in &self.cells {
            let key = NativeCellKey {
                subject: temp_to_native[temp.key.0 as usize],
                relation: temp_to_native[temp.key.1 as usize],
                modality: temp.key.2.map(|face| temp_to_native[face as usize]),
                object: temp_to_native[temp.key.3 as usize],
                copular: temp.key.4,
            };
            merged_cells
                .entry(key)
                .or_default()
                .extend(temp.occurrences.iter().cloned());
        }
        let mut native_cells = Vec::with_capacity(merged_cells.len());
        for (key, occurrences) in merged_cells {
            let occurrences = aggregate_cell_occurrences(&occurrences)?;
            let factor_support = cell_factor_support(&occurrences);
            let address = digest(&(CELL_ADDRESS_DOMAIN, &key, &occurrences))?;
            native_cells.push(NativeRelationalCell {
                address,
                subject: key.subject,
                relation: key.relation,
                modality: key.modality,
                object: key.object,
                copular: key.copular,
                occurrences,
                factor_support,
            });
        }
        native_cells.sort_by(|left, right| {
            left.occurrences
                .first()
                .cmp(&right.occurrences.first())
                .then_with(|| left.address.cmp(&right.address))
        });

        let mut codec_faces = self
            .faces
            .into_iter()
            .enumerate()
            .map(|(temp_at, face)| NativeBoundaryFace {
                key: face.key,
                surface_variants: face.variants.into_iter().collect(),
                native_face: temp_to_native[temp_at],
            })
            .collect::<Vec<_>>();
        codec_faces.sort_by(|left, right| {
            left.key
                .cmp(&right.key)
                .then_with(|| left.native_face.cmp(&right.native_face))
        });
        let codec = NativeRelationalCodec {
            schema: CODEC_SCHEMA.to_owned(),
            faces: codec_faces,
        };
        let potential = NativeRelationalPotentialComplex {
            schema: POTENTIAL_SCHEMA.to_owned(),
            factor_addresses: self.factor_addresses,
            factor_adjacency: self.factor_adjacency.into_iter().collect(),
            faces: native_faces,
            cells: native_cells,
            obstructed_delivery_population: self.obstructed_delivery_population,
        };
        codec.validate(&potential)?;
        potential.validate()?;
        let retained_face_occurrence_population =
            potential.faces.iter().try_fold(0u64, |total, face| {
                face.occurrences
                    .iter()
                    .try_fold(total, |subtotal, occurrence| {
                        subtotal
                            .checked_add(occurrence.occurrence_population)
                            .ok_or(NativeCirculationError::Standing)
                    })
            })?;
        let retained_cell_occurrence_population =
            potential.cells.iter().try_fold(0u64, |total, cell| {
                cell.occurrences
                    .iter()
                    .try_fold(total, |subtotal, occurrence| {
                        subtotal
                            .checked_add(occurrence.occurrence_population)
                            .ok_or(NativeCirculationError::Standing)
                    })
            })?;
        let receipt = NativeRelationalConditionReceipt {
            delivered_occurrence_population: self.delivery_order,
            relational_clause_population: self.clause_population,
            obstructed_delivery_population: self.obstructed_delivery_population,
            native_face_population: potential.faces.len(),
            native_cell_population: potential.cells.len(),
            factor_world_line_join_population: potential.factor_adjacency.len(),
            descended_face_section_population: potential
                .faces
                .iter()
                .map(|face| face.occurrences.len())
                .sum(),
            descended_cell_section_population: potential
                .cells
                .iter()
                .map(|cell| cell.occurrences.len())
                .sum(),
            retained_face_occurrence_population,
            retained_cell_occurrence_population,
            source_clause_ledger_retained: false,
            triangular_boundary_defect_population: 0,
        };
        Ok((codec, potential, receipt))
    }
}

impl NativeRelationalPotentialComplex {
    /// The addressed dialogue participant port itself.  A copular cell is a carried relation, not
    /// an identity proof: transitively closing `entity -> be -> participant` would turn unrelated
    /// existential or predicative subjects into the participant everywhere that merged face
    /// recurs.  Exterior names and richer aliases therefore remain receiver charts rather than
    /// native participant classes.
    pub fn addressed_participant_subject_faces(
        &self,
    ) -> Result<BTreeSet<u32>, NativeCirculationError> {
        let faces = self
            .faces
            .iter()
            .enumerate()
            .filter_map(|(at, face)| {
                (face.kind == NativeRelationalFaceKind::Participant)
                    .then(|| u32::try_from(at).ok())
                    .flatten()
            })
            .collect::<BTreeSet<_>>();
        if faces.is_empty() {
            return Err(NativeCirculationError::Correspondence(
                "the cultivated ecology has no addressed participant port".to_owned(),
            ));
        }
        Ok(faces)
    }

    pub fn validate(&self) -> Result<(), NativeCirculationError> {
        if self.schema != POTENTIAL_SCHEMA
            || self.factor_addresses.is_empty()
            || self.faces.is_empty()
            || self.cells.is_empty()
            || self.factor_addresses.iter().any(String::is_empty)
            || self.factor_addresses.iter().collect::<BTreeSet<_>>().len()
                != self.factor_addresses.len()
        {
            return Err(NativeCirculationError::Standing);
        }
        let mut prior_join = None;
        for join in &self.factor_adjacency {
            if join.0 >= join.1
                || join.1 as usize >= self.factor_addresses.len()
                || prior_join.is_some_and(|prior| prior >= *join)
            {
                return Err(NativeCirculationError::Standing);
            }
            prior_join = Some(*join);
        }
        let mut face_addresses = BTreeMap::<
            &str,
            (
                &NativeRelationalFaceKind,
                u64,
                u64,
                &[NativeRelationalFaceOccurrence],
            ),
        >::new();
        for face in &self.faces {
            if face.occurrences.is_empty()
                || face.occurrences.iter().any(|section| {
                    section.occurrence_population == 0
                        || !is_digest(&section.source_occurrence_identity_sha256)
                        || section.first_delivery_order > section.last_delivery_order
                })
                || face.occurrences.windows(2).any(|pair| pair[0] >= pair[1])
                || face.factor_support != occurrence_factor_support(&face.occurrences)
                || face
                    .factor_support
                    .iter()
                    .any(|factor| *factor as usize >= self.factor_addresses.len())
                || face.address
                    != digest(&(
                        FACE_ADDRESS_DOMAIN,
                        &(
                            face.kind,
                            face.founding_delivery_order,
                            face.founding_clause_order,
                            &face.occurrences,
                        ),
                    ))?
            {
                return Err(NativeCirculationError::Standing);
            }
            if let Some((kind, founding_delivery, founding_clause, occurrences)) = face_addresses
                .insert(
                    &face.address,
                    (
                        &face.kind,
                        face.founding_delivery_order,
                        face.founding_clause_order,
                        face.occurrences.as_slice(),
                    ),
                )
            {
                if kind != &face.kind
                    || founding_delivery != face.founding_delivery_order
                    || founding_clause != face.founding_clause_order
                    || occurrences != face.occurrences.as_slice()
                {
                    return Err(NativeCirculationError::Standing);
                }
            }
        }
        let mut cell_addresses = BTreeSet::new();
        for cell in &self.cells {
            let key = NativeCellKey {
                subject: cell.subject,
                relation: cell.relation,
                modality: cell.modality,
                object: cell.object,
                copular: cell.copular,
            };
            if cell.occurrences.is_empty()
                || cell.occurrences.iter().any(|section| {
                    section.occurrence_population == 0
                        || !is_digest(&section.source_occurrence_identity_sha256)
                        || section.first_delivery_order > section.last_delivery_order
                })
                || cell.occurrences.windows(2).any(|pair| pair[0] >= pair[1])
                || [cell.subject, cell.relation, cell.object]
                    .iter()
                    .any(|face| *face as usize >= self.faces.len())
                || cell
                    .modality
                    .is_some_and(|face| face as usize >= self.faces.len())
                || cell.factor_support != cell_factor_support(&cell.occurrences)
                || cell.address != digest(&(CELL_ADDRESS_DOMAIN, &key, &cell.occurrences))?
                || !cell_addresses.insert(&cell.address)
            {
                return Err(NativeCirculationError::Standing);
            }
            let subject_kind = self.faces[cell.subject as usize].kind;
            let object_kind = self.faces[cell.object as usize].kind;
            if !matches!(
                subject_kind,
                NativeRelationalFaceKind::Entity | NativeRelationalFaceKind::Participant
            ) || self.faces[cell.relation as usize].kind != NativeRelationalFaceKind::Relation
                || !matches!(
                    object_kind,
                    NativeRelationalFaceKind::Entity | NativeRelationalFaceKind::Participant
                )
                || cell.modality.is_some_and(|face| {
                    self.faces[face as usize].kind != NativeRelationalFaceKind::Modality
                })
            {
                return Err(NativeCirculationError::Standing);
            }
        }
        Ok(())
    }

    pub(super) fn participant_closure(
        &self,
        seeds: &BTreeSet<u32>,
    ) -> Result<(BTreeSet<u32>, Option<(u32, u32)>), NativeCirculationError> {
        let mut closure = seeds.clone();
        let mut alias = None;
        for cell in &self.cells {
            if !cell.copular {
                continue;
            }
            let subject_kind = self
                .faces
                .get(cell.subject as usize)
                .ok_or(NativeCirculationError::Standing)?
                .kind;
            let object_kind = self
                .faces
                .get(cell.object as usize)
                .ok_or(NativeCirculationError::Standing)?
                .kind;
            if seeds.contains(&cell.subject) && object_kind == NativeRelationalFaceKind::Participant
            {
                closure.insert(cell.object);
                alias.get_or_insert((cell.object, cell.subject));
            } else if seeds.contains(&cell.object)
                && matches!(
                    subject_kind,
                    NativeRelationalFaceKind::Entity | NativeRelationalFaceKind::Participant
                )
            {
                closure.insert(cell.subject);
                alias.get_or_insert((cell.object, cell.subject));
            }
        }
        Ok((closure, alias))
    }

    pub fn canonical_bytes(&self) -> Result<Vec<u8>, NativeCirculationError> {
        self.validate()?;
        serde_json::to_vec(self).map_err(|error| NativeCirculationError::Wire(error.to_string()))
    }

    /// Number of independent addressed world-lines met by one factor support. Adjacency is the
    /// exact continuation relation founded during cultivation; disconnected factors are not
    /// treated as independent merely because their indices differ.
    pub fn world_line_component_population(
        &self,
        factors: &[u32],
    ) -> Result<usize, NativeCirculationError> {
        if factors.is_empty()
            || factors
                .iter()
                .any(|factor| *factor as usize >= self.factor_addresses.len())
        {
            return Err(NativeCirculationError::Standing);
        }
        let mut parent = (0..self.factor_addresses.len()).collect::<Vec<_>>();
        for (left, right) in &self.factor_adjacency {
            union_roots(&mut parent, *left as usize, *right as usize);
        }
        Ok(factors
            .iter()
            .map(|factor| find_root(&mut parent, *factor as usize))
            .collect::<BTreeSet<_>>()
            .len())
    }

    pub fn read(bytes: &[u8]) -> Result<Self, NativeCirculationError> {
        let potential: Self = serde_json::from_slice(bytes)
            .map_err(|error| NativeCirculationError::Wire(error.to_string()))?;
        potential.validate()?;
        Ok(potential)
    }
}

impl NativeRelationalCell {
    pub fn last_delivery_order(&self) -> Option<u64> {
        self.occurrences
            .iter()
            .map(|section| section.last_delivery_order)
            .max()
    }

    pub fn occurrence_population(&self) -> Result<u64, NativeCirculationError> {
        self.occurrences.iter().try_fold(0u64, |sum, section| {
            sum.checked_add(section.occurrence_population)
                .ok_or(NativeCirculationError::Standing)
        })
    }
}

impl NativeRelationalCodec {
    pub fn validate(
        &self,
        potential: &NativeRelationalPotentialComplex,
    ) -> Result<(), NativeCirculationError> {
        if self.schema != CODEC_SCHEMA || self.faces.is_empty() {
            return Err(NativeCirculationError::Standing);
        }
        let mut keys = BTreeSet::new();
        for face in &self.faces {
            if face.key.identity.is_empty()
                || face.surface_variants.is_empty()
                || face.surface_variants.iter().any(Vec::is_empty)
                || face.native_face as usize >= potential.faces.len()
                || potential.faces[face.native_face as usize].kind != face.key.kind
                || !keys.insert(&face.key)
            {
                return Err(NativeCirculationError::Standing);
            }
        }
        Ok(())
    }

    pub fn canonical_bytes(
        &self,
        potential: &NativeRelationalPotentialComplex,
    ) -> Result<Vec<u8>, NativeCirculationError> {
        self.validate(potential)?;
        serde_json::to_vec(self).map_err(|error| NativeCirculationError::Wire(error.to_string()))
    }

    pub fn read(
        bytes: &[u8],
        potential: &NativeRelationalPotentialComplex,
    ) -> Result<Self, NativeCirculationError> {
        let codec: Self = serde_json::from_slice(bytes)
            .map_err(|error| NativeCirculationError::Wire(error.to_string()))?;
        codec.validate(potential)?;
        Ok(codec)
    }

    pub fn contact(
        &self,
        potential: &NativeRelationalPotentialComplex,
        question: &str,
    ) -> Result<NativeRelationalContact, NativeCirculationError> {
        let frontier = relational_deliberation_frontier(question);
        let mut required_regions = frontier
            .required_regions
            .into_iter()
            .map(|region| region.into_iter().collect::<Vec<_>>())
            .collect::<Vec<_>>();
        required_regions.sort();
        required_regions.dedup();
        let mut faces = BTreeSet::new();
        for region in &required_regions {
            for face in &self.faces {
                let direct = face.key.kind == NativeRelationalFaceKind::Entity
                    && face.key.identity == *region;
                let participant_surface = face.key.kind == NativeRelationalFaceKind::Participant
                    && face.surface_variants.iter().any(|surface| {
                        surface
                            .iter()
                            .map(|word| word.to_lowercase())
                            .collect::<BTreeSet<_>>()
                            == region.iter().cloned().collect::<BTreeSet<_>>()
                    });
                if direct || participant_surface {
                    faces.insert(face.native_face);
                }
            }
        }
        if faces.is_empty() {
            return Err(NativeCirculationError::Correspondence(
                "the ordinary receiver regions have no returned native face".to_owned(),
            ));
        }
        let (faces, participant_alias) = potential.participant_closure(&faces)?;
        let mut factor_support = BTreeSet::new();
        for face in &faces {
            factor_support.extend(
                potential
                    .faces
                    .get(*face as usize)
                    .ok_or(NativeCirculationError::Standing)?
                    .factor_support
                    .iter()
                    .copied(),
            );
        }
        if factor_support.is_empty() {
            return Err(NativeCirculationError::Standing);
        }
        Ok(NativeRelationalContact {
            required_regions,
            faces: faces.into_iter().collect(),
            factor_support: factor_support.into_iter().collect(),
            participant_alias,
        })
    }

    /// Freeze every exterior entity chart which is joined by a witnessed copular cell to an
    /// addressed participant port. The exterior region remains a receiver coordinate; the pair
    /// records which participant face must be rendered through which witnessed alias after native
    /// radiation has already returned.
    pub(super) fn participant_alias_charts(
        &self,
        potential: &NativeRelationalPotentialComplex,
        participants: &BTreeSet<u32>,
    ) -> Result<Vec<(Vec<String>, (u32, u32))>, NativeCirculationError> {
        let mut aliases = BTreeSet::new();
        for cell in &potential.cells {
            if !cell.copular {
                continue;
            }
            let subject_kind = potential
                .faces
                .get(cell.subject as usize)
                .ok_or(NativeCirculationError::Standing)?
                .kind;
            let object_kind = potential
                .faces
                .get(cell.object as usize)
                .ok_or(NativeCirculationError::Standing)?
                .kind;
            let alias = if participants.contains(&cell.subject)
                && object_kind == NativeRelationalFaceKind::Entity
            {
                Some((cell.subject, cell.object))
            } else if participants.contains(&cell.object)
                && subject_kind == NativeRelationalFaceKind::Entity
            {
                Some((cell.object, cell.subject))
            } else {
                None
            };
            let Some(alias) = alias else { continue };
            for face in self.faces.iter().filter(|face| {
                face.native_face == alias.1 && face.key.kind == NativeRelationalFaceKind::Entity
            }) {
                aliases.insert((face.key.identity.clone(), alias));
            }
        }
        if aliases.is_empty() {
            return Err(NativeCirculationError::Correspondence(
                "the participant port has no exterior alias chart".to_owned(),
            ));
        }
        Ok(aliases.into_iter().collect())
    }

    /// Return every witnessed exterior relation face and its native occurrence address. This is
    /// a cold chart atlas: later contact may transport current through a matching face, but the
    /// surface never becomes a native factor or morphology key.
    pub(super) fn relation_face_charts(&self) -> Vec<(Vec<String>, u32)> {
        self.faces
            .iter()
            .filter(|face| face.key.kind == NativeRelationalFaceKind::Relation)
            .map(|face| (face.key.identity.clone(), face.native_face))
            .collect()
    }

    pub fn surface_for(
        &self,
        face: u32,
        expected: NativeRelationalFaceKind,
    ) -> Result<Vec<String>, NativeCirculationError> {
        let entries = self
            .faces
            .iter()
            .filter(|entry| entry.native_face == face && entry.key.kind == expected)
            .collect::<Vec<_>>();
        if entries.is_empty() {
            return Err(NativeCirculationError::Standing);
        }
        if matches!(
            expected,
            NativeRelationalFaceKind::Entity | NativeRelationalFaceKind::Participant
        ) {
            // Possessive case and punctuation are exterior presentation, while word order is a
            // real surface coordinate. Preserve the shortest witnessed ordering and remove only
            // the possessive mark which the oriented `owns` relation already carries. This does
            // not alter or select the native face, whose equality is its causal signature.
            let mut surface = entries
                .iter()
                .flat_map(|entry| entry.surface_variants.iter())
                .min_by(|left, right| left.len().cmp(&right.len()).then_with(|| left.cmp(right)))
                .cloned()
                .ok_or(NativeCirculationError::Standing)?;
            for word in &mut surface {
                if let Some(stem) = word
                    .strip_suffix("'s")
                    .or_else(|| word.strip_suffix("’s"))
                    .or_else(|| word.strip_suffix("'S"))
                {
                    *word = stem.to_owned();
                }
                if word.len() > 1
                    && word
                        .chars()
                        .all(|character| !character.is_alphabetic() || character.is_uppercase())
                    && word.to_lowercase() == entries[0].key.identity.join(" ")
                {
                    let mut characters = word.to_lowercase().chars().collect::<Vec<_>>();
                    if let Some(first) = characters.first_mut() {
                        first.make_ascii_uppercase();
                    }
                    *word = characters.into_iter().collect();
                }
            }
            return Ok(surface);
        }
        entries
            .into_iter()
            .flat_map(|entry| entry.surface_variants.iter())
            .min()
            .cloned()
            .ok_or(NativeCirculationError::Standing)
    }

    pub fn clause(
        &self,
        potential: &NativeRelationalPotentialComplex,
        cell: &NativeRelationalCell,
        participant_alias: Option<(u32, u32)>,
    ) -> Result<RelationalClause, NativeCirculationError> {
        if cell.subject as usize >= potential.faces.len()
            || cell.object as usize >= potential.faces.len()
        {
            return Err(NativeCirculationError::Standing);
        }
        let surface = |face: u32| {
            if let Some((participant, alias)) = participant_alias {
                if face == participant {
                    return self.surface_for(alias, NativeRelationalFaceKind::Entity);
                }
            }
            self.surface_for(face, potential.faces[face as usize].kind)
        };
        let subject = surface(cell.subject)?;
        let relation = self.surface_for(cell.relation, NativeRelationalFaceKind::Relation)?;
        let object = surface(cell.object)?;
        let modality = cell
            .modality
            .map(|face| self.surface_for(face, NativeRelationalFaceKind::Modality))
            .transpose()?
            .map(|surface| surface.join(" "));
        let relation = relation.join(" ");
        let entity = |surface: Vec<String>| RelationalEntity {
            identity: surface.iter().map(|word| word.to_lowercase()).collect(),
            surface,
        };
        Ok(RelationalClause {
            identity: cell.address.clone(),
            passage: potential.schema.clone(),
            source: "native-relational-potential".to_owned(),
            receiver: 0,
            source_order: cell
                .occurrences
                .first()
                .map_or(0, |occurrence| u128::from(occurrence.first_delivery_order)),
            source_order_declared: true,
            source_local_step: 0,
            subject: entity(subject),
            relation: relation.clone(),
            modality,
            object: entity(object),
            witnessed_voice: if cell.copular {
                RelationalClauseVoice::Copular
            } else {
                RelationalClauseVoice::Active
            },
            witnessed_surface: String::new(),
        })
    }
}

fn situated_entity_key(entity: &RelationalEntity, phase: NativeDeliveryPhase) -> BoundaryFaceKey {
    let identity = entity
        .identity
        .iter()
        .map(String::as_str)
        .collect::<BTreeSet<_>>();
    let first_person = ["i", "me", "my", "mine", "we", "us", "our", "ours"]
        .into_iter()
        .collect::<BTreeSet<_>>();
    let second_person = ["you", "your", "yours"]
        .into_iter()
        .collect::<BTreeSet<_>>();
    let addressed_participant = !identity.is_empty()
        && (identity == BTreeSet::from(["user"])
            || (matches!(
                phase,
                NativeDeliveryPhase::Ingress | NativeDeliveryPhase::Return
            ) && identity.is_subset(&first_person))
            || (phase == NativeDeliveryPhase::Emanation && identity.is_subset(&second_person)));
    BoundaryFaceKey {
        kind: if addressed_participant {
            NativeRelationalFaceKind::Participant
        } else {
            NativeRelationalFaceKind::Entity
        },
        identity: if addressed_participant {
            vec!["addressed-dialogue-participant".to_owned()]
        } else {
            entity.identity.iter().cloned().collect()
        },
    }
}

fn aggregate_face_occurrences(
    occurrences: &[TempFaceOccurrence],
) -> Result<Vec<NativeRelationalFaceOccurrence>, NativeCirculationError> {
    let mut sections =
        BTreeMap::<(u32, NativeDeliveryPhase, NativeRelationalRole, String), (u64, u64, u64)>::new(
        );
    for occurrence in occurrences {
        let section = sections
            .entry((
                occurrence.factor,
                occurrence.phase,
                occurrence.role,
                occurrence.source_occurrence_identity_sha256.clone(),
            ))
            .or_insert((occurrence.delivery_order, occurrence.delivery_order, 0));
        section.0 = section.0.min(occurrence.delivery_order);
        section.1 = section.1.max(occurrence.delivery_order);
        section.2 = section
            .2
            .checked_add(1)
            .ok_or(NativeCirculationError::Standing)?;
    }
    Ok(sections
        .into_iter()
        .map(
            |(
                (factor, phase, role, source_occurrence_identity_sha256),
                (first_delivery_order, last_delivery_order, occurrence_population),
            )| {
                NativeRelationalFaceOccurrence {
                    factor,
                    phase,
                    role,
                    source_occurrence_identity_sha256,
                    first_delivery_order,
                    last_delivery_order,
                    occurrence_population,
                }
            },
        )
        .collect())
}

fn aggregate_cell_occurrences(
    occurrences: &[TempCellOccurrence],
) -> Result<Vec<NativeRelationalCellOccurrence>, NativeCirculationError> {
    let mut sections = BTreeMap::<(u32, NativeDeliveryPhase, String), (u64, u64, u64)>::new();
    for occurrence in occurrences {
        let section = sections
            .entry((
                occurrence.factor,
                occurrence.phase,
                occurrence.source_occurrence_identity_sha256.clone(),
            ))
            .or_insert((occurrence.delivery_order, occurrence.delivery_order, 0));
        section.0 = section.0.min(occurrence.delivery_order);
        section.1 = section.1.max(occurrence.delivery_order);
        section.2 = section
            .2
            .checked_add(1)
            .ok_or(NativeCirculationError::Standing)?;
    }
    Ok(sections
        .into_iter()
        .map(
            |(
                (factor, phase, source_occurrence_identity_sha256),
                (first_delivery_order, last_delivery_order, occurrence_population),
            )| {
                NativeRelationalCellOccurrence {
                    factor,
                    phase,
                    source_occurrence_identity_sha256,
                    first_delivery_order,
                    last_delivery_order,
                    occurrence_population,
                }
            },
        )
        .collect())
}

fn occurrence_factor_support(occurrences: &[NativeRelationalFaceOccurrence]) -> Vec<u32> {
    occurrences
        .iter()
        .map(|occurrence| occurrence.factor)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn cell_factor_support(occurrences: &[NativeRelationalCellOccurrence]) -> Vec<u32> {
    occurrences
        .iter()
        .map(|occurrence| occurrence.factor)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

fn find_root(parent: &mut [usize], mut at: usize) -> usize {
    while parent[at] != at {
        parent[at] = parent[parent[at]];
        at = parent[at];
    }
    at
}

fn union_roots(parent: &mut [usize], left: usize, right: usize) {
    let left = find_root(parent, left);
    let right = find_root(parent, right);
    if left != right {
        let (lower, higher) = (left.min(right), left.max(right));
        parent[higher] = lower;
    }
}

fn digest(value: &impl Serialize) -> Result<String, NativeCirculationError> {
    let bytes = serde_json::to_vec(value)
        .map_err(|error| NativeCirculationError::Wire(error.to_string()))?;
    Ok(render_hex(&Sha256::digest(bytes)))
}

use holonic_engine::is_sha256_digest as is_digest;

fn render_hex(value: &[u8]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    let mut out = String::with_capacity(value.len() * 2);
    for octet in value {
        out.push(HEX[(octet >> 4) as usize] as char);
        out.push(HEX[(octet & 15) as usize] as char);
    }
    out
}

#[cfg(test)]
#[path = "native_relational_potential_tests.rs"]
mod tests;
