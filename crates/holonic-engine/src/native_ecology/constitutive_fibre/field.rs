//! Coupled constitutive circulation on a complete port field. This extends the existing local
//! rational relation and lossless two-port law; it does not define a text encoder or a second
//! learner. Each junction receives its own exterior excitation. The source section retains BOTH
//! outgoing and held branches, and an actual later receiving field joins the same resident relation.
//!
//! This field chart has fixed nodes and unit-phase incidences. Live fixed-node recharting
//! and physical incoming-incidence replacement retain their distinct frame/history semantics;
//! root-carrier enlargement, contextual parent contacts and a learned text-codec product remain
//! outside it.
//! The paired-junction constructor additionally makes a formed Hermitian contact moment and
//! retained internal current operative on the root port field, with a complete internal decoder.

use super::circulation::HeldCurrentFrame;
use super::*;
use crate::dimensional_wave::ExactComplexWaveCurrent;
use std::rc::Rc;

mod junction;
mod rechart;
pub use junction::{NativeFieldInternalCurrent, NativeFieldJunctionReading};
use junction::{PairedJunction, PendingJunction};

/// One actual emitted source from this live body. It is linear; the caller cannot manufacture
/// it from an occurrence number or duplicate it for another receiving edge.
#[derive(Debug)]
pub struct NativeFieldEmission {
    owner: Rc<()>,
    occurrence: usize,
}

#[derive(Debug)]
pub struct NativeFieldOccurrence {
    incoming: Vec<NativePhaseCurrent>,
    source: Option<NativeFieldEmission>,
}

impl NativeFieldOccurrence {
    pub fn entering(incoming: Vec<NativePhaseCurrent>) -> Self {
        Self {
            incoming,
            source: None,
        }
    }
    pub fn through(source: NativeFieldEmission, incoming: Vec<NativePhaseCurrent>) -> Self {
        Self {
            incoming,
            source: Some(source),
        }
    }
    pub fn take_source(&mut self) -> Option<NativeFieldEmission> {
        self.source.take()
    }
    pub fn incoming(&self) -> &[NativePhaseCurrent] {
        &self.incoming
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeFieldLineage {
    pub occurrence: usize,
    /// Producing chart in this body's frame chronology, never a contextual identity.
    pub frame: u64,
    pub predecessor_state: Option<usize>,
    pub received_from: Option<usize>,
    /// Complete exterior excitation field, not a semantic feature vector or a fitted source.
    pub incoming: Vec<NativePhaseCurrent>,
}

#[derive(Debug, PartialEq, Eq, Serialize)]
pub struct NativeFieldReceivedDifference<Reading = ConstitutiveReading> {
    pub source_occurrence: usize,
    pub former_receiver: Reading,
    pub arrived: Vec<ExactComplexWaveCurrent>,
}

#[derive(Debug)]
pub struct NativeFieldStep<Reading = ConstitutiveReading> {
    pub source: NativeFieldEmission,
    pub lineage: NativeFieldLineage,
    /// The immutable local frame in which this occurrence produced its source branches.
    pub frame: Rc<NativeCurrentFrame>,
    pub outgoing: Vec<ExactComplexWaveCurrent>,
    pub held_successor: Vec<ExactComplexWaveCurrent>,
    pub receiver: Reading,
    pub received_difference: Option<NativeFieldReceivedDifference<Reading>>,
    pub formed_pivot: Option<usize>,
    pub successor_rank: usize,
    pub junction: Option<NativeFieldJunctionReading>,
}

/// Explicit classification projection. It contains no selected response or alleged full fibre;
/// all source/relation carriers remain owned by the continuing body.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum NativeFieldReceiverStatus {
    Unique,
    OutsideDomain,
    Plural,
}

struct HeldField<'chart> {
    section: ResidentSection<'chart>,
    lineage: NativeFieldLineage,
    frame: Rc<HeldCurrentFrame<'chart>>,
    returned: bool,
    junction: Option<Rc<ResidentSection<'chart>>>,
}

/// One move owner for phase standing, the same local relation accumulator, and its actual
/// emitted sources. The wider source chart is 4N real coordinates (two complex branches/node);
/// the receiving chart is the complete 2N real coordinates of the next exterior input field.
pub struct NativeConstitutiveField<'chart> {
    seed: ResidentSection<'chart>,
    memory: ResidentSection<'chart>,
    relation: ResidentConstitutiveFibre<'chart>,
    material: Vec<NativeJunctionSeed>,
    frame: Rc<HeldCurrentFrame<'chart>>,
    recharts: Vec<NativeRechartReceipt>,
    incidence_changes: Vec<NativeIncidenceChange>,
    owner: Rc<()>,
    history: Vec<HeldField<'chart>>,
    pending: Option<HeldField<'chart>>,
    junction: Option<PairedJunction<'chart>>,
    pending_junction: Option<PendingJunction<'chart>>,
}

impl<'chart> NativeConstitutiveField<'chart> {
    pub fn found(
        surface: &'chart ResidentSurface<'chart>,
        material: Vec<NativeJunctionSeed>,
    ) -> Result<Self, ConstitutiveFibreError> {
        let nodes = material.len();
        let source_width = nodes.checked_mul(4).ok_or(ConstitutiveFibreError::Shape)?;
        let target_width = nodes.checked_mul(2).ok_or(ConstitutiveFibreError::Shape)?;
        let scratch = nodes
            .checked_mul(24)
            .and_then(|v| v.checked_mul(16))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let available = surface.declaration().max_sectiond_bytes;
        if nodes == 0 {
            return Err(ConstitutiveFibreError::Shape);
        }
        if scratch > available as usize {
            return Err(ConstitutiveFibreError::ScratchAperture {
                required: scratch,
                available,
            });
        }
        for node in &material {
            node.validate()?;
        }
        let relation = ResidentConstitutiveFibre::found(surface, source_width, target_width)?;
        let mut seed_words = Vec::new();
        let mut memory_words = Vec::new();
        for node in &material {
            let turn = node.incoming_transport.words();
            seed_words.extend([
                node.incoming_admittance,
                node.held_admittance,
                turn[0],
                turn[1],
                turn[2],
            ]);
            memory_words.extend(node.initial_held.words());
        }
        let mount = |width, words: Vec<i64>| -> Result<_, ConstitutiveFibreError> {
            let rest = ResidentSectionRest::found(
                nodes,
                width,
                ResidentGrain(0),
                64,
                words.into_iter().map(|v| (v, v)).collect(),
            )
            .map_err(|_| ConstitutiveFibreError::Shape)?;
            Ok(surface.mount_section_rest(&rest)?)
        };
        let frame_native = mount(3, (0..nodes).flat_map(|_| [1, 0, 1]).collect())?;
        let frame = Rc::new(HeldCurrentFrame {
            native: frame_native,
            view: Rc::new(NativeCurrentFrame {
                ordinal: 0,
                root_to_local: vec![NativePhaseCurrent::unit(); nodes],
            }),
        });
        Ok(Self {
            seed: mount(5, seed_words)?,
            memory: mount(3, memory_words)?,
            relation,
            material,
            frame,
            recharts: Vec::new(),
            incidence_changes: Vec::new(),
            owner: Rc::new(()),
            history: Vec::new(),
            pending: None,
            junction: None,
            pending_junction: None,
        })
    }

    pub fn nodes(&self) -> usize {
        self.material.len()
    }
    pub fn material(&self) -> &[NativeJunctionSeed] {
        &self.material
    }
    pub fn occurrence_count(&self) -> usize {
        self.history.len()
    }
    pub fn census(&self) -> TransferCensus {
        self.relation.census()
    }
    pub fn pending_lineage(&self) -> Option<&NativeFieldLineage> {
        self.pending.as_ref().map(|p| &p.lineage)
    }
    pub fn current_frame(&self) -> &NativeCurrentFrame {
        &self.frame.view
    }
    pub fn recharts(&self) -> &[NativeRechartReceipt] {
        &self.recharts
    }
    pub fn incidence_changes(&self) -> &[NativeIncidenceChange] {
        &self.incidence_changes
    }
    pub fn lineage(&self, occurrence: usize) -> Option<&NativeFieldLineage> {
        self.history.get(occurrence).map(|p| &p.lineage)
    }
    /// The immutable producing chart for an inspected historical section; no receiving handle
    /// is issued by observing it.
    pub fn source_frame(&self, occurrence: usize) -> Option<&NativeCurrentFrame> {
        self.history.get(occurrence).map(|p| p.frame.view.as_ref())
    }
    pub fn inspect_relation(&self) -> Result<ResidentSectionRest, ConstitutiveFibreError> {
        self.relation.inspect_relation()
    }
    pub fn inspect_held(&self) -> Result<ResidentSectionRest, ConstitutiveFibreError> {
        Ok(self.relation.surface.detach_section(&self.memory, 64)?)
    }
    /// Explicit historical source inspection; it issues no new receiving capability.
    pub fn inspect_source(
        &self,
        occurrence: usize,
    ) -> Result<ResidentSectionRest, ConstitutiveFibreError> {
        let source = self
            .history
            .get(occurrence)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        Ok(self.relation.surface.detach_section(&source.section, 64)?)
    }

    pub fn advance(
        &mut self,
        occurrence: &mut NativeFieldOccurrence,
    ) -> Result<NativeFieldStep, ConstitutiveFibreError> {
        self.advance_reading(occurrence, |relation, words, at, exclude| {
            relation.decode_reading(words, at, exclude)
        })
    }

    /// Read only the native receiver classification. In particular, this does not copy the
    /// resident paired basis to the host when the fibre is plural. Formation and successor
    /// conduct are identical to `advance`; the projection is only an exterior observation.
    pub fn advance_status(
        &mut self,
        occurrence: &mut NativeFieldOccurrence,
    ) -> Result<NativeFieldStep<NativeFieldReceiverStatus>, ConstitutiveFibreError> {
        self.advance_reading(occurrence, |relation, words, at, _exclude| {
            let width = relation.source_width + relation.target_width;
            if words[at + width].0 <= 0 {
                return Err(ConstitutiveFibreError::Uncertain);
            }
            match words[at + width + 1].0 {
                0 => Ok(NativeFieldReceiverStatus::Unique),
                1 => Ok(NativeFieldReceiverStatus::OutsideDomain),
                2 => Ok(NativeFieldReceiverStatus::Plural),
                _ => Err(ConstitutiveFibreError::Uncertain),
            }
        })
    }

    fn advance_reading<Reading>(
        &mut self,
        occurrence: &mut NativeFieldOccurrence,
        read: impl Fn(
            &ResidentConstitutiveFibre<'chart>,
            &[(i64, i64)],
            usize,
            Option<usize>,
        ) -> Result<Reading, ConstitutiveFibreError>,
    ) -> Result<NativeFieldStep<Reading>, ConstitutiveFibreError> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        if occurrence.incoming.len() != self.nodes() {
            return Err(ConstitutiveFibreError::Shape);
        }
        let source_at = if let Some(source) = &occurrence.source {
            if !Rc::ptr_eq(&source.owner, &self.owner)
                || self
                    .history
                    .get(source.occurrence)
                    .is_none_or(|h| h.returned)
            {
                return Err(ConstitutiveFibreError::ForeignOccurrence);
            }
            Some(source.occurrence)
        } else {
            None
        };
        let next = self
            .relation
            .occurrences
            .checked_add(1)
            .ok_or(ConstitutiveFibreError::Shape)?;
        self.history
            .try_reserve(1)
            .map_err(|_| ConstitutiveFibreError::Shape)?;
        let at = self.history.len();
        let lineage = NativeFieldLineage {
            occurrence: at,
            frame: self.frame.view.ordinal,
            predecessor_state: at.checked_sub(1),
            received_from: source_at,
            incoming: occurrence.incoming.clone(),
        };
        let surface = self.relation.surface;
        let input = surface.mount_section_rest(
            &ResidentSectionRest::found(
                self.nodes(),
                3,
                ResidentGrain(0),
                64,
                occurrence
                    .incoming
                    .iter()
                    .flat_map(|p| p.words())
                    .map(|v| (v, v))
                    .collect(),
            )
            .map_err(|_| ConstitutiveFibreError::Shape)?,
        )?;
        let output_width = self
            .nodes()
            .checked_mul(16)
            .and_then(|v| v.checked_add(9))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let output = surface.fresh_section(1, output_width, ResidentGrain(0))?;
        let prepared = self.prepare_junction()?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_constitutive_field(
                &lane,
                &self.seed,
                &mut self.memory,
                &mut self.relation.basis,
                &input,
                source_at.map(|i| &self.history[i].section),
                &self.frame.native,
                source_at.map(|i| &self.history[i].frame.native),
                self.junction
                    .as_ref()
                    .zip(prepared.as_ref())
                    .map(|(old, (next, scratch))| {
                        (
                            &old.covariance,
                            old.current.as_ref(),
                            &next.covariance,
                            next.report.as_ref(),
                            scratch,
                        )
                    }),
                at as u64,
                &output,
            )?;
        }
        passage.close(0, &output, 64)?;
        let passage = passage.finish()?;
        self.pending = Some(HeldField {
            section: output,
            lineage: lineage.clone(),
            frame: Rc::clone(&self.frame),
            returned: false,
            junction: prepared.as_ref().map(|(next, _)| Rc::clone(&next.report)),
        });
        let (pending_junction, junction_scratch) = match prepared {
            Some((next, scratch)) => (Some(next), Some(scratch)),
            None => (None, None),
        };
        self.pending_junction = pending_junction;
        self.relation.usable = false;
        let launched = passage.launch()?;
        drop(junction_scratch);
        if !launched.obstruction.is_empty() {
            self.pending = None;
            self.pending_junction = None;
            self.relation.usable = true;
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "{:?}",
                launched.obstruction
            )));
        }
        let words = surface.read_out(&self.pending.as_ref().expect("pending field").section)?;
        let source_width = self.relation.source_width;
        let width = source_width + self.relation.target_width;
        let current_at = source_width + 1;
        let former_at = current_at + width + 4;
        if words.iter().any(|(l, h)| l != h) || words[source_width].0 <= 0 {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let formed_pivot = match words[current_at + width + 2].0 {
            -1 => None,
            p if p >= 0 && (p as usize) < width => Some(p as usize),
            _ => return Err(ConstitutiveFibreError::Uncertain),
        };
        let rank = usize::try_from(words[current_at + width + 3].0)
            .map_err(|_| ConstitutiveFibreError::Uncertain)?;
        if rank > width {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let receiver = read(&self.relation, &words, current_at, None)?;
        let received_difference = source_at
            .map(|source_occurrence| -> Result<_, ConstitutiveFibreError> {
                Ok(NativeFieldReceivedDifference {
                    source_occurrence,
                    former_receiver: read(&self.relation, &words, former_at, formed_pivot)?,
                    arrived: occurrence.incoming.iter().map(|p| p.current()).collect(),
                })
            })
            .transpose()?;
        let denominator = words[source_width].0;
        let phase = |j: usize| {
            ExactComplexWaveCurrent::new(
                Rat::new(words[j].0.into(), denominator.into()),
                Rat::new(words[j + 1].0.into(), denominator.into()),
            )
        };
        let outgoing = (0..self.nodes()).map(|i| phase(4 * i)).collect();
        let held_successor = (0..self.nodes()).map(|i| phase(4 * i + 2)).collect();
        let junction = self.read_pending_junction()?;
        if let Some(i) = source_at {
            self.history[i].returned = true;
        }
        occurrence.source = None;
        self.history
            .push(self.pending.take().expect("completed field"));
        if let Some(next) = self.pending_junction.take() {
            self.junction = Some(PairedJunction {
                covariance: next.covariance,
                current: next.report,
            });
        }
        self.relation.occurrences = next;
        self.relation.usable = true;
        Ok(NativeFieldStep {
            source: NativeFieldEmission {
                owner: Rc::clone(&self.owner),
                occurrence: at,
            },
            lineage,
            frame: Rc::clone(&self.frame.view),
            outgoing,
            held_successor,
            receiver,
            received_difference,
            formed_pivot,
            successor_rank: rank,
            junction,
        })
    }
}

#[cfg(test)]
mod tests;
