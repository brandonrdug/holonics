//! Source-port preparation through the contemporary receiving relation (Refs #73 #62).
//!
//! [agent-inferred] On the declared exact linear domain, y(u)=y(0)+L u and
//! L=R P_receiver A I_source B. The existing producing Word's matched return reads
//! L; the existing exact preimage owner returns the whole affine control fibre.
//! A requested receiving carrier is distinct from the later world observation.
//! Only a singleton fibre releases a control. No class chooser, minimum-norm
//! representative, effort/wave identification or selection-policy derivative is supplied.

use std::sync::Arc;

use num_traits::Zero;

use super::{EndChange, FieldBalance, PowerForm, Word, WordBalance};
use crate::hnn::HnnError;
use crate::hnn::constitution::Constitution;
use crate::hnn::field::{Current, Field, FieldMaterial};
use crate::hnn::moment::SourceMoment;
use crate::hnn::propagation::Operands;
use crate::hnn::receiving::ReceivingPhases;
use crate::ratio::Rat;
use crate::ratio::linear::ExactRatMatrix;

/// A fixed declared wave preparation at one existing source-storage port.
/// Every u in Q^(B.columns) is in this declaration's admitted control domain;
/// a constrained actuator needs a separate domain/restriction certificate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PortPreparation {
    field: Field,
    ring: usize,
    map: ExactRatMatrix,
}

impl PortPreparation {
    pub fn new(field: &Field, ring: usize, map: ExactRatMatrix) -> Result<Self, HnnError> {
        let declared = field.rings().get(ring).ok_or(HnnError::RingOutside {
            ring,
            rings: field.rings().len(),
        })?;
        if !field.is_source(ring) {
            return Err(HnnError::Unadmitted {
                reason: "a preparation acts at an actually declared source wave port",
            });
        }
        if map.rows() != declared.width() {
            return Err(HnnError::Shape {
                what: "the preparation map's source wave rows",
                expected: declared.width(),
                found: map.rows(),
            });
        }
        Ok(Self {
            field: field.clone(),
            ring,
            map,
        })
    }

    pub fn ring(&self) -> usize {
        self.ring
    }
    pub fn map(&self) -> &ExactRatMatrix {
        &self.map
    }
    pub fn controls(&self) -> usize {
        self.map.columns()
    }
}

/// The entire preimage, or a covector proving the requested residual unreachable.
/// `particular` is a coordinate origin of the fibre, never a selected action.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ControlFibre {
    Affine {
        particular: Vec<Rat>,
        kernel: Vec<Vec<Rat>>,
    },
    Obstructed {
        covector: Vec<Rat>,
        pairing: Rat,
    },
}

impl ControlFibre {
    pub fn unique_control(&self) -> Option<&[Rat]> {
        match self {
            Self::Affine { particular, kernel } if kernel.is_empty() => Some(particular),
            _ => None,
        }
    }
}

/// Source-private producing operands and full opening; transient, never resident history.
#[derive(Clone, Debug, PartialEq, Eq)]
struct ActionProducer {
    field: Field,
    constitution: Constitution,
    current: Current,
    source: Arc<SourceMoment>,
    support: Vec<usize>,
    operands: Operands,
    opening: EndChange,
    opened_at: usize,
}

impl ActionProducer {
    fn of(word: &Word<'_>) -> Result<Self, HnnError> {
        if word.ticks() != 0 || word.is_ended() {
            return Err(HnnError::Unadmitted {
                reason: "a prospective preparation starts at the actual unrun source opening",
            });
        }
        let (constitution, current, source, support) =
            word.native_source.as_ref().ok_or(HnnError::Unadmitted {
                reason: "a prospective preparation requires its native source producer",
            })?;
        if word.operands().lattice().is_some()
            || word.operands().rings().iter().any(|r| r.chart().is_some())
            || word
                .operands()
                .contacts()
                .iter()
                .any(|c| c.chart().is_some())
            || word
                .operands()
                .resonators()
                .iter()
                .flatten()
                .any(|r| r.material().saturation().is_some() || !r.charts().is_empty())
        {
            return Err(HnnError::Unadmitted {
                reason: "an affine control fibre requires the exact unsplit quadratic Word",
            });
        }
        Ok(Self {
            field: word.field.clone(),
            constitution: constitution.clone(),
            current: current.clone(),
            source: source.clone(),
            support: support.clone(),
            operands: word.operands.clone(),
            opening: word.change()?,
            opened_at: word.opened_at(),
        })
    }

    fn matches(&self, word: &Word<'_>) -> bool {
        word.field == &self.field
            && word.operands == self.operands
            && word.opened_at == self.opened_at
            && word
                .native_source
                .as_ref()
                .is_some_and(|(theta, current, source, support)| {
                    theta == &self.constitution
                        && current == &self.current
                        && Arc::ptr_eq(source, &self.source)
                        && support == &self.support
                })
    }
}

/// Prospective relation at the current material/frame/clock, including its full control fibre.
/// Baseline/request are realified receiving carriers, before any probability/grain quotient.
#[derive(Debug)]
pub struct ProspectiveControl {
    producer: ActionProducer,
    preparation: PortPreparation,
    phases: ReceivingPhases,
    requested: Vec<Vec<Rat>>,
    compared: Vec<bool>,
    baseline: Vec<Vec<Rat>>,
    /// The executed native inference passage, separate from the later actual controlled Word.
    prediction_word: WordBalance,
    prediction_balances: Vec<FieldBalance>,
    response: ExactRatMatrix,
    residual: Vec<Rat>,
    fibre: ControlFibre,
}

impl ProspectiveControl {
    pub fn fibre(&self) -> &ControlFibre {
        &self.fibre
    }
    pub fn unique_control(&self) -> Option<&[Rat]> {
        self.fibre.unique_control()
    }
    pub fn preparation(&self) -> &PortPreparation {
        &self.preparation
    }
    pub fn phases(&self) -> &ReceivingPhases {
        &self.phases
    }
    pub fn requested(&self) -> &[Vec<Rat>] {
        &self.requested
    }
    pub fn compared(&self) -> &[bool] {
        &self.compared
    }
    pub fn baseline(&self) -> &[Vec<Rat>] {
        &self.baseline
    }
    pub fn prediction_word(&self) -> &WordBalance { &self.prediction_word }
    pub fn prediction_balances(&self) -> &[FieldBalance] { &self.prediction_balances }
    /// Rows are selected stations in order, then each realified receiving coordinate.
    pub fn response(&self) -> &ExactRatMatrix {
        &self.response
    }
    pub fn residual(&self) -> &[Rat] {
        &self.residual
    }
    pub fn current(&self) -> &Current {
        &self.producer.current
    }
    pub fn producing_commit(&self) -> u64 {
        self.producer.constitution.commit()
    }
    pub fn opened_at(&self) -> usize {
        self.producer.opened_at
    }

    /// Execute the singleton preparation at the original full native source opening.
    /// The same applied u is a conditional control, not a derivative of its inference.
    pub fn prepare<'c>(
        self,
        baseline: Word<'c>,
    ) -> Result<(Word<'c>, PortPreparationReceipt, AppliedPortPreparation), HnnError> {
        if !self.producer.matches(&baseline)
            || baseline.ticks() != 0
            || baseline.is_ended()
            || baseline.change()? != self.producer.opening
        {
            return Err(HnnError::Unadmitted {
                reason: "the action consumes its own whole producing source opening",
            });
        }
        let control = self
            .unique_control()
            .ok_or(HnnError::Unadmitted {
                reason: "a plural or obstructed control fibre withholds native action release",
            })?
            .to_vec();
        if self.response.apply(&control)? != self.residual {
            return Err(HnnError::Realization {
                what: "the released control solves its producing relation",
            });
        }
        let added = self.preparation.map.apply(&control)?;
        let ring = self.preparation.ring;
        let mut opening = self.producer.opening.clone();
        let old = opening.storage[ring].clone();
        for (x, delta) in opening.storage[ring].iter_mut().zip(&added) {
            *x += delta;
        }
        let form = PowerForm::read(
            baseline.field,
            &self.producer.constitution,
            &self.producer.current,
        )?;
        let before =
            form.power(&self.producer.opening)? + form.resonator_power(&self.producer.opening)?;
        let after = form.power(&opening)? + form.resonator_power(&opening)?;
        let quadratic = form.ring_power(ring, &added);
        let cross = form.ring_power(ring, &opening.storage[ring])
            - form.ring_power(ring, &old)
            - &quadratic;
        let receipt = PortPreparationReceipt {
            before: before.clone(),
            after: after.clone(),
            work: after - before,
            cross,
            quadratic,
            added,
        };
        if !receipt.closes() {
            return Err(HnnError::Realization {
                what: "the actual source preparation work closes",
            });
        }
        // No encoded answer or synthesized SourceMoment: only the actual wave port changes.
        let mut word = Word::on_change(
            baseline.field,
            baseline.operands.clone(),
            opening.clone(),
            baseline.opened_at,
        )?;
        let mut producer = self.producer;
        producer.opening = opening;
        producer
            .support
            .extend(producer.opening.support(baseline.field));
        producer.support.sort_unstable();
        producer.support.dedup();
        word.native_source = Some((
            producer.constitution.clone(),
            producer.current.clone(),
            producer.source.clone(),
            producer.support.clone(),
        ));
        let applied = AppliedPortPreparation {
            producer,
            preparation: self.preparation,
            phases: self.phases,
            requested: self.requested,
            compared: self.compared,
            baseline: self.baseline,
            response: self.response,
            control,
            injection: receipt.added.clone(),
        };
        Ok((word, receipt, applied))
    }
}

/// Model source preparation work at fixed material/phase. Actual world effort/flow
/// supply and its port work are separate readings of the participating world law.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PortPreparationReceipt {
    pub before: Rat,
    pub after: Rat,
    pub work: Rat,
    pub cross: Rat,
    pub quadratic: Rat,
    pub added: Vec<Rat>,
}

impl PortPreparationReceipt {
    pub fn closes(&self) -> bool {
        &self.after - &self.before == self.work && &self.cross + &self.quadratic == self.work
    }
}

/// Opaque binding of a released native preparation to its actual producer.
/// A comparison/encounter consumer carries this alongside the controlled Word.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AppliedPortPreparation {
    producer: ActionProducer,
    preparation: PortPreparation,
    phases: ReceivingPhases,
    requested: Vec<Vec<Rat>>,
    compared: Vec<bool>,
    baseline: Vec<Vec<Rat>>,
    response: ExactRatMatrix,
    control: Vec<Rat>,
    injection: Vec<Rat>,
}

impl AppliedPortPreparation {
    pub fn preparation(&self) -> &PortPreparation {
        &self.preparation
    }
    pub fn ring(&self) -> usize {
        self.preparation.ring
    }
    pub fn control(&self) -> &[Rat] {
        &self.control
    }
    pub fn injection(&self) -> &[Rat] {
        &self.injection
    }
    pub fn actual_source_wave(&self) -> &[Rat] {
        &self.producer.opening.storage[self.ring()]
    }
    pub fn current(&self) -> &Current {
        &self.producer.current
    }
    pub fn producing_commit(&self) -> u64 {
        self.producer.constitution.commit()
    }
    pub fn phases(&self) -> &ReceivingPhases {
        &self.phases
    }
    pub fn requested(&self) -> &[Vec<Rat>] {
        &self.requested
    }
    pub fn compared(&self) -> &[bool] {
        &self.compared
    }
    pub fn baseline(&self) -> &[Vec<Rat>] {
        &self.baseline
    }
    pub fn response(&self) -> &ExactRatMatrix {
        &self.response
    }
    pub fn opened_at(&self) -> usize {
        self.producer.opened_at
    }

    pub(crate) fn matches_word(&self, word: &Word<'_>) -> bool {
        self.producer.matches(word)
    }

    pub(crate) fn verify_producer(&self, word: &Word<'_>) -> Result<(), HnnError> {
        if !self.matches_word(word) || word.ticks() != self.phases.junction_steps() {
            return Err(HnnError::Unadmitted {
                reason: "the prepared action keeps its actual producing Word and clock",
            });
        }
        Ok(())
    }

    /// Exact model relation checked against the actual executed controlled Word.
    /// This checks no requested-vs-world equality and certifies no world prediction.
    pub fn verify_execution(&self, word: &Word<'_>) -> Result<(), HnnError> {
        self.verify_producer(word)?;
        for ((epoch, target), selected) in self
            .phases
            .epochs()
            .zip(&self.requested)
            .zip(&self.compared)
        {
            if !selected {
                continue;
            }
            let anchor = word
                .anchor(epoch, self.phases.ring())
                .ok_or(HnnError::WordEnded {
                    ticks: word.ticks(),
                })?;
            let read = self.phases.read(
                word.field,
                &self.producer.constitution,
                &self.producer.current,
                anchor,
            )?;
            if &read.logits != target {
                return Err(HnnError::Realization {
                    what: "the actual controlled Word satisfies its inferred receiving relation",
                });
            }
        }
        Ok(())
    }
}

impl Word<'_> {
    /// Read the full control preimage through this source-bound exact native opening.
    /// The request is a receiving carrier constraint; it never becomes an observation.
    pub fn prospective_port_preparation(
        &self,
        phases: &ReceivingPhases,
        preparation: &PortPreparation,
        requested: &[Vec<Rat>],
        compared: &[bool],
    ) -> Result<ProspectiveControl, HnnError> {
        let producer = ActionProducer::of(self)?;
        if self.field != &preparation.field {
            return Err(HnnError::Unadmitted {
                reason: "the preparation belongs to its actually declared field",
            });
        }
        let width = self
            .field
            .alphabet()
            .checked_mul(2)
            .ok_or(HnnError::CountOverflow)?;
        if compared.len() != phases.aperture()
            || requested.len() != phases.aperture()
            || requested.iter().any(|r| r.len() != width)
        {
            return Err(HnnError::Shape {
                what: "the requested carrier and complete receiving partition",
                expected: phases.aperture(),
                found: requested.len(),
            });
        }
        let mut baseline_word = Word::on_change(
            self.field,
            self.operands.clone(),
            producer.opening.clone(),
            self.opened_at,
        )?;
        // Full ticks retain the real end for the later current; anchors are read at their
        // own junctions. Loaded pump phases read opened_at+k exactly as the controlled Word.
        baseline_word.run(phases.junction_steps())?;
        let prediction_word=WordBalance::of(&baseline_word.released()?);
        let prediction_balances=baseline_word.field_balances().to_vec();
        if !prediction_word.closes() || prediction_balances.iter().any(|b| !b.closes()) {
            return Err(HnnError::Unadmitted {
                reason:"the native prospective passage exposes its actual closed work receipts",
            });
        }
        let baseline = phases
            .epochs()
            .map(|epoch| {
                let anchor =
                    baseline_word
                        .anchor(epoch, phases.ring())
                        .ok_or(HnnError::WordEnded {
                            ticks: baseline_word.ticks(),
                        })?;
                Ok(phases
                    .read(
                        self.field,
                        &producer.constitution,
                        &producer.current,
                        anchor,
                    )?
                    .logits)
            })
            .collect::<Result<Vec<_>, HnnError>>()?;
        let map = producer.constitution.receiving_map(phases.ring()).ok_or(
            HnnError::MissingReceivingMap {
                ring: phases.ring(),
            },
        )?;
        let preparation_transpose = preparation.map.transpose()?;
        let mut rows = Vec::new();
        let mut residual = Vec::new();
        for (((epoch, target), base), selected) in
            phases.epochs().zip(requested).zip(&baseline).zip(compared)
        {
            if !selected {
                continue;
            }
            for coordinate in 0..width {
                let receiving_row = (0..map.columns())
                    .map(|j| map.get(coordinate, j).cloned())
                    .collect::<Result<Vec<_>, _>>()?;
                // P is a declared permutation: its transpose is the inverse rotor.
                let anchor_row = self
                    .field
                    .ring(phases.ring())
                    .rotate(&receiving_row, &(-&producer.current.lift()[phases.ring()]));
                let mut anchors = vec![None; baseline_word.ticks()];
                anchors[epoch] = Some(anchor_row);
                let opening_dual = baseline_word.anchor_differential(anchors, phases.ring())?;
                rows.push(preparation_transpose.apply(&opening_dual.storage[preparation.ring])?);
                residual.push(&target[coordinate] - &base[coordinate]);
            }
        }
        let response = ExactRatMatrix::shaped(rows.len(), preparation.controls(), rows)?;
        let fibre = match response.preimage_fibre(&residual)? {
            Some((particular, kernel)) => {
                // Keep both reconstruction clauses with the complete returned fibre.
                if response.apply(&particular)? != residual
                    || kernel.iter().any(|k| {
                        response
                            .apply(k)
                            .map_or(true, |v| v.iter().any(|x| !x.is_zero()))
                    })
                {
                    return Err(HnnError::Realization {
                        what: "the entire prospective control fibre reconstructs",
                    });
                }
                ControlFibre::Affine { particular, kernel }
            }
            None => {
                let covector =
                    response
                        .preimage_obstruction(&residual)?
                        .ok_or(HnnError::Realization {
                            what: "an unreachable control has an actual annihilator obstruction",
                        })?;
                let pairing = covector.iter().zip(&residual).map(|(a, b)| a * b).sum();
                ControlFibre::Obstructed { covector, pairing }
            }
        };
        Ok(ProspectiveControl {
            producer,
            preparation: preparation.clone(),
            phases: phases.clone(),
            requested: requested.to_vec(),
            compared: compared.to_vec(),
            baseline,
            prediction_word,
            prediction_balances,
            response,
            residual,
            fibre,
        })
    }
}
