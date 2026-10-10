//! Source-port preparation through the contemporary receiving relation (Refs #73 #62).
//!
//! [agent-inferred] On the declared exact linear domain, y(u)=y(0)+L u and
//! L=R P_receiver A I_source B. The existing producing Word's matched return reads
//! L; the existing exact preimage owner returns the whole affine control fibre.
//! A requested receiving carrier is distinct from the later world observation.
//! Only a singleton fibre releases a control. No class chooser, minimum-norm
//! representative, effort/wave identification or selection-policy derivative is supplied.
//!
//! [definition; agent-inferred, October 8] **The native feature read of an informative probe.**
//! The receiving read of one station multiplies a single vector, the feature
//! `x = P_receiver^lift · anchor` (`ReceivingPhases::read`: logits `f = R x`, class phases
//! `φ_c = Im f_c / 2`). On the same exact linear domain `x(u) = x0 + J u`, where `x0` is the
//! baseline passage's feature at the compared station and row `j` of `J` is the matched reverse law
//! of the unit covector `e_j` in the place of the receiving row `R_i` that
//! [`Word::prospective_port_preparation`] reverses. [`Word::prospective_feature`] returns `(x0, J)`
//! and nothing else: no request, no residual and no control fibre are formed, because an
//! informative probe is not a request. `y(0) + L u` is never installed as a requested carrier or as
//! a target, and a candidate control is a point of a declared finite lattice
//! (`physical::action::AdmittedWaves`), never a sample of a control fibre. The consumer equations,
//! checked by [`ProspectiveFeature::agrees_with`] and by `tests/physical_ask.rs` against an
//! independent forward perturbation: at the one compared station `R J` is the response that
//! [`Word::prospective_port_preparation`] forms row by row, `R x0` is its baseline reading, and
//! `x(u)` is the feature an independently executed forward Word reads after the injection `B u`.
//! [definition] The feature is the NATIVE passage's. The actual World's reflected return replaces
//! the source storage after every full tick, which this baseline does not model, so `x(u)` predicts
//! the native readout only and the executed feature may differ from it.
//!
//! [definition; agent-inferred, October 8] **The model preparation work of a candidate.** The
//! existing owner of the storage power is [`PowerForm::ring_power`], `P(s) = (h/4) Y |s|²` at the
//! preparation's ring. For the opening's source wave `m` the work of the control `u` is
//! `W(u) = P(m + B u) − P(m) = h Y (m · B u) / 2 + h Y |B u|² / 4`
//! ([`ProspectiveFeature::preparation_work`]), the same quantity
//! [`PortPreparationReceipt::work`] reports when `u` is applied. No second formula is kept: the
//! bound of the admitted lattice is derived from `P` at a unit wave.
//!
//! [definition; agent-inferred, October 8] **Recorded failures checked**
//! ([lessons](../../../../../research/records/2026-09-29_LESSONS_THE_FAILURES_THAT_REPEATED_AFTER_THEY_WERE_RECORDED.md)).
//! Lesson 5 (no authored routine): this owner selects nothing; the probe's choice belongs to the
//! retained family and the release law (`physical::action`). Lesson 4 (no tape): no occurrence,
//! old Word or response column is retained. A requested carrier stays distinct from a probe: the
//! applied preparation of a probe carries an empty `requested`, and
//! [`AppliedPortPreparation::verify_execution`] refuses it rather than verifying nothing.
//!
//! [open] The Lean counterpart of the affine feature read (`R J` = the response, `x(u)` against a
//! forward perturbation) is owed (#62); `tests/physical_ask.rs` checks it exactly on the declared
//! fixtures.

use std::sync::Arc;

use num_traits::{One, Zero};

use super::{EndChange, FieldBalance, PowerForm, Word, WordBalance};
use crate::hnn::HnnError;
use crate::hnn::constitution::Constitution;
use crate::hnn::field::{Current, Field, FieldMaterial};
use crate::hnn::moment::SourceMoment;
use crate::hnn::propagation::Operands;
use crate::hnn::receiving::ReceivingPhases;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::{Rat, integer};

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
        // The shared tail: the same physical application serves a probe's admitted control.
        let (word, receipt, producer) =
            apply_control(self.producer, &self.preparation, &baseline, &control)?;
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

impl ProspectiveControl {
    /// **The controlled Word this control would open**, read without consuming either (the World
    /// model's coupled prospect, C1b-2a): the unique control applied at the producing opening by the
    /// same checks and the same shared tail as [`ProspectiveControl::prepare`]. The baseline stays
    /// unrun; a plural or obstructed fibre is refused.
    pub fn controlled_word<'c>(&self, baseline: &Word<'c>) -> Result<Word<'c>, HnnError> {
        if !self.producer.matches(baseline)
            || baseline.ticks() != 0
            || baseline.is_ended()
            || baseline.change()? != self.producer.opening
        {
            return Err(HnnError::Unadmitted {
                reason: "the action consumes its own whole producing source opening",
            });
        }
        let control = self.unique_control().ok_or(HnnError::Unadmitted {
            reason: "a plural or obstructed control fibre withholds native action release",
        })?;
        if self.response.apply(control)? != self.residual {
            return Err(HnnError::Realization {
                what: "the released control solves its producing relation",
            });
        }
        let (word, _, _) =
            apply_control(self.producer.clone(), &self.preparation, baseline, control)?;
        Ok(word)
    }
}

/// [definition; agent-inferred, October 8] **One admitted control applied at the whole producing
/// opening**: the tail that `ProspectiveControl::prepare` (a request's unique preimage) and
/// `ProspectiveFeature::prepare_control` (a probe's lattice point) share, moved out of `prepare`
/// with its checks and their order unchanged. Only the actual wave port changes: the added wave
/// `B u` enters the opening's source storage, the model preparation work is read from the one
/// power form at the opening's own material, current and pump phase and must close, and the
/// controlled Word opens on that change with the producer's source binding. No encoded answer and
/// no synthesized `SourceMoment` is made. Returns the controlled Word, the receipt and the producer
/// with its opening and support advanced to the controlled change.
fn apply_control<'c>(
    mut producer: ActionProducer,
    preparation: &PortPreparation,
    baseline: &Word<'c>,
    control: &[Rat],
) -> Result<(Word<'c>, PortPreparationReceipt, ActionProducer), HnnError> {
    let added = preparation.map.apply(control)?;
    let ring = preparation.ring;
    let mut opening = producer.opening.clone();
    let old = opening.storage[ring].clone();
    for (x, delta) in opening.storage[ring].iter_mut().zip(&added) {
        *x += delta;
    }
    let form = PowerForm::read(baseline.field, &producer.constitution, &producer.current)?;
    let before = form.power(&producer.opening)? + form.resonator_power(&producer.opening)?;
    let after = form.power(&opening)? + form.resonator_power(&opening)?;
    let quadratic = form.ring_power(ring, &added);
    let cross =
        form.ring_power(ring, &opening.storage[ring]) - form.ring_power(ring, &old) - &quadratic;
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
    Ok((word, receipt, producer))
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
    /// One requested carrier per station of the aperture; EMPTY for a probe's applied
    /// preparation, which has no requested consequence (a probe is not a request).
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
        // A probe's applied preparation (`ProspectiveFeature::prepare_control`) carries no
        // requested consequence: verifying it would compare nothing and pass. A request's
        // always carries one carrier per station of its aperture.
        if self.requested.len() != self.phases.aperture() {
            return Err(HnnError::Unadmitted {
                reason: "a probe's applied preparation carries no requested consequence to verify",
            });
        }
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

/// [definition; agent-inferred, October 8] **The native feature read at one compared station**
/// (module header): the baseline feature `x0`, its Jacobian `J` in the declared controls, and the
/// operands that produced them. Nothing is requested and nothing is selected: `x(u) = x0 + J u` is
/// the NATIVE passage's feature after the declared wave `B u`, a prediction of the readout and not
/// of the actual World's reflected return. Source-private, like [`ProspectiveControl`]: it keeps
/// the producing operands and is transient, never resident history.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProspectiveFeature {
    producer: ActionProducer,
    preparation: PortPreparation,
    phases: ReceivingPhases,
    compared: Vec<bool>,
    /// The one compared station, an index into the receiving aperture.
    station: usize,
    /// The word tick (junction step) at which that station reads the passage.
    crossing: usize,
    /// `x0 = P_receiver^lift · anchor`, one entry per coordinate of the receiving ring.
    baseline_feature: Vec<Rat>,
    /// `J`, the receiving ring's width by the preparation's controls.
    jacobian: ExactRatMatrix,
    /// The baseline receiving reading at every station of the aperture, as
    /// [`ProspectiveControl::baseline`] holds it.
    baseline: Vec<Vec<Rat>>,
    /// `R J`: the receiving map's rows at the compared station applied to `J`.
    response: ExactRatMatrix,
    /// The one power form of the opening's own material, current and pump phase.
    form: PowerForm,
    prediction_word: WordBalance,
    prediction_balances: Vec<FieldBalance>,
}

impl ProspectiveFeature {
    /// The one compared station, an index into the receiving aperture.
    pub fn station(&self) -> usize {
        self.station
    }
    /// The word tick (junction step) at which the compared station reads the passage.
    pub fn crossing(&self) -> usize {
        self.crossing
    }
    /// The absolute pump clock of that crossing, `opened_at + crossing`.
    pub fn tick(&self) -> usize {
        self.producer.opened_at + self.crossing
    }
    /// `x0`, the baseline passage's feature at the compared station.
    pub fn baseline_feature(&self) -> &[Rat] {
        &self.baseline_feature
    }
    /// `J`: `x(u) = x0 + J u` on the declared exact linear domain.
    pub fn jacobian(&self) -> &ExactRatMatrix {
        &self.jacobian
    }
    /// The baseline receiving logits at the compared station, `R x0`.
    pub fn baseline_logits(&self) -> &[Rat] {
        &self.baseline[self.station]
    }
    /// The baseline receiving logits at every station of the aperture.
    pub fn baseline(&self) -> &[Vec<Rat>] {
        &self.baseline
    }
    /// `R J` at the compared station: the rows are its realified receiving coordinates.
    pub fn response(&self) -> &ExactRatMatrix {
        &self.response
    }
    pub fn phases(&self) -> &ReceivingPhases {
        &self.phases
    }
    pub fn preparation(&self) -> &PortPreparation {
        &self.preparation
    }
    pub fn compared(&self) -> &[bool] {
        &self.compared
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
    pub fn prediction_word(&self) -> &WordBalance {
        &self.prediction_word
    }
    pub fn prediction_balances(&self) -> &[FieldBalance] {
        &self.prediction_balances
    }
    /// `m`, the opening's current source storage wave at the preparation's ring.
    pub fn source_wave(&self) -> &[Rat] {
        &self.producer.opening.storage[self.preparation.ring]
    }

    /// The existing owner's storage power at the preparation's ring, `P(s) = (h/4) Y |s|²`
    /// ([`PowerForm::ring_power`]), under the opening's own material, current and pump phase.
    pub fn storage_power(&self, wave: &[Rat]) -> Rat {
        self.form.ring_power(self.preparation.ring, wave)
    }

    /// **The model preparation work of the control `u`**: `W(u) = P(m + B u) − P(m)`, with `P` the
    /// owner's [`Self::storage_power`] and `m` the opening's [`Self::source_wave`]; that is
    /// `h Y (m · B u) / 2 + h Y |B u|² / 4`. It is the `work` of the [`PortPreparationReceipt`]
    /// that applying `u` returns. Actual world-port work is a separate supply.
    pub fn preparation_work(&self, control: &[Rat]) -> Result<Rat, HnnError> {
        let added = self.preparation.map.apply(control)?;
        let old = self.source_wave();
        let wave: Vec<Rat> = old.iter().zip(&added).map(|(m, delta)| m + delta).collect();
        Ok(self.storage_power(&wave) - self.storage_power(old))
    }

    /// `x(u) = x0 + J u`: the native feature at the compared station after the declared wave.
    pub fn feature_at(&self, control: &[Rat]) -> Result<Vec<Rat>, HnnError> {
        let moved = self.jacobian.apply(control)?;
        Ok(self
            .baseline_feature
            .iter()
            .zip(&moved)
            .map(|(x, delta)| x + delta)
            .collect())
    }

    /// **The consumer equations against the request path.** For a [`ProspectiveControl`] that reads
    /// the same producing opening, phases, preparation and compared station, `R x0` is its
    /// baseline reading at that station and `R J` is its response, row by row. `false` when the
    /// two do not read the same opening (so nothing is compared); an error is a refusal of the
    /// receiving map, not a disagreement.
    pub fn agrees_with(&self, control: &ProspectiveControl) -> Result<bool, HnnError> {
        if control.compared() != self.compared.as_slice()
            || control.phases() != &self.phases
            || control.preparation() != &self.preparation
            || control.producing_commit() != self.producing_commit()
            || control.opened_at() != self.opened_at()
            || control.current() != self.current()
        {
            return Ok(false);
        }
        let map = self
            .producer
            .constitution
            .receiving_map(self.phases.ring())
            .ok_or(HnnError::MissingReceivingMap {
                ring: self.phases.ring(),
            })?;
        let reads = control.baseline().get(self.station) == Some(&map.apply(&self.baseline_feature)?);
        let rows = &map.multiply(&self.jacobian)? == control.response();
        Ok(reads && rows)
    }

    /// Apply one admitted control of the declared domain at the original full native source
    /// opening: the probe's counterpart of [`ProspectiveControl::prepare`], with its producer,
    /// opening and shape checks and the one shared physical application ([`apply_control`]), and
    /// without any fibre or request. The applied preparation carries an empty `requested`.
    pub(crate) fn prepare_control<'c>(
        self,
        baseline: Word<'c>,
        control: &[Rat],
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
        if control.len() != self.preparation.controls() {
            return Err(HnnError::Shape {
                what: "the admitted source wave control",
                expected: self.preparation.controls(),
                found: control.len(),
            });
        }
        let (word, receipt, producer) =
            apply_control(self.producer, &self.preparation, &baseline, control)?;
        let applied = AppliedPortPreparation {
            producer,
            preparation: self.preparation,
            phases: self.phases,
            requested: Vec::new(),
            compared: self.compared,
            baseline: self.baseline,
            response: self.response,
            control: control.to_vec(),
            injection: receipt.added.clone(),
        };
        Ok((word, receipt, applied))
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

impl Word<'_> {
    /// **Read the native feature of the one compared station through this source-bound exact
    /// native opening** (module header): `x0` and `J` with `x(u) = x0 + J u` on the preparation's
    /// declared controls. It mirrors [`Word::prospective_port_preparation`] up to the reverse
    /// sweeps: the same producer check, field check, baseline Word run and closed-balance check, and
    /// exactly one compared station. Row `j` of `J` replaces the receiving row `R_i` by the unit
    /// covector `e_j` in the same loop (rotate by `−lift`, the anchor differential at the
    /// station's epoch, the opening dual at the preparation's ring, the preparation transpose).
    /// No request is read, so no target, residual or fibre exists here; the opening and the Word
    /// are left unrun and unchanged.
    pub fn prospective_feature(
        &self,
        phases: &ReceivingPhases,
        preparation: &PortPreparation,
        compared: &[bool],
    ) -> Result<ProspectiveFeature, HnnError> {
        let producer = ActionProducer::of(self)?;
        if self.field != &preparation.field {
            return Err(HnnError::Unadmitted {
                reason: "the preparation belongs to its actually declared field",
            });
        }
        if compared.len() != phases.aperture() {
            return Err(HnnError::Shape {
                what: "the complete receiving partition",
                expected: phases.aperture(),
                found: compared.len(),
            });
        }
        let selected: Vec<usize> = compared
            .iter()
            .enumerate()
            .filter(|(_, chosen)| **chosen)
            .map(|(station, _)| station)
            .collect();
        let [station] = selected[..] else {
            return Err(HnnError::Unadmitted {
                reason: "a native feature read compares exactly one declared receiving station",
            });
        };
        let mut baseline_word = Word::on_change(
            self.field,
            self.operands.clone(),
            producer.opening.clone(),
            self.opened_at,
        )?;
        // Full ticks retain the real end for the later current; anchors are read at their
        // own junctions. Loaded pump phases read opened_at+k exactly as the controlled Word.
        baseline_word.run(phases.junction_steps())?;
        let prediction_word = WordBalance::of(&baseline_word.released()?);
        let prediction_balances = baseline_word.field_balances().to_vec();
        if !prediction_word.closes() || prediction_balances.iter().any(|b| !b.closes()) {
            return Err(HnnError::Unadmitted {
                reason: "the native prospective passage exposes its actual closed work receipts",
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
        let crossing = phases.epochs().nth(station).ok_or(HnnError::Shape {
            what: "the compared station inside the receiving aperture",
            expected: phases.aperture(),
            found: station,
        })?;
        let anchor = baseline_word
            .anchor(crossing, phases.ring())
            .ok_or(HnnError::WordEnded {
                ticks: baseline_word.ticks(),
            })?;
        let ring = self.field.ring(phases.ring());
        let lift = &producer.current.lift()[phases.ring()];
        // x0 is what the receiving read multiplies: `ReceivingPhases::read` forms logits as R x0.
        let baseline_feature = ring.rotate(anchor, lift);
        if map.apply(&baseline_feature)? != baseline[station] {
            return Err(HnnError::Realization {
                what: "the native feature reproduces the baseline receiving reading",
            });
        }
        let width = baseline_feature.len();
        let preparation_transpose = preparation.map.transpose()?;
        let mut rows = Vec::with_capacity(width);
        for coordinate in 0..width {
            let mut unit = vec![Rat::zero(); width];
            unit[coordinate] = Rat::one();
            // P is a declared permutation: its transpose is the inverse rotor.
            let anchor_row = ring.rotate(&unit, &(-lift));
            let mut anchors = vec![None; baseline_word.ticks()];
            anchors[crossing] = Some(anchor_row);
            let opening_dual = baseline_word.anchor_differential(anchors, phases.ring())?;
            rows.push(preparation_transpose.apply(&opening_dual.storage[preparation.ring])?);
        }
        let jacobian = ExactRatMatrix::shaped(width, preparation.controls(), rows)?;
        let response = map.multiply(&jacobian)?;
        let form = PowerForm::read(self.field, &producer.constitution, &producer.current)?;
        Ok(ProspectiveFeature {
            producer,
            preparation: preparation.clone(),
            phases: phases.clone(),
            compared: compared.to_vec(),
            station,
            crossing,
            baseline_feature,
            jacobian,
            baseline,
            response,
            form,
            prediction_word,
            prediction_balances,
        })
    }
}

/// [definition; agent-inferred, October 9] **A coupled prospective passage** (the World model's
/// C1b-2a, `physical::action::model`): the native Word's exact passage from its actual unrun opening
/// when every source wave it emits is answered by a declared return law instead of the actual World.
/// Per junction step the emitted wave `a_t` and the returned wave `b_t`; at every compared station the
/// native feature in the receiving frame, formed exactly as [`Word::prospective_feature`] forms it
/// (`ring.rotate(anchor, lift)`), with its receiving logits. It is the native readout, not the World's
/// observed face. Transient: it keeps no producer and is never resident history.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoupledPassage {
    /// `(a_t, b_t)` for every junction step `t = 1..=ticks`, in order.
    pub waves: Vec<(Vec<Rat>, Vec<Rat>)>,
    /// `(station, feature, logits)` for every compared station, in station order.
    pub features: Vec<(usize, Vec<Rat>, Vec<Rat>)>,
    /// The passage's released work, closed.
    pub word: WordBalance,
    /// The native carry at the passage's end, which the next encounter of a schedule opens on.
    pub end: crate::hnn::word::ReceptionCarry,
}

/// The declared return law of a coupled passage ([`Word::prospective_coupled_passage`]): the returned
/// wave for each step's emitted one, `(t, a_t) ↦ b_t`.
pub type WaveReturns<'a> = dyn FnMut(usize, &[Rat]) -> Result<Vec<Rat>, HnnError> + 'a;

/// [definition; agent-inferred, October 10; the held-carry record §7b] A reader beside a coupled
/// passage: it sees the Word after step `t`'s return and before the next tick, exactly where a
/// consumer beside an actual encounter sees it, and cannot change the Word.
pub type PassageObserver<'a> = dyn FnMut(&Word<'_>, usize) -> Result<(), HnnError> + 'a;

impl<'f> Word<'f> {
    /// **Run the coupled prospective passage** ([`CoupledPassage`]): a fresh Word on this unrun
    /// Word's actual source opening, opened exactly as [`Word::prospective_feature`] opens its
    /// baseline, ticked through the receiving phases' junction steps. After each tick the source
    /// ring's emitted wave `a_t` is answered by `returns(t, a_t)` through the existing
    /// `Word::return_source_wave`, with the exterior work `−h Y_s (|b|² − |a|²)/4` that closes
    /// native power. This Word stays unrun and unchanged, and no actual World is read or written.
    /// The passage's own Word is returned beside it, keeping this Word's source binding, so the
    /// observed receiving return can consume it (the held-carry record §7h).
    pub fn prospective_coupled_passage(
        &self,
        source_ring: usize,
        phases: &ReceivingPhases,
        compared: &[bool],
        returns: &mut WaveReturns<'_>,
        observer: &mut PassageObserver<'_>,
    ) -> Result<(CoupledPassage, Word<'f>), HnnError> {
        let producer = ActionProducer::of(self)?;
        if compared.len() != phases.aperture() {
            return Err(HnnError::Shape {
                what: "the complete receiving partition",
                expected: phases.aperture(),
                found: compared.len(),
            });
        }
        let mut word = Word::on_change(
            self.field,
            self.operands.clone(),
            producer.opening.clone(),
            self.opened_at,
        )?;
        // The passage is this Word's own, re-run: it keeps this Word's source binding, so the observed
        // receiving return can consume it as it consumes an executed Word.
        word.native_source = self.native_source.clone();
        word.opened_on = self.opened_on.clone();
        word.admit_source_boundary(source_ring)?;
        let admittance = self.field.ring(source_ring).admittance().clone();
        let squares = |wave: &[Rat]| wave.iter().map(|x| x * x).sum::<Rat>();
        let mut waves = Vec::with_capacity(phases.junction_steps());
        for t in 1..=phases.junction_steps() {
            word.tick()?;
            let incident = word.source_wave(source_ring)?.to_vec();
            let reflected = returns(t, &incident)?;
            if reflected.len() != incident.len() {
                return Err(HnnError::Shape {
                    what: "a declared returned wave on the source ring",
                    expected: incident.len(),
                    found: reflected.len(),
                });
            }
            let work = self.field.step() * &admittance * (squares(&reflected) - squares(&incident))
                / integer(4);
            let native_tick = word
                .opened_at()
                .checked_add(t)
                .ok_or(HnnError::CountOverflow)?;
            word.return_source_wave(source_ring, native_tick, &incident, &reflected, &-work)?;
            observer(&word, t)?;
            waves.push((incident, reflected));
        }
        let prediction = WordBalance::of(&word.released()?);
        if !prediction.closes() || word.field_balances().iter().any(|b| !b.closes()) {
            return Err(HnnError::Unadmitted {
                reason: "the coupled prospective passage exposes its actual closed work receipts",
            });
        }
        let map = producer.constitution.receiving_map(phases.ring()).ok_or(
            HnnError::MissingReceivingMap {
                ring: phases.ring(),
            },
        )?;
        let ring = self.field.ring(phases.ring());
        let lift = &producer.current.lift()[phases.ring()];
        let mut features = Vec::new();
        for (station, crossing) in phases.epochs().enumerate() {
            if !compared[station] {
                continue;
            }
            let anchor = word
                .anchor(crossing, phases.ring())
                .ok_or(HnnError::WordEnded {
                    ticks: word.ticks(),
                })?;
            let feature = ring.rotate(anchor, lift);
            let logits = map.apply(&feature)?;
            features.push((station, feature, logits));
        }
        let end = word.reception_end()?;
        Ok((
            CoupledPassage {
                waves,
                features,
                word: prediction,
                end,
            },
            word,
        ))
    }
}
