//! Budgeted, input-only attempts of declared source views.
//!
//! An attempt is an actual `ExecutionPort::refine_view`, including its causal carry.
//! It is not a promised information gain. Untried nonzero views are explored first;
//! thereafter normalized input change per last measured Word tick is a declared
//! contextual-novelty policy. History survives material/current changes and retains
//! their provenance; transferred estimates are not same-state counterfactual proofs.
//! Labels never enter selection. The ordinary caller may compare the resulting
//! single pending observation once when its label arrives.

use super::ModeView;
use crate::hnn::constitution::Constitution;
use crate::hnn::moment::SourceMoment;
use crate::hnn::port::{ExecutionPort, Handle, MomentId, PendingId, PortReceipt, ReceiptDetail};
use crate::hnn::ratio::Faces;
use crate::hnn::reference::ExposedResident;
use crate::hnn::word::ReceptionCarry;
use crate::hnn::{Current, Field, HnnError, ReceivingPhases};
use crate::ratio::Rat;
use crate::ratio::work::ExactWork;
use crate::receiver::reception::InteractionReturn;
use num_bigint::BigInt;
use num_traits::{One, Zero};
use std::{sync::Arc, time::Instant};

/// Two explicit finite-work coordinates. Neither is an estimate of RAM or machine instructions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExplorationBudget {
    pub traversals: u64,
    pub receiving_stations: u64,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ViewContext {
    pub commit: u64,
    pub lift: Vec<BigInt>,
    pub receiver: usize,
    pub phases: ReceivingPhases,
    pub carried: Option<ReceptionCarry>,
    /// Exact producer identity, shared by the returned feedback and last-only history.
    pub material: Arc<Constitution>,
}
/// Measured feedback from an actual port invocation, not supplied by the caller.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ViewFeedback {
    pub context: ViewContext,
    pub word_ticks: usize,
    pub reported_work: ExactWork,
    pub reached_logits: Vec<Vec<Rat>>,
    pub selected_source_bits: u64,
    pub reported_peak_bits: u64,
}
/// A bounded summary per declared view, retaining the last actual response and source operand.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ViewHistory {
    pub attempted: u64,
    pub completed: u64,
    pub failed: u64,
    pub last: Option<ViewFeedback>,
    // In the ring's intrinsic phase frame; material changes remain in ViewContext.
    source: Option<Vec<Vec<Rat>>>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ChoiceReason {
    UnmeasuredNonzero,
    ContextualNovelty,
    ZeroInjectionObservation,
}

/// Opt-in wall-time breakdown of the existing proposal calculation. These are host wall times,
/// not hardware instruction counts or estimates of device work.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct ProposalTiming {
    pub resident_read_ns: u128,
    pub source_open_storage_ns: u128,
    pub source_storage_audit_ns: u128,
    pub source_storage_shape: Vec<usize>,
    pub source_storage_entries: u128,
    pub source_storage_nonzero: u128,
    /// Sum of exact numerator and denominator magnitude bits; excludes signs and Vec/BigInt
    /// allocation overhead, so it is a logical rational payload measure rather than RAM.
    pub source_storage_rational_component_bits: u128,
    pub source_storage_max_component_bits: u64,
    pub source_projection_ns: u128,
    pub intrinsic_frame_ns: u128,
    pub novelty_and_norm_ns: u128,
    pub proposal_construction_ns: u128,
    pub menu_views: usize,
}

/// Read-only policy payload audit. These coordinates are not allocated RAM or machine work.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct PolicyStorage {
    pub retained_contexts: usize,
    pub material_logical_bits: u64,
    pub source_and_response_rational_bits: u64,
    /// UTF-8 bytes of the complete phases/carry/lift diagnostic representation. This explicitly
    /// includes private phase metadata; it is neither a stable checkpoint format nor heap size.
    pub contextual_diagnostic_text_bytes: usize,
}

/// Move-only and sealed. Cloning a receipt or reusing a consumed proposal cannot record feedback.
pub struct ModeProposal {
    owner: Arc<()>,
    sequence: u64,
    index: usize,
    view: ModeView,
    constitution: Constitution,
    current: Current,
    moment: SourceMoment,
    carry: Option<ReceptionCarry>,
    moment_id: MomentId,
    phases: ReceivingPhases,
    source: Vec<Vec<Rat>>,
    reason: ChoiceReason,
    novelty: Rat,
    timing: Option<ProposalTiming>,
}
impl std::fmt::Debug for ModeProposal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ModeProposal")
            .field("sequence", &self.sequence)
            .field("index", &self.index)
            .field("view", &self.view)
            .field("commit", &self.constitution.commit())
            .field("reason", &self.reason)
            .field("novelty", &self.novelty)
            .finish()
    }
}
impl ModeProposal {
    pub fn view(&self) -> &ModeView {
        &self.view
    }
    pub fn reason(&self) -> &ChoiceReason {
        &self.reason
    }
    /// Normalized input change divided by the last observed Word tick count.
    pub fn contextual_score(&self) -> &Rat {
        &self.novelty
    }
    pub fn sequence(&self) -> u64 {
        self.sequence
    }
    /// Present only when the caller explicitly selected the profiled proposal path.
    pub fn timing(&self) -> Option<&ProposalTiming> {
        self.timing.as_ref()
    }
}

pub struct ModeTrial {
    pub pending: PendingId,
    pub returned: InteractionReturn<Faces, (), (), Vec<ReceivingPhases>, PortReceipt>,
    pub view_index: usize,
    pub feedback: ViewFeedback,
}

/// Typed checkpoint of the selector only. It does not snapshot a resident or a pending proposal.
/// Disk serialization belongs to the caller's continuing-state owner; this type makes no disk claim.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ExplorationCheckpoint {
    field: Field,
    menu: Vec<ModeView>,
    budget: ExplorationBudget,
    spent: ExplorationBudget,
    sequence: u64,
    history: Vec<ViewHistory>,
}

pub struct ModeExplorer {
    state: ExplorationCheckpoint,
    owner: Arc<()>,
    outstanding: Option<u64>,
}
fn refused(reason: &'static str) -> HnnError {
    HnnError::Unadmitted { reason }
}
fn norm(values: &[Vec<Rat>]) -> Rat {
    values.iter().flatten().map(|x| x * x).sum()
}
fn difference(a: &[Vec<Rat>], b: &[Vec<Rat>]) -> Rat {
    a.iter()
        .zip(b)
        .flat_map(|(a, b)| a.iter().zip(b))
        .map(|(a, b)| {
            let d = a - b;
            &d * &d
        })
        .sum()
}
fn intrinsic(field: &Field, current: &Current, storage: Vec<Vec<Rat>>) -> Vec<Vec<Rat>> {
    storage
        .into_iter()
        .enumerate()
        .map(|(g, v)| field.ring(g).rotate(&v, &(-current.lift()[g].clone())))
        .collect()
}
impl ModeExplorer {
    pub fn new(
        field: &Field,
        menu: Vec<ModeView>,
        budget: ExplorationBudget,
    ) -> Result<Self, HnnError> {
        if menu.is_empty() {
            return Err(refused("mode exploration needs a declared finite menu"));
        }
        for (i, view) in menu.iter().enumerate() {
            view.check(field)?;
            if menu[..i].contains(view) {
                return Err(refused("mode exploration menu entries are distinct"));
            }
        }
        let history = menu
            .iter()
            .map(|_| ViewHistory {
                attempted: 0,
                completed: 0,
                failed: 0,
                last: None,
                source: None,
            })
            .collect();
        Ok(Self {
            state: ExplorationCheckpoint {
                field: field.clone(),
                menu,
                budget,
                spent: ExplorationBudget {
                    traversals: 0,
                    receiving_stations: 0,
                },
                sequence: 0,
                history,
            },
            owner: Arc::new(()),
            outstanding: None,
        })
    }
    pub fn menu(&self) -> &[ModeView] {
        &self.state.menu
    }
    pub fn history(&self) -> &[ViewHistory] {
        &self.state.history
    }
    pub fn spent(&self) -> &ExplorationBudget {
        &self.state.spent
    }
    /// Optional last-only payload audit; exact-equal material identities are counted once.
    /// Formatting is performed only when this diagnostic is explicitly requested.
    pub fn policy_storage(&self) -> PolicyStorage {
        let mut audit = PolicyStorage::default();
        let mut materials: Vec<&Constitution> = Vec::new();
        for history in &self.state.history {
            if let Some(last) = &history.last {
                audit.retained_contexts += 1;
                let material = last.context.material.as_ref();
                if !materials.contains(&material) {
                    materials.push(material);
                    audit.material_logical_bits += material.exact_bits();
                }
                audit.source_and_response_rational_bits += history
                    .source
                    .iter()
                    .flatten()
                    .flatten()
                    .chain(last.reached_logits.iter().flatten())
                    .map(|x| x.numer().bits() + x.denom().bits())
                    .sum::<u64>();
                audit.contextual_diagnostic_text_bytes += format!(
                    "{:?}",
                    (
                        &last.context.phases,
                        &last.context.carried,
                        &last.context.lift
                    )
                )
                .len();
            }
        }
        audit
    }
    pub fn checkpoint(&self) -> Result<ExplorationCheckpoint, HnnError> {
        if self.outstanding.is_some() {
            return Err(refused(
                "an outstanding mode proposal must execute or cancel before checkpoint",
            ));
        }
        Ok(self.state.clone())
    }
    pub fn resume(saved: ExplorationCheckpoint) -> Self {
        Self {
            state: saved,
            owner: Arc::new(()),
            outstanding: None,
        }
    }
    /// Cancellation consumes the exact proposal, charges no traversal and records no invented result.
    pub fn cancel(&mut self, proposal: ModeProposal) -> Result<(), HnnError> {
        self.check_owner(&proposal)?;
        self.outstanding = None;
        Ok(())
    }
    /// Abandon a dropped or misplaced proposal. Any surviving token becomes stale; no feedback
    /// or traversal is recorded because execution has not happened.
    pub fn abandon_outstanding(&mut self, sequence: u64) -> bool {
        if self.outstanding == Some(sequence) {
            self.outstanding = None;
            true
        } else {
            false
        }
    }
    fn check_owner(&self, proposal: &ModeProposal) -> Result<(), HnnError> {
        if !Arc::ptr_eq(&self.owner, &proposal.owner) || self.outstanding != Some(proposal.sequence)
        {
            return Err(refused(
                "a mode proposal belongs to this selector's outstanding attempt",
            ));
        }
        Ok(())
    }
    /// Read only the actual input/material. No label, target, heldout score or future return enters.
    pub fn propose<P: ExecutionPort>(
        &mut self,
        port: &P,
        resident: &P::Resident,
        moment_id: MomentId,
        phases: &ReceivingPhases,
    ) -> Result<Option<ModeProposal>, HnnError>
    where
        P::Resident: ExposedResident,
    {
        self.propose_inner(port, resident, moment_id, phases, false)
    }
    /// Same policy and effects as `propose`, with opt-in wall-time readings for the existing
    /// resident check, source opening, view projection and scoring substeps.
    pub fn propose_profiled<P: ExecutionPort>(
        &mut self,
        port: &P,
        resident: &P::Resident,
        moment_id: MomentId,
        phases: &ReceivingPhases,
    ) -> Result<Option<ModeProposal>, HnnError>
    where
        P::Resident: ExposedResident,
    {
        self.propose_inner(port, resident, moment_id, phases, true)
    }
    fn propose_inner<P: ExecutionPort>(
        &mut self,
        port: &P,
        resident: &P::Resident,
        moment_id: MomentId,
        phases: &ReceivingPhases,
        profile: bool,
    ) -> Result<Option<ModeProposal>, HnnError>
    where
        P::Resident: ExposedResident,
    {
        if self.outstanding.is_some() {
            return Err(refused("one mode proposal is outstanding at a time"));
        }
        let resident_read_started = profile.then(Instant::now);
        if port.read(resident)?.0 != self.state.field {
            return Err(refused("mode exploration uses its declared field"));
        }
        let resident_read_ns =
            resident_read_started.map_or(0, |started| started.elapsed().as_nanos());
        if !resident.admitted().contains(phases) {
            return Err(refused(
                "mode exploration uses the resident's admitted receiving phases",
            ));
        }
        let stations = u64::try_from(phases.aperture()).map_err(|_| HnnError::CountOverflow)?;
        let next_stations = self
            .state
            .spent
            .receiving_stations
            .checked_add(stations)
            .ok_or(HnnError::CountOverflow)?;
        if self.state.spent.traversals >= self.state.budget.traversals
            || next_stations > self.state.budget.receiving_stations
        {
            return Ok(None);
        }
        let moment = resident.moment(&moment_id).ok_or(refused(
            "mode exploration requires the live original source moment",
        ))?;
        let source_open_started = profile.then(Instant::now);
        let storage = moment.open_storage(
            &self.state.field,
            resident.constitution(),
            resident.current(),
        )?;
        let source_open_storage_ns =
            source_open_started.map_or(0, |started| started.elapsed().as_nanos());
        let (
            source_storage_audit_ns,
            source_storage_shape,
            source_storage_entries,
            source_storage_nonzero,
            source_storage_rational_component_bits,
            source_storage_max_component_bits,
        ) = if profile {
            let audit_started = Instant::now();
            let shape = storage.iter().map(Vec::len).collect::<Vec<_>>();
            let entries = storage.iter().map(|source| source.len() as u128).sum();
            let nonzero = storage
                .iter()
                .flatten()
                .filter(|coefficient| !coefficient.is_zero())
                .count() as u128;
            let mut rational_component_bits = 0u128;
            let mut max_component_bits = 0u64;
            for coefficient in storage.iter().flatten() {
                let numerator_bits = coefficient.numer().bits();
                let denominator_bits = coefficient.denom().bits();
                rational_component_bits = rational_component_bits
                    .checked_add(u128::from(numerator_bits))
                    .and_then(|sum| sum.checked_add(u128::from(denominator_bits)))
                    .expect("logical source storage bit count overflowed u128");
                max_component_bits = max_component_bits.max(numerator_bits.max(denominator_bits));
            }
            (
                audit_started.elapsed().as_nanos(),
                shape,
                entries,
                nonzero,
                rational_component_bits,
                max_component_bits,
            )
        } else {
            (0, Vec::new(), 0, 0, 0, 0)
        };
        let mut best: Option<(usize, bool, Rat, Vec<Vec<Rat>>)> = None;
        let mut source_projection_ns = 0u128;
        let mut intrinsic_frame_ns = 0u128;
        let mut novelty_and_norm_ns = 0u128;
        let mut menu_views = 0usize;
        for (i, view) in self.state.menu.iter().enumerate() {
            menu_views += 1;
            let projection_started = profile.then(Instant::now);
            let projected = view.apply(&self.state.field, &storage)?;
            if let Some(started) = projection_started {
                source_projection_ns =
                    source_projection_ns.saturating_add(started.elapsed().as_nanos());
            }
            let intrinsic_started = profile.then(Instant::now);
            let source = intrinsic(&self.state.field, resident.current(), projected);
            if let Some(started) = intrinsic_started {
                intrinsic_frame_ns =
                    intrinsic_frame_ns.saturating_add(started.elapsed().as_nanos());
            }
            let scoring_started = profile.then(Instant::now);
            let energy = norm(&source);
            if energy.is_zero() {
                if let Some(started) = scoring_started {
                    novelty_and_norm_ns =
                        novelty_and_norm_ns.saturating_add(started.elapsed().as_nanos());
                }
                continue;
            }
            let history = &self.state.history[i];
            let unmeasured = history.attempted == 0;
            let novelty = match &history.source {
                Some(old) => difference(&source, old) / (&energy + norm(old)),
                None => Rat::one(),
            };
            // Word ticks are one measured physical-work coordinate, not a sum of incomparable
            // arithmetic widths/operations or a claimed hardware instruction count.
            let ticks = history.last.as_ref().map_or(1, |f| f.word_ticks.max(1));
            let score = novelty / Rat::from_integer(BigInt::from(ticks));
            let better = best.as_ref().is_none_or(|(old, unknown, value, _)| {
                (unmeasured && !unknown)
                    || (unmeasured == *unknown
                        && (score > *value
                            || (score == *value
                                && history.attempted < self.state.history[*old].attempted)))
            });
            if better {
                best = Some((i, unmeasured, score, source));
            }
            if let Some(started) = scoring_started {
                novelty_and_norm_ns =
                    novelty_and_norm_ns.saturating_add(started.elapsed().as_nanos());
            }
        }
        // A zero fresh source does not erase carried motion or prohibit a declared clocked
        // observation. Prefer the declared Whole view when all candidates inject zero; otherwise
        // use the first declared candidate, still with zero source novelty and normal work cost.
        let zero_injection = best.is_none();
        let proposal_construction_started = profile.then(Instant::now);
        let (index, unknown, novelty, source) = best.unwrap_or_else(|| {
            let index = self
                .state
                .menu
                .iter()
                .position(ModeView::is_whole)
                .unwrap_or(0);
            (
                index,
                false,
                Rat::zero(),
                storage.iter().map(|v| vec![Rat::zero(); v.len()]).collect(),
            )
        });
        self.state.sequence = self
            .state
            .sequence
            .checked_add(1)
            .ok_or(HnnError::CountOverflow)?;
        self.outstanding = Some(self.state.sequence);
        Ok(Some(ModeProposal {
            owner: self.owner.clone(),
            sequence: self.state.sequence,
            index,
            view: self.state.menu[index].clone(),
            constitution: resident.constitution().clone(),
            current: resident.current().clone(),
            moment: moment.clone(),
            carry: resident.carried().cloned(),
            moment_id,
            phases: phases.clone(),
            source,
            reason: if zero_injection {
                ChoiceReason::ZeroInjectionObservation
            } else if unknown {
                ChoiceReason::UnmeasuredNonzero
            } else {
                ChoiceReason::ContextualNovelty
            },
            novelty,
            timing: proposal_construction_started.map(|started| ProposalTiming {
                resident_read_ns,
                source_open_storage_ns,
                source_storage_audit_ns,
                source_storage_shape,
                source_storage_entries,
                source_storage_nonzero,
                source_storage_rational_component_bits,
                source_storage_max_component_bits,
                source_projection_ns,
                intrinsic_frame_ns,
                novelty_and_norm_ns,
                proposal_construction_ns: started.elapsed().as_nanos(),
                menu_views,
            }),
        }))
    }
    /// Execute exactly once through the backend and obtain feedback from that actual call.
    /// A backend refusal records a failed attempted traversal conservatively; no success is invented.
    pub fn execute<P: ExecutionPort>(
        &mut self,
        port: &P,
        resident: &mut P::Resident,
        proposal: ModeProposal,
    ) -> Result<ModeTrial, HnnError>
    where
        P::Resident: ExposedResident,
    {
        self.check_owner(&proposal)?;
        self.outstanding = None;
        if resident.constitution() != &proposal.constitution
            || resident.current() != &proposal.current
            || resident.moment(&proposal.moment_id) != Some(&proposal.moment)
            || resident.carried() != proposal.carry.as_ref()
            || !resident.admitted().contains(&proposal.phases)
            || port.read(resident)?.0 != self.state.field
        {
            return Err(refused(
                "a mode proposal's exact producing material, input, lift and carried opening must still match",
            ));
        }
        self.state.spent.traversals += 1;
        self.state.spent.receiving_stations += proposal.phases.aperture() as u64;
        self.state.history[proposal.index].attempted += 1;
        let result = port.refine_view(
            resident,
            &proposal.moment_id,
            &proposal.phases,
            &proposal.view,
        );
        let (pending, returned) = match result {
            Ok(value) => value,
            Err(error) => {
                self.state.history[proposal.index].failed += 1;
                return Err(error);
            }
        };
        self.record_return(port, resident, proposal, pending, returned)
    }
    fn record_return<P: ExecutionPort>(
        &mut self,
        port: &P,
        resident: &mut P::Resident,
        proposal: ModeProposal,
        pending: PendingId,
        returned: InteractionReturn<Faces, (), (), Vec<ReceivingPhases>, PortReceipt>,
    ) -> Result<ModeTrial, HnnError> {
        let measured = (|| {
            let ReceiptDetail::Refine {
                view, peak_bits, ..
            } = &returned.receipt.detail
            else {
                return Err(refused("mode feedback is an actual refinement receipt"));
            };
            if view != &proposal.view {
                return Err(refused(
                    "mode feedback must report the actually selected source view",
                ));
            }
            let faces = returned
                .forward
                .present()
                .ok_or(refused("mode feedback requires its actual reached face"))?;
            Ok(ViewFeedback {
                context: ViewContext {
                    commit: proposal.constitution.commit(),
                    lift: proposal.current.lift().to_vec(),
                    receiver: proposal.phases.ring(),
                    phases: proposal.phases.clone(),
                    carried: proposal.carry.clone(),
                    material: Arc::new(proposal.constitution.clone()),
                },
                word_ticks: returned.receipt.balances.len(),
                reported_work: returned.receipt.work.clone(),
                reached_logits: faces.logits.clone(),
                selected_source_bits: proposal
                    .source
                    .iter()
                    .flatten()
                    .map(|x| x.numer().bits() + x.denom().bits())
                    .sum(),
                reported_peak_bits: *peak_bits,
            })
        })();
        let feedback = match measured {
            Ok(feedback) => feedback,
            Err(error) => {
                self.state.history[proposal.index].failed += 1;
                // Discard the pending handle only. The actual traversal and its carry already
                // occurred and remain charged; cleanup must never pretend to undo that evolution.
                port.discard(resident, Handle::Pending(pending))?;
                return Err(error);
            }
        };
        let history = &mut self.state.history[proposal.index];
        history.completed += 1;
        history.source = Some(proposal.source);
        history.last = Some(feedback.clone());
        Ok(ModeTrial {
            pending,
            returned,
            view_index: proposal.index,
            feedback,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::Reference;
    use crate::hnn::tests::learning::{chain, generic};
    use crate::hnn::tests::support::encoded;
    #[test]
    fn mode_exploration_uses_actual_feedback_and_retains_context_after_deposit() {
        let field = chain();
        let port = Reference::new(4, 1 << 40);
        let mut resident = port
            .mount_with(&field, &Current::at_rest(&field), generic(&field, 31))
            .unwrap();
        let (moment, _) = port
            .ingest(&mut resident, None, &encoded(&field, &[0, 1, 2, 3, 2]))
            .unwrap();
        let phases = resident.admitted()[0].clone();
        let mut explorer = ModeExplorer::new(
            &field,
            vec![
                ModeView::whole(),
                ModeView::primitive(&field, 0, 4).unwrap(),
            ],
            ExplorationBudget {
                traversals: 2,
                receiving_stations: 4,
            },
        )
        .unwrap();
        let before_proposal = crate::hnn::word::work::read();
        let proposal = explorer
            .propose(&port, &resident, moment, &phases)
            .unwrap()
            .unwrap();
        assert_eq!(
            crate::hnn::word::work::read()
                .since(before_proposal)
                .unwrap()
                .words_opened,
            0
        );
        assert_eq!(proposal.reason(), &ChoiceReason::UnmeasuredNonzero);
        assert!(explorer.checkpoint().is_err());
        let before_refine = crate::hnn::word::work::read();
        let first = explorer.execute(&port, &mut resident, proposal).unwrap();
        assert_eq!(
            crate::hnn::word::work::read()
                .since(before_refine)
                .unwrap()
                .words_opened,
            1
        );
        let carried_after_refine = resident.carried().cloned();
        assert_eq!(first.view_index, 0);
        assert!(!first.feedback.reached_logits.is_empty());
        let before_compare = crate::hnn::word::work::read();
        let (staged, _) = port
            .compare(&mut resident, first.pending, &encoded(&field, &[2, 1]))
            .unwrap();
        let compare_work = crate::hnn::word::work::read()
            .since(before_compare)
            .unwrap();
        assert_eq!(compare_work.words_opened, 0);
        assert_eq!(compare_work.returns, 1);
        assert!(
            port.compare(&mut resident, first.pending, &encoded(&field, &[2, 1]))
                .is_err()
        );
        assert_eq!(resident.carried(), carried_after_refine.as_ref());
        port.deposit(&mut resident, staged).unwrap();
        assert_eq!(resident.carried(), carried_after_refine.as_ref());
        let historical_commit = explorer.history()[0].last.as_ref().unwrap().context.commit;
        assert_ne!(historical_commit, resident.constitution().commit());
        port.discard(&mut resident, Handle::Moment(moment)).unwrap();
        let (moment, _) = port
            .ingest(&mut resident, None, &encoded(&field, &[3, 2, 1, 0]))
            .unwrap();
        let mut resumed = ModeExplorer::resume(explorer.checkpoint().unwrap());
        let resumed_choice = resumed
            .propose(&port, &resident, moment, &phases)
            .unwrap()
            .unwrap();
        let second = explorer
            .propose(&port, &resident, moment, &phases)
            .unwrap()
            .unwrap();
        assert_eq!(second.view(), resumed_choice.view());
        assert_eq!(second.contextual_score(), resumed_choice.contextual_score());
        resumed.cancel(resumed_choice).unwrap();
        assert_eq!(second.view(), &ModeView::primitive(&field, 0, 4).unwrap());
        let trial = explorer.execute(&port, &mut resident, second).unwrap();
        port.discard(&mut resident, Handle::Pending(trial.pending))
            .unwrap();
        assert_eq!(explorer.history()[0].completed, 1);
        assert_eq!(
            explorer.history()[0].last.as_ref().unwrap().context.commit,
            historical_commit
        );
        assert_eq!(explorer.history()[1].completed, 1);
        let audit = explorer.policy_storage();
        assert_eq!(audit.retained_contexts, 2);
        assert!(audit.material_logical_bits > 0);
        assert!(audit.contextual_diagnostic_text_bytes > 0);
        assert_eq!(
            explorer.history()[0].last.as_ref().unwrap().context.phases,
            phases
        );
        assert!(
            explorer
                .propose(&port, &resident, moment, &phases)
                .unwrap()
                .is_none()
        );
        let saved = explorer.checkpoint().unwrap();
        let restored = ModeExplorer::resume(saved.clone());
        assert_eq!(restored.checkpoint().unwrap(), saved);
    }
    #[test]
    fn mode_exploration_zero_injection_observes_retained_motion_and_quiescence() {
        let field = chain();
        let port = Reference::new(4, 1 << 40).with_reception(
            crate::hnn::reference::Reception::Carry(crate::hnn::Absorption::Nothing),
        );
        let mut resident = port
            .mount_with(&field, &Current::at_rest(&field), generic(&field, 31))
            .unwrap();
        let phases = resident.admitted()[0].clone();
        let mut explorer = ModeExplorer::new(
            &field,
            vec![
                ModeView::primitive(&field, 0, 4).unwrap(),
                ModeView::whole(),
            ],
            ExplorationBudget {
                traversals: 3,
                receiving_stations: 6,
            },
        )
        .unwrap();
        let empty_source = encoded(&field, &[0]);
        let empty = empty_source.part(0..0).unwrap();
        let (idle, _) = port.ingest(&mut resident, None, &empty).unwrap();
        let proposal = explorer
            .propose(&port, &resident, idle, &phases)
            .unwrap()
            .unwrap();
        assert_eq!(proposal.reason(), &ChoiceReason::ZeroInjectionObservation);
        assert!(proposal.contextual_score().is_zero());
        assert!(proposal.view().is_whole());
        let trial = explorer.execute(&port, &mut resident, proposal).unwrap();
        port.discard(&mut resident, Handle::Pending(trial.pending))
            .unwrap();
        port.discard(&mut resident, Handle::Moment(idle)).unwrap();
        let (moment, _) = port
            .ingest(&mut resident, None, &encoded(&field, &[0, 1, 2, 3, 2]))
            .unwrap();
        let proposal = explorer
            .propose(&port, &resident, moment, &phases)
            .unwrap()
            .unwrap();
        let trial = explorer.execute(&port, &mut resident, proposal).unwrap();
        port.discard(&mut resident, Handle::Pending(trial.pending))
            .unwrap();
        port.discard(&mut resident, Handle::Moment(moment)).unwrap();
        let carry = resident.carried().unwrap();
        assert!(
            carry
                .change
                .storage
                .iter()
                .chain(carry.change.arrivals.iter().flatten())
                .chain(carry.change.states.iter().flatten())
                .flatten()
                .any(|x| !x.is_zero())
        );
        let (idle, _) = port.ingest(&mut resident, None, &empty).unwrap();
        let proposal = explorer
            .propose(&port, &resident, idle, &phases)
            .unwrap()
            .unwrap();
        assert_eq!(proposal.reason(), &ChoiceReason::ZeroInjectionObservation);
        assert!(proposal.view().is_whole());
        assert!(proposal.contextual_score().is_zero());
        let before_ticks = resident.carried().unwrap().ticks;
        let trial = explorer.execute(&port, &mut resident, proposal).unwrap();
        assert!(trial.feedback.word_ticks > 0);
        assert!(resident.carried().unwrap().ticks > before_ticks);
        assert!(
            trial
                .returned
                .receipt
                .balances
                .iter()
                .any(|b| !b.before.is_zero()),
            "the empty injection still traverses retained interior motion"
        );
        assert_eq!(explorer.spent().traversals, 3);
        port.discard(&mut resident, Handle::Pending(trial.pending))
            .unwrap();
    }
    #[test]
    fn mode_exploration_malformed_success_discards_handle_and_records_failure() {
        let field = chain();
        let port = Reference::new(4, 1 << 40);
        let mut resident = port
            .mount_with(&field, &Current::at_rest(&field), generic(&field, 31))
            .unwrap();
        let (moment, _) = port
            .ingest(&mut resident, None, &encoded(&field, &[0, 1, 2]))
            .unwrap();
        let phases = resident.admitted()[0].clone();
        let mut explorer = ModeExplorer::new(
            &field,
            vec![ModeView::whole()],
            ExplorationBudget {
                traversals: 1,
                receiving_stations: 2,
            },
        )
        .unwrap();
        let proposal = explorer
            .propose(&port, &resident, moment, &phases)
            .unwrap()
            .unwrap();
        // Inject a malformed backend receipt after a real traversal, at the exact post-call seam.
        explorer.outstanding = None;
        explorer.state.spent.traversals = 1;
        explorer.state.spent.receiving_stations = phases.aperture() as u64;
        explorer.state.history[0].attempted = 1;
        let (pending, mut returned) = port
            .refine_view(&mut resident, &moment, &phases, proposal.view())
            .unwrap();
        if let ReceiptDetail::Refine { view, .. } = &mut returned.receipt.detail {
            *view = ModeView::primitive(&field, 0, 4).unwrap();
        } else {
            panic!("actual refinement receipt expected")
        }
        let carried = resident.carried().cloned();
        assert!(
            explorer
                .record_return(&port, &mut resident, proposal, pending, returned)
                .is_err()
        );
        assert!(
            port.discard(&mut resident, Handle::Pending(pending))
                .is_err()
        );
        assert_eq!(resident.carried(), carried.as_ref());
        assert_eq!(explorer.spent().traversals, 1);
        assert_eq!(explorer.history()[0].attempted, 1);
        assert_eq!(explorer.history()[0].failed, 1);
        assert_eq!(explorer.history()[0].completed, 0);
        assert!(explorer.history()[0].last.is_none());
        assert!(explorer.checkpoint().is_ok());
    }
    #[test]
    fn mode_exploration_refuses_foreign_proposal_and_changed_arrival_without_feedback() {
        let field = chain();
        let port = Reference::new(4, 1 << 40);
        let mut resident = port
            .mount_with(&field, &Current::at_rest(&field), generic(&field, 31))
            .unwrap();
        let (moment, _) = port
            .ingest(&mut resident, None, &encoded(&field, &[0, 1, 2]))
            .unwrap();
        let phases = resident.admitted()[0].clone();
        let mut one = ModeExplorer::new(
            &field,
            vec![ModeView::whole()],
            ExplorationBudget {
                traversals: 1,
                receiving_stations: 2,
            },
        )
        .unwrap();
        let mut two = ModeExplorer::new(
            &field,
            vec![ModeView::whole()],
            ExplorationBudget {
                traversals: 1,
                receiving_stations: 2,
            },
        )
        .unwrap();
        let wrong = one
            .propose(&port, &resident, moment, &phases)
            .unwrap()
            .unwrap();
        assert!(two.execute(&port, &mut resident, wrong).is_err());
        assert_eq!(two.spent().traversals, 0);
        assert!(one.abandon_outstanding(1));
        assert!(one.checkpoint().is_ok());
        let stale = two
            .propose(&port, &resident, moment, &phases)
            .unwrap()
            .unwrap();
        port.ingest(&mut resident, Some(&moment), &encoded(&field, &[3]))
            .unwrap();
        assert!(two.execute(&port, &mut resident, stale).is_err());
        assert_eq!(two.history()[0].attempted, 0);
        assert_eq!(two.spent().traversals, 0);
        let cancelled = two
            .propose(&port, &resident, moment, &phases)
            .unwrap()
            .unwrap();
        two.cancel(cancelled).unwrap();
        assert!(two.checkpoint().is_ok());
    }
}
