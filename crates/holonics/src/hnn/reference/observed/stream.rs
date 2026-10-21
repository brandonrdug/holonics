//! A stream boundary for the native atomic observed-epoch owner.
//!
//! A committed resident and its finite closing crib are retained. Only the current unfinished
//! physical interval's boundary classes wait beside that opening. At its actual receiving tick,
//! the grouped owner consumes them once and the completed input batch is discarded. This is an
//! unpublished transaction, never a history of published updates or a source replay model.
//!
//! [agent-inferred] On the admitted Lock route, ring zero fits every boundary class and advances
//! once per cell. A receiving ring r must therefore tick within H = product(g < r) d_g cells;
//! other fitting locks can only make that arrival earlier. An unfinished batch has fewer than H
//! classes. Routes without this finite bound refuse, rather than accepting an unbounded queue.
//! This owner touches helix/carry, receiving placement and the compatible continuing thread;
//! paired contacts, holonomy and the tube remain attached through the actual epoch owner.

use super::*;

#[derive(Clone, Debug)]
pub struct ObservedStream {
    resident: Resident,
    crib: ObservedCrib,
    scope: ObservedEpochDepositionScope,
    pending: Vec<usize>,
    bound: usize,
}

/// Exterior evidence for this delivery, never retained by the stream.
#[derive(Debug)]
pub struct ObservedStreamReceipt {
    /// New boundary classes accepted by this call, including its unfinished interval.
    pub accepted: usize,
    /// Classes actually published in this call, including a preceding pending fragment.
    pub published: usize,
    pub pending: usize,
    pub epochs: Vec<ObservedEpochReceipt>,
}

fn refuse(what: &'static str) -> HnnError {
    HnnError::ContinuingState { what }
}

impl ObservedStream {
    /// Additive reciprocal return on the published opening. The current unfinished input
    /// fragment stays exterior and is neither replayed nor flushed. Every validation is staged.
    #[allow(clippy::too_many_arguments)]
    pub fn return_source_relation(
        &mut self,
        reference: &Reference,
        pairing: &PairingDeclaration,
        prior: &crate::ratio::linear::ExactRatMatrix,
        ring: usize,
        family: &crate::hnn::reference::reciprocal::JointFamily,
        origin: crate::hnn::reference::reciprocal::ReturnOrigin,
    ) -> Result<crate::hnn::reference::reciprocal::ReciprocalOutcome, HnnError> {
        let mut next = self.clone();
        let frontier = self.pending_frontier(pairing)?;
        let accepted = self.accepted_cells()?;
        let cut = reference.bind_source_return(
            &next.resident,
            &next.crib,
            pairing,
            prior,
            ring,
            family,
            origin,
        )?;
        let result = cut.publish(reference, &mut next.resident, &next.crib)?;
        next.bound = Self::finite_bound(&next.resident)?;
        let next = Self::restore(next.resident, next.crib, next.scope, next.pending)?;
        if next.accepted_cells()? != accepted || next.pending_frontier(pairing)? != frontier {
            return Err(refuse(
                "a reciprocal source successor preserves the accepted/pending frontier",
            ));
        }
        *self = next;
        Ok(result)
    }
    pub fn new(
        resident: Resident,
        crib: ObservedCrib,
        scope: ObservedEpochDepositionScope,
    ) -> Result<Self, HnnError> {
        Self::restore(resident, crib, scope, Vec::new())
    }

    fn finite_bound(resident: &Resident) -> Result<usize, HnnError> {
        resident.admit_exact_current()?;
        if resident.observed_epoch_terminal
            || resident.moments.len() != 1
            || !resident.pending.is_empty()
            || !resident.staged.is_empty()
            || resident.aeon.awaiting
        {
            return Err(refuse(
                "a bounded observed stream needs one continuing moment at an ordinary committed native opening",
            ));
        }
        resident.field.admit_lock_route()?;
        let [phases] = resident.admitted.as_slice() else {
            return Err(refuse("one receiving section bounds an observed stream"));
        };
        if phases.aperture() != 1
            || !resident.field.sources().contains(&0)
            || (0..resident.field.alphabet()).any(|class| {
                !resident
                    .field
                    .ring(0)
                    .fits(resident.field.ring(0).port(class))
            })
        {
            return Err(refuse(
                "a bounded observed stream needs an aperture-one receiver and an always-ticking first source ring",
            ));
        }
        resident.field.rings()[..phases.ring()]
            .iter()
            .try_fold(1usize, |product, ring| {
                product
                    .checked_mul(
                        usize::try_from(ring.period()).map_err(|_| HnnError::CountOverflow)?,
                    )
                    .ok_or(HnnError::CountOverflow)
            })
    }

    /// Validate a saved current transaction against the restored native opening. Complete
    /// sections cannot appear here: they must already have been consumed and dropped.
    pub fn restore(
        resident: Resident,
        crib: ObservedCrib,
        scope: ObservedEpochDepositionScope,
        pending: Vec<usize>,
    ) -> Result<Self, HnnError> {
        let bound = Self::finite_bound(&resident)?;
        if scope == ObservedEpochDepositionScope::LocalReceivingReturn
            && resident.receiving_law() != crate::hnn::receiving::ReceivingLaw::RetainedFibreV1
        {
            return Err(refuse(
                "local receiving streams explicitly require RetainedFibreV1",
            ));
        }
        let published = resident
            .moments
            .values()
            .next()
            .map_or(0, SourceMoment::cells);
        if crib.next_position()
            != usize::try_from(published).map_err(|_| HnnError::CountOverflow)?
            || pending.len() >= bound
            || published
                .checked_add(u64::try_from(pending.len()).map_err(|_| HnnError::CountOverflow)?)
                .ok_or(HnnError::CountOverflow)?
                > resident.field.population()
        {
            return Err(refuse(
                "the observed stream's finite transaction against its native opening and horizon",
            ));
        }
        ObservedCrib::from_unplaced_checkpoint(
            &resident.field,
            &resident.current,
            crib.next_position(),
            &crib.unplaced_checkpoint()?,
        )?;
        let stream = Self {
            resident,
            crib,
            scope,
            pending,
            bound,
        };
        // Clock validation does not need a newly authored pairing: use the native selective
        // law in-crate and admit the actual producing codec when a delivery or view consumes it.
        let mut lift = stream.resident.current.lift().to_vec();
        let receiver = stream.resident.admitted[0].ring();
        for &class in &stream.pending {
            let step = stream.resident.field.step_class(&mut lift, class, None)?;
            if step.ticks[receiver] != 0 || step.carry_out {
                return Err(refuse(
                    "a saved pending interval already crossed its actual receiving section",
                ));
            }
        }
        Ok(stream)
    }

    /// Fresh explicit opt-in. The existing stream remains the sole ingress owner.
    pub fn select_prepared_input(&mut self,pairing:&PairingDeclaration)->Result<(),HnnError>{
        if !self.pending.is_empty() || self.scope!=ObservedEpochDepositionScope::LocalReceivingReturn{return Err(refuse("fresh prepared input uses LocalReceivingReturn with no pending arrivals"));}
        self.resident.select_prepared_input(pairing)
    }

    pub fn resident(&self) -> &Resident {
        &self.resident
    }
    pub fn crib(&self) -> &ObservedCrib {
        &self.crib
    }
    pub fn pending_classes(&self) -> &[usize] {
        &self.pending
    }
    pub fn epoch_bound(&self) -> usize {
        self.bound
    }
    pub fn scope(&self) -> ObservedEpochDepositionScope {
        self.scope
    }
    pub fn accepted_cells(&self) -> Result<u64, HnnError> {
        self.resident
            .moments
            .values()
            .next()
            .map_or(0, SourceMoment::cells)
            .checked_add(u64::try_from(self.pending.len()).map_err(|_| HnnError::CountOverflow)?)
            .ok_or(HnnError::CountOverflow)
    }

    fn pending_frontier(&self, pairing: &PairingDeclaration) -> Result<Current, HnnError> {
        let boundary =
            PairedObservation::admit(&self.resident.field, &self.resident.constitution, pairing)?;
        let encoded = boundary.encode(&self.pending)?;
        let mut frontier = self.resident.current.clone();
        let receiver = self.resident.admitted[0].ring();
        for at in 0..encoded.len() {
            let step = frontier.step(&self.resident.field, &encoded, at)?;
            if step.ticks[receiver] != 0 || step.carry_out {
                return Err(refuse(
                    "the unfinished observed interval crossed its receiving section",
                ));
            }
        }
        Ok(frontier)
    }

    /// Accept source classes transactionally. Only actual receiving ticks publish the native
    /// grouped comparison; no end-of-source flush or artificial terminal clock is introduced.
    pub fn receive(
        &mut self,
        reference: &Reference,
        pairing: &PairingDeclaration,
        classes: &[usize],
    ) -> Result<ObservedStreamReceipt, HnnError> {
        self.receive_with_execution(reference, pairing, classes, &HostObservedEpochExecution)
    }

    /// Accept source classes through the explicitly selected observed-epoch execution.
    /// The stream still publishes only after the full delivery succeeds.
    pub fn receive_with_execution(
        &mut self,
        reference: &Reference,
        pairing: &PairingDeclaration,
        classes: &[usize],
        execution: &dyn ObservedEpochExecution,
    ) -> Result<ObservedStreamReceipt, HnnError> {
        self.receive_diagnosed_with_execution(
            reference,
            pairing,
            classes,
            execution,
            &mut |_, _| {},
        )
    }

    /// The same transaction with an exterior observer for the first failed whole/R stage
    /// in each actual epoch. A fatal refusal still reports evidence before returning the
    /// original error. No evidence is retained in the stream or its checkpoint.
    pub fn receive_diagnosed(
        &mut self,
        reference: &Reference,
        pairing: &PairingDeclaration,
        classes: &[usize],
        stage_refused: &mut dyn FnMut(EpochStageAttempt, &EpochStageRefusal),
    ) -> Result<ObservedStreamReceipt, HnnError> {
        self.receive_diagnosed_with_execution(
            reference,
            pairing,
            classes,
            &HostObservedEpochExecution,
            stage_refused,
        )
    }

    /// The same transaction with an explicitly selected observed-epoch execution and
    /// an exterior observer for the first failed whole/R stage in each actual epoch.
    /// A fatal refusal still reports evidence before returning the original error.
    /// Neither execution nor evidence is retained in the stream or its checkpoint.
    pub fn receive_diagnosed_with_execution(
        &mut self,
        reference: &Reference,
        pairing: &PairingDeclaration,
        classes: &[usize],
        execution: &dyn ObservedEpochExecution,
        stage_refused: &mut dyn FnMut(EpochStageAttempt, &EpochStageRefusal),
    ) -> Result<ObservedStreamReceipt, HnnError> {
        if self.resident.prepared_input.as_ref().is_some_and(|p|p.mode()!=prepared_input::PrefixMode::Training){return Err(refuse("forecast conditioning advances the frozen prefix receiver, not observed training"));}
        let mut next = self.clone();
        if next
            .accepted_cells()?
            .checked_add(u64::try_from(classes.len()).map_err(|_| HnnError::CountOverflow)?)
            .ok_or(HnnError::CountOverflow)?
            > next.resident.field.population()
        {
            return Err(refuse(
                "the observed stream delivery exceeds its declared source horizon",
            ));
        }
        let mut frontier = next.pending_frontier(pairing)?;
        let mut boundary =
            PairedObservation::admit(&next.resident.field, &next.resident.constitution, pairing)?;
        let mut receiver = next.resident.admitted[0].ring();
        let mut epochs = Vec::new();
        let mut published = 0;
        for &class in classes {
            let encoded = boundary.encode(&[class])?;
            let step = frontier.step(&next.resident.field, &encoded, 0)?;
            next.pending.push(class);
            if next.pending.len() > next.bound {
                return Err(refuse(
                    "the physical receiving bound did not close the observed interval",
                ));
            }
            if step.ticks[receiver] != 0 || step.carry_out {
                let receipt = reference.observe_epoch_continuing_at_cuts_with_scope_diagnosed(
                    &mut next.resident,
                    &mut next.crib,
                    pairing,
                    &next.pending,
                    None,
                    &[],
                    false,
                    execution,
                    next.scope,
                    stage_refused,
                )?;
                if receipt.consumed != next.pending.len() || receipt.terminal_partial {
                    return Err(refuse(
                        "the grouped owner did not consume exactly the actual unfinished interval",
                    ));
                }
                published += receipt.consumed;
                epochs.push(receipt);
                next.pending.clear();
                next.bound = Self::finite_bound(&next.resident)?;
                receiver = next.resident.admitted[0].ring();
                frontier = next.resident.current.clone();
                boundary = PairedObservation::admit(
                    &next.resident.field,
                    &next.resident.constitution,
                    pairing,
                )?;
            }
        }
        let receipt = ObservedStreamReceipt {
            accepted: classes.len(),
            published,
            pending: next.pending.len(),
            epochs,
        };
        *self = next;
        Ok(receipt)
    }

    /// Private query fork of the actual unfinished native word chain. The existing epoch
    /// forward owner advances its source moment, current, address, carried interior and charts
    /// once through this current fragment. No comparison or deposition is performed; the
    /// committed stream is untouched and no completed source interval is replayed.
    pub fn query_fork(
        &self,
        reference: &Reference,
        pairing: &PairingDeclaration,
    ) -> Result<(Resident, ObservedCrib), HnnError> {
        self.query_fork_selected(reference, pairing, None)
    }

    /// Same immutable physical prefix, explicitly dispatched through an admitted executor.
    /// No deposition/scoring or host fallback. The existing host entry retains its old path.
    pub fn query_fork_with_execution(
        &self,
        reference: &Reference,
        pairing: &PairingDeclaration,
        execution: &dyn ObservedEpochExecution,
    ) -> Result<(Resident, ObservedCrib), HnnError> {
        self.query_fork_selected(reference, pairing, Some(execution))
    }

    fn query_fork_selected(
        &self,
        reference: &Reference,
        pairing: &PairingDeclaration,
        execution: Option<&dyn ObservedEpochExecution>,
    ) -> Result<(Resident, ObservedCrib), HnnError> {
        let mut forecast=self.resident.clone();
        if forecast.prepared_input.is_some(){forecast.freeze_prepared_forecast()?;}
        let frontier = self.pending_frontier(pairing)?;
        if self.pending.is_empty() {
            return Ok((forecast.clone(), self.crib.clone()));
        }
        let boundary =
            PairedObservation::admit(&self.resident.field, &self.resident.constitution, pairing)?;
        let encoded = boundary.encode(&self.pending)?;
        let moment = *self
            .resident
            .moments
            .keys()
            .next()
            .ok_or_else(|| refuse("the query fork's one continuing moment"))?;
        let mut forward = match execution {
            None => reference.read_epoch_at_cuts(
                &forecast,
                &moment,
                &self.resident.admitted[0],
                &encoded,
                &[self.pending.len()],
            )?,
            Some(execution) => reference.read_epoch_at_cuts_with_execution(
                &forecast,
                &moment,
                &self.resident.admitted[0],
                &encoded,
                &[self.pending.len()],
                execution,
            )?,
        };
        if forward.consumed != self.pending.len() || forward.carry_out {
            return Err(refuse("the query fork's unfinished native prefix"));
        }
        let resident = forward
            .prefixes
            .remove(&self.pending.len())
            .ok_or_else(|| refuse("the actual unfinished native prefix was not returned"))?;
        // The words are transient operands of this current transaction, never part of a save.
        drop(forward);
        if resident.current != frontier || resident.constitution != self.resident.constitution {
            return Err(refuse(
                "the query prefix must retain contemporary material and its actual frontier",
            ));
        }
        let mut crib = self.crib.clone();
        let mut current = self.resident.current.clone();
        for (at, &class) in self.pending.iter().enumerate() {
            let before = current.clone();
            current.step(&self.resident.field, &encoded, at)?;
            crib.push(
                &self.resident.field,
                &before,
                class,
                None,
                self.resident.field.crib().window,
            )?;
        }
        Ok((resident, crib))
    }

    /// Only the bounded unfinished boundary transaction is serialized here. Native material,
    /// passage and the closing crib retain their existing owners and checkpoint codecs.
    pub fn pending_checkpoint(&self) -> String {
        let (header, law_field) = match self.resident.receiving_law() {
            crate::hnn::receiving::ReceivingLaw::CoarseGrainV1 => {
                ("observed-stream-pending-v1", String::new())
            }
            crate::hnn::receiving::ReceivingLaw::RetainedFibreV1 => (
                "observed-stream-pending-v2",
                "retained-fibre-v1 ".to_string(),
            ),
        };
        let scope = match self.scope {
            ObservedEpochDepositionScope::All => "all",
            ObservedEpochDepositionScope::LocalReceivingReturn => "local-receiving-return-v1",
            ObservedEpochDepositionScope::NormalMaps => "normal-maps",
            ObservedEpochDepositionScope::NormalMapsAndChannelDissipation => {
                "normal-maps-channel-dissipation"
            }
            ObservedEpochDepositionScope::NormalMapsAndChannelMaterial => {
                "normal-maps-channel-material"
            }
        };
        format!(
            "{header} {law_field}{scope} {} {} {}\n{}\n",
            self.resident.constitution.commit(),
            self.crib.next_position(),
            self.pending.len(),
            self.pending
                .iter()
                .map(ToString::to_string)
                .collect::<Vec<_>>()
                .join(" ")
        )
    }

    pub fn restore_checkpoint(
        resident: Resident,
        crib: ObservedCrib,
        text: &str,
    ) -> Result<Self, HnnError> {
        let bound = Self::finite_bound(&resident)?;
        let mut lines = text.lines();
        let header: Vec<_> = lines
            .next()
            .ok_or_else(|| refuse("the unfinished observed transaction header"))?
            .split_whitespace()
            .collect();
        let (law, scope_at, commit_at) = match header.first().copied() {
            Some("observed-stream-pending-v1") if header.len() == 5 => {
                (crate::hnn::receiving::ReceivingLaw::CoarseGrainV1, 1, 2)
            }
            Some("observed-stream-pending-v2") if header.len() == 6 => {
                let law = header[1]
                    .parse::<crate::hnn::receiving::ReceivingLaw>()
                    .map_err(|_| refuse("the explicit unfinished-stream receiving law"))?;
                if law != crate::hnn::receiving::ReceivingLaw::RetainedFibreV1 {
                    return Err(refuse(
                        "version-2 pending streams explicitly name retained-fibre-v1",
                    ));
                }
                (law, 2, 3)
            }
            _ => return Err(refuse("the unfinished observed transaction version")),
        };
        if law != resident.receiving_law() {
            return Err(refuse(
                "the pending transaction's receiving law matches its restored resident",
            ));
        }
        let scope = match header[scope_at] {
            "all" => ObservedEpochDepositionScope::All,
            "local-receiving-return-v1" => ObservedEpochDepositionScope::LocalReceivingReturn,
            "normal-maps" => ObservedEpochDepositionScope::NormalMaps,
            "normal-maps-channel-dissipation" => {
                ObservedEpochDepositionScope::NormalMapsAndChannelDissipation
            }
            "normal-maps-channel-material" => {
                ObservedEpochDepositionScope::NormalMapsAndChannelMaterial
            }
            _ => return Err(refuse("the saved observed deposition scope")),
        };
        let commit: u64 = header[commit_at]
            .parse()
            .map_err(|_| refuse("the unfinished transaction commit"))?;
        let published: usize = header[commit_at + 1]
            .parse()
            .map_err(|_| refuse("the unfinished transaction opening"))?;
        let count: usize = header[commit_at + 2]
            .parse()
            .map_err(|_| refuse("the unfinished transaction count"))?;
        if commit != resident.constitution.commit()
            || published != crib.next_position()
            || count >= bound
        {
            return Err(refuse(
                "the unfinished transaction against its native opening and physical bound",
            ));
        }
        let mut pending = Vec::new();
        for value in lines
            .next()
            .ok_or_else(|| refuse("the unfinished transaction classes"))?
            .split_whitespace()
        {
            if pending.len() == count {
                return Err(refuse("the unfinished transaction class count"));
            }
            pending.push(
                value
                    .parse()
                    .map_err(|_| refuse("an unfinished transaction class"))?,
            );
        }
        if pending.len() != count || lines.next().is_some() {
            return Err(refuse("the unfinished transaction class count"));
        }
        Self::restore(resident, crib, scope, pending)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::hnn::constitution::ContinuingState;
    use crate::hnn::paired::PairedCarrier;
    use crate::hnn::tests::support::{contact, small_field_of};
    use std::sync::atomic::{AtomicUsize, Ordering};

    struct CountingExecution {
        forwards: AtomicUsize,
        returns: AtomicUsize,
        flows: AtomicUsize,
        refuse_forward: bool,
    }

    impl CountingExecution {
        fn new(refuse_forward: bool) -> Self {
            Self {
                forwards: AtomicUsize::new(0),
                returns: AtomicUsize::new(0),
                flows: AtomicUsize::new(0),
                refuse_forward,
            }
        }
    }

    impl ObservedEpochExecution for CountingExecution {
        fn forward(
            &self,
            field: &crate::hnn::field::Field,
            constitution: &crate::hnn::constitution::Constitution,
            ratio: &crate::hnn::pending::PendingRatio,
            charts: &mut crate::hnn::chart::Charts,
            opening: &crate::hnn::word::WordOpening,
        ) -> Result<ObservedEpochForwardWord, HnnError> {
            self.forwards.fetch_add(1, Ordering::Relaxed);
            if self.refuse_forward {
                return Err(HnnError::ContinuingState {
                    what: "selected stream test execution refused forward",
                });
            }
            HostObservedEpochExecution.forward(field, constitution, ratio, charts, opening)
        }

        fn pull_back(
            &self,
            word: crate::hnn::word::Word<'_>,
            covector: &crate::hnn::ratio::RatioCovector,
            map: &crate::ratio::linear::ExactRatMatrix,
            phases: &crate::hnn::receiving::ReceivingPhases,
        ) -> Result<crate::hnn::port::WordReturn, HnnError> {
            self.returns.fetch_add(1, Ordering::Relaxed);
            HostObservedEpochExecution.pull_back(word, covector, map, phases)
        }

        fn aggregate_records(
            &self,
            locus: crate::hnn::constitution::LinearLocus,
            rows: usize,
            columns: usize,
            receiver_grain: u32,
            epoch_cells: u64,
            epoch: u64,
            heard_cells: u64,
            records: &[crate::hnn::constitution::EpochProducerRecordReading],
        ) -> Result<crate::hnn::constitution::EpochRecordFlowReading, HnnError> {
            self.flows.fetch_add(1, Ordering::Relaxed);
            HostObservedEpochExecution.aggregate_records(
                locus,
                rows,
                columns,
                receiver_grain,
                epoch_cells,
                epoch,
                heard_cells,
                records,
            )
        }
    }

    fn opening() -> (Reference, ObservedStream, PairingDeclaration, Constitution) {
        opening_with_law(None)
    }

    fn opening_with_law(
        law: Option<crate::hnn::receiving::ReceivingLaw>,
    ) -> (Reference, ObservedStream, PairingDeclaration, Constitution) {
        // The existing serial small-field declaration, with the always-ticking first source
        // and the grouped phase owner's smallest odd receiving period.
        let base = small_field_of(
            &[5, 2, 3],
            vec![contact(0, 1, 1, 0), contact(1, 2, 1, 0)],
            2,
            4,
        );
        let mut declaration = base.declaration().clone();
        declaration.rings[0].lock = (0..4).collect();
        for ring in &mut declaration.rings[1..] {
            ring.lock.clear();
        }
        let field = Field::declare(declaration.by_lattice_rule()).unwrap();
        let pairing = PairingDeclaration::Family {
            table: (0..4).map(|class| (class, class ^ 1)).collect(),
        };
        let material = PairedCarrier::found(
            &field,
            Constitution::initial(&field, 1 << 40).unwrap(),
            0,
            &pairing,
        )
        .unwrap()
        .0;
        let reference = Reference::new(16, 1 << 40);
        let mut resident = reference
            .mount_with(&field, &Current::at_rest(&field), material.clone())
            .unwrap();
        if let Some(law) = law {
            resident.select_receiving_law(law).unwrap();
        }
        let boundary = PairedObservation::admit(&field, &material, &pairing).unwrap();
        reference
            .ingest(&mut resident, None, &boundary.encode(&[]).unwrap())
            .unwrap();
        let stream = ObservedStream::new(
            resident,
            ObservedCrib::new(0),
            ObservedEpochDepositionScope::NormalMaps,
        )
        .unwrap();
        (reference, stream, pairing, material)
    }

    #[test]
    fn unfinished_native_interval_roundtrips_and_closes_at_the_actual_receiving_tick() {
        let (reference, mut stream, pairing, opening) = opening();
        let before = stream.resident.continuing_state(0).unwrap();
        let partial = stream
            .receive(&reference, &pairing, &[0, 1, 2, 3, 0, 1, 2])
            .unwrap();
        assert_eq!(
            (partial.accepted, partial.published, partial.pending),
            (7, 0, 7)
        );
        assert!(partial.epochs.is_empty());
        assert_eq!(stream.epoch_bound(), 10);
        assert_eq!(stream.resident.continuing_state(0).unwrap(), before);
        let pending_text = stream.pending_checkpoint();
        assert!(pending_text.starts_with("observed-stream-pending-v1 normal-maps "));
        let parsed = ContinuingState::from_text(&before.to_text(), 1 << 40).unwrap();
        let field = stream.resident.field.clone();
        let cold_resident = reference
            .mount_continued(&field, &Current::at_rest(&field), opening, &parsed)
            .unwrap();
        let cold_crib = ObservedCrib::from_unplaced_checkpoint(
            &field,
            cold_resident.current(),
            0,
            &stream.crib.unplaced_checkpoint().unwrap(),
        )
        .unwrap();
        let mut cold =
            ObservedStream::restore_checkpoint(cold_resident, cold_crib, &pending_text).unwrap();
        assert_eq!(cold.pending_checkpoint(), pending_text);
        let (warm_view, _) = stream.query_fork(&reference, &pairing).unwrap();
        let (cold_view, _) = cold.query_fork(&reference, &pairing).unwrap();
        assert_eq!(
            warm_view.continuing_state(0).unwrap(),
            cold_view.continuing_state(0).unwrap()
        );
        assert_eq!(warm_view.moments.values().next().unwrap().cells(), 7);
        assert!(
            warm_view.carried.is_some(),
            "the unfinished word chain's physical interior reaches the query"
        );
        assert_eq!(
            stream.resident.carried, None,
            "the committed opening remains untouched"
        );
        let warm_receipt = stream.receive(&reference, &pairing, &[3, 0, 1]).unwrap();
        let cold_receipt = cold.receive(&reference, &pairing, &[3, 0, 1]).unwrap();
        assert_eq!(
            (
                warm_receipt.accepted,
                warm_receipt.published,
                warm_receipt.pending
            ),
            (3, 10, 0)
        );
        assert_eq!(warm_receipt.epochs.len(), 1);
        assert!(warm_receipt.epochs[0].closed_section);
        assert!(!warm_receipt.epochs[0].terminal_partial);
        assert_eq!(
            warm_receipt.epochs[0].outcome,
            cold_receipt.epochs[0].outcome
        );
        assert_eq!(
            stream.resident.continuing_state(0).unwrap(),
            cold.resident.continuing_state(0).unwrap()
        );
        assert_eq!(stream.pending_checkpoint(), cold.pending_checkpoint());
        assert_eq!(stream.accepted_cells().unwrap(), 10);
    }

    #[test]
    fn fine_pending_checkpoint_keeps_law_identity_and_refuses_mismatch_atomically() {
        use crate::hnn::receiving::ReceivingLaw;

        let (reference, mut stream, pairing, opening) =
            opening_with_law(Some(ReceivingLaw::RetainedFibreV1));
        stream.receive(&reference, &pairing, &[0, 1, 2, 3]).unwrap();
        let pending = stream.pending_checkpoint();
        assert!(pending.starts_with("observed-stream-pending-v2 retained-fibre-v1 normal-maps "));
        let saved = stream.resident.continuing_state(0).unwrap();
        let parsed = ContinuingState::from_text(&saved.to_text(), 1 << 40).unwrap();
        let field = stream.resident.field.clone();
        let cold_resident = reference
            .mount_continued(&field, &Current::at_rest(&field), opening, &parsed)
            .unwrap();
        assert_eq!(cold_resident.receiving_law(), ReceivingLaw::RetainedFibreV1);
        let cold_crib = ObservedCrib::from_unplaced_checkpoint(
            &field,
            cold_resident.current(),
            stream.crib.next_position(),
            &stream.crib.unplaced_checkpoint().unwrap(),
        )
        .unwrap();
        let cold =
            ObservedStream::restore_checkpoint(cold_resident, cold_crib.clone(), &pending).unwrap();
        assert_eq!(cold.pending_checkpoint(), pending);
        assert_eq!(cold.resident.continuing_state(0).unwrap(), saved);

        let mut wrong_law = cold.resident.clone();
        wrong_law.receiving_law = ReceivingLaw::CoarseGrainV1;
        assert!(ObservedStream::restore_checkpoint(wrong_law, cold_crib, &pending).is_err());
        let before = stream.resident.continuing_state(0).unwrap();
        assert_eq!(stream.pending_checkpoint(), pending);
        assert_eq!(before, saved);
    }

    #[test]
    fn unfinished_stream_rejects_completed_or_mismatched_saved_transactions_and_rolls_back_refused_delivery()
     {
        let (reference, mut stream, pairing, _) = opening();
        let saved = stream.pending_checkpoint();
        let malformed = format!(
            "observed-stream-pending-v1 normal-maps {} 0 10\n0 0 0 0 0 0 0 0 0 0\n",
            stream.resident.constitution.commit()
        );
        assert!(
            ObservedStream::restore_checkpoint(
                stream.resident.clone(),
                stream.crib.clone(),
                &malformed
            )
            .is_err()
        );
        assert!(
            ObservedStream::restore_checkpoint(
                stream.resident.clone(),
                stream.crib.clone(),
                &saved.replace("normal-maps", "other")
            )
            .is_err()
        );
        let before = stream.resident.continuing_state(0).unwrap();
        let mut missing = stream.resident.clone();
        missing.moments.clear();
        assert!(ObservedStream::new(missing, stream.crib.clone(), stream.scope).is_err());
        assert!(stream.receive(&reference, &pairing, &[0, 1, 4]).is_err());
        assert_eq!(stream.pending_checkpoint(), saved);
        assert_eq!(stream.resident.continuing_state(0).unwrap(), before);
    }
    #[test]
    fn d_only_scope_pending_checkpoint_roundtrips_and_refused_input_is_atomic() {
        let (reference, mut stream, pairing, _) = opening();
        stream.scope = ObservedEpochDepositionScope::NormalMapsAndChannelDissipation;
        stream.receive(&reference, &pairing, &[0, 1, 2]).unwrap();
        let pending = stream.pending_checkpoint();
        assert!(pending.starts_with("observed-stream-pending-v1 normal-maps-channel-dissipation "));
        let before = stream.resident.continuing_state(0).unwrap();
        let mut cold = ObservedStream::restore_checkpoint(
            stream.resident.clone(),
            stream.crib.clone(),
            &pending,
        )
        .unwrap();
        assert_eq!(cold.scope, stream.scope);
        assert_eq!(cold.pending_checkpoint(), pending);
        assert_eq!(cold.resident.continuing_state(0).unwrap(), before);
        assert!(cold.receive(&reference, &pairing, &[4]).is_err());
        assert_eq!(cold.pending_checkpoint(), pending);
        assert_eq!(cold.resident.continuing_state(0).unwrap(), before);
        // A partial continuation remains below the actual receiving section.
        stream.receive(&reference, &pairing, &[3]).unwrap();
        cold.receive(&reference, &pairing, &[3]).unwrap();
        assert_eq!(stream.pending_checkpoint(), cold.pending_checkpoint());
        assert_eq!(
            stream.resident.continuing_state(0).unwrap(),
            cold.resident.continuing_state(0).unwrap()
        );
    }

    #[test]
    fn selected_stream_execution_delegates_actual_epoch_work() {
        let (reference, mut selected, pairing, _) = opening();
        let (_, mut host, _, _) = opening();
        let execution = CountingExecution::new(false);
        let classes = [0, 1, 2, 3, 0, 1, 2, 3, 0, 1];
        selected
            .receive_with_execution(&reference, &pairing, &classes, &execution)
            .unwrap();
        host.receive(&reference, &pairing, &classes).unwrap();
        assert!(execution.forwards.load(Ordering::Relaxed) > 0);
        assert!(execution.returns.load(Ordering::Relaxed) > 0);
        assert!(execution.flows.load(Ordering::Relaxed) > 0);
        assert_eq!(
            selected.resident.continuing_state(0).unwrap(),
            host.resident.continuing_state(0).unwrap()
        );
        assert_eq!(selected.pending_checkpoint(), host.pending_checkpoint());
        assert_eq!(selected.crib, host.crib);
    }

    #[test]
    fn selected_stream_execution_refusal_rolls_back_resident_crib_and_pending_input() {
        let (reference, mut stream, pairing, _) = opening();
        let before = stream.resident.continuing_state(0).unwrap();
        let before_crib = stream.crib.clone();
        let before_pending = stream.pending_checkpoint();
        let execution = CountingExecution::new(true);
        let classes = [0, 1, 2, 3, 0, 1, 2, 3, 0, 1];
        let error = stream
            .receive_with_execution(&reference, &pairing, &classes, &execution)
            .unwrap_err();
        assert!(matches!(error, HnnError::ContinuingState { .. }));
        assert_eq!(execution.forwards.load(Ordering::Relaxed), 1);
        assert_eq!(stream.resident.continuing_state(0).unwrap(), before);
        assert_eq!(stream.crib, before_crib);
        assert_eq!(stream.pending_checkpoint(), before_pending);
    }
}
