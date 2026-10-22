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
        if resident.prepared_input.as_ref().is_some_and(|p|p.context_chart()==prepared_input::ContextChart::LaggedReceiverBoundaryV1) && scope!=ObservedEpochDepositionScope::LocalReceivingReturnWithHeldMap{return Err(refuse("native section explicitly retains its held local publication policy"));}
        if scope.is_local_receiving()
            && resident.receiving_law() != crate::hnn::receiving::ReceivingLaw::RetainedFibreV1
            && !resident.prepared_input.as_ref().is_some_and(|p|p.context_chart()==prepared_input::ContextChart::LaggedReceiverBoundaryV1)
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
        if !self.pending.is_empty() || !self.scope.is_local_receiving(){return Err(refuse("fresh prepared input uses LocalReceivingReturn with no pending arrivals"));}
        self.resident.select_prepared_input(pairing)
    }

    /// Fresh framed law; four known source contexts, not uncertain branches.
    pub fn select_source_framing_prepared_input(&mut self,pairing:&PairingDeclaration)->Result<(),HnnError>{
        if !self.pending.is_empty()||!self.scope.is_local_receiving(){return Err(refuse("fresh source framing uses local receiving and no pending arrivals"));}
        self.resident.select_source_framing_prepared_input(pairing)
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
        let local_family = self.resident.constitution.receiving_return_policy(self.resident.admitted[0].ring()) == Some(crate::hnn::receiving::RetainedReturnPolicy::FamilyLocalRetainedReturnV1);
        let adaptive = self.resident.constitution.receiving_representation_policy(self.resident.admitted[0].ring()) == Some(crate::hnn::constitution::ReceivingRepresentationPolicy::BoundedSubquantumV1);
        let native=self.resident.prepared_input.as_ref().is_some_and(|p|p.context_chart()==prepared_input::ContextChart::LaggedReceiverBoundaryV1);
        let quadratic=self.resident.prepared_input.as_ref().map(|p|p.work_receipt_policy());
        let (header, law_field) = if let Some(crate::hnn::word::action::PreparationWorkPolicy::NativeQuadraticV1(b))=quadratic {(if self.resident.constitution.native_rational_receiving(self.resident.admitted[0].ring()){"observed-stream-pending-native-rational-v1"}else{"observed-stream-pending-native-current-v2"},format!("{} {} {} native-quadratic-work-v1 {} {} {} ",crate::hnn::word::native_prediction::LAW,self.resident.constitution.receiving_return_policy(self.resident.admitted[0].ring()).expect("native receiving owner").tag(),if adaptive{"bounded-subquantum20-v1"}else{"fixed-lattice-v1"},b.aggregate_bits,b.integer_bits,b.coordinates))} else if native {("observed-stream-pending-native-current-v1",format!("{} {} {} ",crate::hnn::word::native_prediction::LAW,self.resident.constitution.receiving_return_policy(self.resident.admitted[0].ring()).expect("native receiving owner").tag(),if adaptive{"bounded-subquantum20-v1"}else{"fixed-lattice-v1"}))} else if adaptive {("observed-stream-pending-v4", "retained-fibre-v1 family-local-retained-return-v1 bounded-subquantum20-v1 ".to_string())} else if local_family { ("observed-stream-pending-v3", "retained-fibre-v1 family-local-retained-return-v1 ".to_string()) } else { match self.resident.receiving_law() {
            crate::hnn::receiving::ReceivingLaw::CoarseGrainV1 => {
                ("observed-stream-pending-v1", String::new())
            }
            crate::hnn::receiving::ReceivingLaw::RetainedFibreV1 => (
                "observed-stream-pending-v2",
                "retained-fibre-v1 ".to_string(),
            ),
        }};
        let scope = match self.scope {
            ObservedEpochDepositionScope::All => "all",
            ObservedEpochDepositionScope::LocalReceivingReturn => "local-receiving-return-v1",
            ObservedEpochDepositionScope::LocalReceivingReturnWithHeldMap => "local-receiving-held-map-v1",
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
        let native=matches!(header.first().copied(),Some("observed-stream-pending-native-current-v1"|"observed-stream-pending-native-current-v2"|"observed-stream-pending-native-rational-v1"));
        let rational=header.first().copied()==Some("observed-stream-pending-native-rational-v1");
        if rational!=resident.constitution.native_rational_receiving(resident.admitted[0].ring()){return Err(refuse("pending native rational moments policy matches original source owner"));}
        let quadratic=rational||header.first().copied()==Some("observed-stream-pending-native-current-v2");
        let owner_policy=resident.prepared_input.as_ref().map(|p|p.work_receipt_policy());
        if quadratic!=matches!(owner_policy,Some(crate::hnn::word::action::PreparationWorkPolicy::NativeQuadraticV1(_))){return Err(refuse("native pending keeps its original work receipt policy"));}
        if let Some(crate::hnn::word::action::PreparationWorkPolicy::NativeQuadraticV1(b))=owner_policy{
            if header.get(4).copied()!=Some("native-quadratic-work-v1")||header.get(5).and_then(|s|s.parse::<u64>().ok())!=Some(b.aggregate_bits)||header.get(6).and_then(|s|s.parse::<u64>().ok())!=Some(b.integer_bits)||header.get(7).and_then(|s|s.parse::<usize>().ok())!=Some(b.coordinates){return Err(refuse("native pending work resource declaration"));}
        }
        let native_owner=resident.prepared_input.as_ref().is_some_and(|p|p.context_chart()==prepared_input::ContextChart::LaggedReceiverBoundaryV1);
        if native!=native_owner{return Err(refuse("native prediction pending schema matches its original model"));}
        let adaptive = if native{header.get(3).copied()==Some("bounded-subquantum20-v1")}else{header.first().copied()==Some("observed-stream-pending-v4")};
        if adaptive != (resident.constitution.receiving_representation_policy(resident.admitted[0].ring())==Some(crate::hnn::constitution::ReceivingRepresentationPolicy::BoundedSubquantumV1)) {return Err(refuse("pending representation policy matches native material"));}
        let family_local = if native{header.get(2).copied()==Some("family-local-retained-return-v1")}else{matches!(header.first().copied(),Some("observed-stream-pending-v3"|"observed-stream-pending-v4"))};
        if family_local != (resident.constitution.receiving_return_policy(resident.admitted[0].ring()) == Some(crate::hnn::receiving::RetainedReturnPolicy::FamilyLocalRetainedReturnV1)) { return Err(refuse("pending return policy matches native material")); }
        let (law, scope_at, commit_at) = match header.first().copied() {
            Some("observed-stream-pending-native-current-v2"|"observed-stream-pending-native-rational-v1") if header.len()==12&&header[1]==crate::hnn::word::native_prediction::LAW&&matches!(header[3],"fixed-lattice-v1"|"bounded-subquantum20-v1")=>(resident.receiving_law(),8,9),
            Some("observed-stream-pending-native-current-v1") if header.len()==8 && header[1]==crate::hnn::word::native_prediction::LAW && matches!(header[3],"fixed-lattice-v1"|"bounded-subquantum20-v1") => (resident.receiving_law(),4,5),
            Some("observed-stream-pending-v4") if header.len()==8 && header[1]=="retained-fibre-v1" && header[2]=="family-local-retained-return-v1" && header[3]=="bounded-subquantum20-v1" => (crate::hnn::receiving::ReceivingLaw::RetainedFibreV1,4,5),
            Some("observed-stream-pending-v3") if header.len()==7 && header[1]=="retained-fibre-v1" && header[2]=="family-local-retained-return-v1" => (crate::hnn::receiving::ReceivingLaw::RetainedFibreV1,3,4),
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
            "local-receiving-held-map-v1" => ObservedEpochDepositionScope::LocalReceivingReturnWithHeldMap,
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
        reuse:bool,
        flow_readings: std::sync::Mutex<Vec<crate::hnn::constitution::EpochRecordFlowReading>>,
        refuse_aggregate_at: Option<usize>,
    }

    impl CountingExecution {
        fn new(refuse_forward: bool) -> Self {
            Self {
                forwards: AtomicUsize::new(0),
                returns: AtomicUsize::new(0),
                flows: AtomicUsize::new(0),
                refuse_forward,
                reuse:true,
                flow_readings: std::sync::Mutex::new(Vec::new()),
                refuse_aggregate_at: None,
            }
        }
    }

    impl ObservedEpochExecution for CountingExecution {
        fn reuse_receiving_observations(&self)->bool { self.reuse }
        fn admit_prepared_input(&self) -> Result<(),HnnError> { HostObservedEpochExecution.admit_prepared_input() }
        fn forward_scoped(&self, context:&mut ObservedEpochForwardContext<'_,'_>, ratio:&crate::hnn::pending::PendingRatio,
            charts:&mut crate::hnn::chart::Charts, opening:&crate::hnn::word::WordOpening) -> Result<ObservedEpochForwardWord,HnnError> {
            self.forwards.fetch_add(1,Ordering::Relaxed);
            if self.refuse_forward { return Err(HnnError::ContinuingState { what:"selected stream test execution refused forward" }); }
            HostObservedEpochExecution.forward_scoped(context,ratio,charts,opening)
        }
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
            let count=self.flows.fetch_add(1, Ordering::Relaxed)+1;
            let reading=HostObservedEpochExecution.aggregate_records(
                locus,
                rows,
                columns,
                receiver_grain,
                epoch_cells,
                epoch,
                heard_cells,
                records,
            )?;
            self.flow_readings.lock().unwrap().push(reading.clone());
            if self.refuse_aggregate_at==Some(count) { return Err(HnnError::CountOverflow); }
            Ok(reading)
        }
    }

    fn opening() -> (Reference, ObservedStream, PairingDeclaration, Constitution) {
        opening_with_law(None)
    }

    fn opening_with_law(
        law: Option<crate::hnn::receiving::ReceivingLaw>,
    ) -> (Reference, ObservedStream, PairingDeclaration, Constitution) {
        opening_at_context(law,false)
    }
    pub(crate) fn opening_at_context(law:Option<crate::hnn::receiving::ReceivingLaw>,framed:bool)->(Reference,ObservedStream,PairingDeclaration,Constitution){
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
        let field=if framed{field.with_receiving_context(2,crate::hnn::receiving::ObservationPartition::SourceFramingRouteV1).unwrap()}else{field};
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
    fn source_framing_original_part_delayed_return_and_codec(){
        use crate::hnn::reference::prepared_input::{ContextChart,PrefixRole,PreparedInputState};
        use crate::compression::landmark::context::{ObservedAddress,cell_letters};
        let(reference,mut stream,pairing,_)=opening_at_context(Some(crate::hnn::receiving::ReceivingLaw::RetainedFibreV1),true);
        stream.scope=ObservedEpochDepositionScope::LocalReceivingReturnWithHeldMap;
        stream.select_source_framing_prepared_input(&pairing).unwrap();
        let receipt=stream.receive(&reference,&pairing,&[2;10]).unwrap();assert_eq!(receipt.epochs.len(),1);
        let mut input=stream.resident.prepared_input.take().unwrap();assert_eq!(input.context_chart(),ContextChart::SourceFramingRouteV1);
        let moment=stream.resident.continuing().unwrap().0;
        let cut10=input.seal(&stream.resident.field,&stream.resident.constitution,&stream.resident.current,&stream.resident.moments[&moment]).unwrap();
        let same=input.seal(&stream.resident.field,&stream.resident.constitution,&stream.resident.current,&stream.resident.moments[&moment]).unwrap();assert_eq!(cut10,same,"no future target enters source seal");
        assert_eq!(cut10.framing.unwrap().part(),2);
        reference.ingest_class_continuing(&mut stream.resident,&mut stream.crib,&pairing,2,None).unwrap();
        // Explicit CODE-only deferred scheduling of this already accepted actual return.
        input.code_defer_actual(cut10.clone(),2).unwrap();
        let cut11=input.seal(&stream.resident.field,&stream.resident.constitution,&stream.resident.current,&stream.resident.moments[&moment]).unwrap();
        assert_eq!(cut11.framing.unwrap().part(),3);assert_eq!(cut10.history,cut11.history,"same lasttwo classes at distinct actual framed positions; native h need not equal");
        let partition=crate::hnn::receiving::ObservationPartition::SourceFramingRouteV1;
        let tree=stream.resident.constitution.landmarks(2).unwrap();let depth=tree.declaration().depth;
        let a=ObservedAddress::new(partition.path(cut10.framing.unwrap().bits()).unwrap(),cell_letters(&vec![2;depth]));
        let b=ObservedAddress::new(partition.path(cut11.framing.unwrap().bits()).unwrap(),cell_letters(&vec![2;depth]));
        assert_ne!(tree.letters_observed(&a).unwrap(),tree.letters_observed(&b).unwrap());
        reference.ingest_class_continuing(&mut stream.resident,&mut stream.crib,&pairing,2,None).unwrap();input.after_actual(cut11,2).unwrap();
        let saved=input.to_text();let mut cold=PreparedInputState::from_text(&stream.resident.field,&stream.resident.constitution,&saved).unwrap();assert_eq!(cold,input);
        let before=input.material().parts().iter().map(|m|m.observations()).collect::<Vec<_>>();assert_eq!(before,vec![2,2,2,3]);
        let current=stream.resident.current.clone();let carry=stream.resident.carried.clone();
        for state in [&mut input,&mut cold]{state.form(10).unwrap();assert!(state.form(10).is_err());assert_eq!(state.material().parts().iter().map(|m|m.observations()).collect::<Vec<_>>(),vec![2,2,3,3]);}
        assert_eq!(input,cold);assert_eq!(stream.resident.current,current);assert_eq!(stream.resident.carried,carry);
        assert_eq!(input.history.last().unwrap().1,PrefixRole::Observed);
        println!("SOURCE_FRAMING_DELAYED original10/part2 current12/part0 nextpart3 before2,2,2,3 after2,2,3,3 pendingcoldexact replayrefused samecausaldifferentroute=true nativecurrentcarryunchangedbyform=true");
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
    /// Reuse the genuine ten-cell/whole-carry fixture. Synthetic retained news
    /// is explicitly declared before any candidate input, never a dataset replay.
    fn held_receiving_seeded_stream() -> (Reference,ObservedStream,PairingDeclaration,Constitution,ObservedStream) {
        use crate::hnn::receiving::ReceivingLaw;
        use num_traits::{One,Zero};
        let (reference,mut opening,pairing,initial)=opening_with_law(Some(ReceivingLaw::RetainedFibreV1));
        opening.scope=ObservedEpochDepositionScope::LocalReceivingReturn;
        opening.select_prepared_input(&pairing).unwrap();
        let original=opening.clone();
        let data:Vec<_>=(0..10).map(|i|i%4).collect();
        let executor=CountingExecution::new(false);
        let ordinary_started=std::time::Instant::now();
        let ordinary=opening.receive_with_execution(&reference,&pairing,&data,&executor).unwrap();
        println!("HELD_RECEIVING_ORDINARY_COST whole_ns={} stage_ns={:?} nativecounts10/10/1 seeded_news=false",ordinary_started.elapsed().as_nanos(),ordinary.epochs[0].wall.receiving_only_stage.map(|d|d.as_nanos()));
        let flow=executor.flow_readings.lock().unwrap()[0].clone();
        assert!(flow.covector.numerators.iter().any(|v|!v.is_zero()));
        let exponent=flow.covector.exponent.checked_add(20).unwrap();
        assert!(exponent<=256,"finite CODE fixture news scale");
        let scale=-Rat::from_integer(BigInt::one() << exponent as usize);
        let mut selected=original;
        let field=selected.resident.field.clone();let receiver=selected.resident.admitted[0].ring();
        selected.resident.constitution.code_seed_held_receiving_news(&field,receiver,&flow.covector,&scale).unwrap();
        selected.scope=ObservedEpochDepositionScope::LocalReceivingReturnWithHeldMap;
        (reference,selected,pairing,initial,opening)
    }
    #[test]
    fn held_receiving_actual_delivery_pending6_cold_and_once_only() {
        use crate::hnn::reference::prepared_input::PrefixMode;
        let (reference,mut stream,pairing,initial,baseline)=held_receiving_seeded_stream();
        let field=stream.resident.field.clone();let receiver=stream.resident.admitted[0].ring();
        let map=stream.resident.constitution.receiving_map(receiver).unwrap().clone();
        let executor=CountingExecution::new(false);
        let started=std::time::Instant::now();
        let data:Vec<_>=(0..30).map(|i|i%4).collect();
        let first=stream.receive_with_execution(&reference,&pairing,&data[..16],&executor).unwrap();
        assert_eq!((first.accepted,first.published,first.pending),(16,10,6));
        assert_eq!(first.epochs.len(),1);assert_eq!(first.epochs[0].outcome,ObservedEpochOutcome::HeldReceiving);
        assert_eq!(stream.resident.constitution.receiving_map(receiver).unwrap(),&map);
        assert_eq!(stream.resident.current,baseline.resident.current);
        assert_eq!(stream.resident.carried,baseline.resident.carried);
        assert_eq!(stream.resident.moments,baseline.resident.moments);
        assert_eq!(stream.resident.prepared_input,baseline.resident.prepared_input);
        assert_eq!(stream.crib,baseline.crib);
        let held=first.epochs[0].deposit.epoch.as_ref().unwrap().held_receiving.as_ref().unwrap();
        println!("HELD_RECEIVING_STAGING_COST stage_ns={:?} canonical_plus_independent_hold=true nativecounts10/10/1 seeded_news=true not_speedup",first.epochs[0].wall.receiving_only_stage.map(|d|d.as_nanos()));
        assert!(held.gamma>Rat::from_integer(0.into()));assert_eq!(held.crossings_after,held.crossings_before+1);
        assert_eq!(executor.forwards.load(Ordering::Relaxed),10);
        assert_eq!(executor.returns.load(Ordering::Relaxed),10);
        assert_eq!(executor.flows.load(Ordering::Relaxed),1,"held stage does not reaggregate");
        assert_eq!(stream.resident.prepared_input.as_ref().unwrap().mode(),PrefixMode::Training);
        assert_eq!(stream.resident.prepared_input.as_ref().unwrap().frontiers(),(10,0,0));
        let saved=stream.resident.continuing_state(0).unwrap();let pending=stream.pending_checkpoint();
        assert!(pending.contains("local-receiving-held-map-v1"));
        let parsed=ContinuingState::from_text(&saved.to_text(),1<<40).unwrap();
        let cold_resident=reference.mount_continued(&field,&Current::at_rest(&field),initial,&parsed).unwrap();
        let cold_crib=ObservedCrib::from_unplaced_checkpoint(&field,cold_resident.current(),10,&stream.crib.unplaced_checkpoint().unwrap()).unwrap();
        let mut cold=ObservedStream::restore_checkpoint(cold_resident,cold_crib,&pending).unwrap();
        assert_eq!(cold.scope,stream.scope);
        // No old Arrived/Word is exposed after publication. Empty delivery,
        // including cold, cannot repeat the consumed target/news/material return.
        for state in [&mut stream,&mut cold] {
            let before=state.resident.continuing_state(0).unwrap();
            let r=state.receive(&reference,&pairing,&[]).unwrap();
            assert!(r.epochs.is_empty());assert_eq!(state.resident.continuing_state(0).unwrap(),before);
        }
        let later=stream.receive_with_execution(&reference,&pairing,&data[16..],&executor).unwrap();
        let cold_later=cold.receive(&reference,&pairing,&data[16..]).unwrap();
        assert_eq!((later.accepted,later.published,later.pending),(14,20,0));
        assert_eq!(later.epochs.len(),2);assert_eq!(cold_later.epochs.len(),2);
        assert_eq!(stream.resident.continuing_state(0).unwrap(),cold.resident.continuing_state(0).unwrap());
        assert_eq!(stream.pending_checkpoint(),cold.pending_checkpoint());assert_eq!(stream.crib,cold.crib);
        assert_eq!(stream.accepted_cells().unwrap(),30);
        assert_eq!(executor.forwards.load(Ordering::Relaxed),30);assert_eq!(executor.returns.load(Ordering::Relaxed),30);assert_eq!(executor.flows.load(Ordering::Relaxed),3);
        assert_eq!(stream.resident.prepared_input.as_ref().unwrap().frontiers(),(30,0,0));
        assert!(later.epochs.iter().any(|r|r.energy.words.last().is_some_and(|_|r.closed_section)));
        println!("HELD_RECEIVING_STREAM_TRACE unique_actual30 firstaccepted16/published10/pending6 later14/20/0 warmcalls30/30/3 coldseparatebranch20/20/2 elapsed_ns={} firstdecline={:?} gamma={} work={} firstM10 finalM30 coldexact=true",started.elapsed().as_nanos(),held.original_decline.condition,held.gamma,first.epochs[0].energy.deposition_work);
    }
    #[test]
    fn held_receiving_late_delivery_execution_fault_is_atomic() {
        let (reference,mut stream,pairing,_,_)=held_receiving_seeded_stream();
        let before=stream.resident.continuing_state(0).unwrap();let pending=stream.pending_checkpoint();let crib=stream.crib.clone();
        let mut executor=CountingExecution::new(false);executor.refuse_aggregate_at=Some(2);
        let error=stream.receive_with_execution(&reference,&pairing,&(0..20).map(|i|i%4).collect::<Vec<_>>(),&executor).unwrap_err();
        assert!(matches!(error,HnnError::CountOverflow));
        assert_eq!(stream.resident.continuing_state(0).unwrap(),before);assert_eq!(stream.pending_checkpoint(),pending);assert_eq!(stream.crib,crib);
        assert_eq!(stream.accepted_cells().unwrap(),0,"a preceding staged hold is not committed on a later delivery fault");
        assert_eq!(executor.forwards.load(Ordering::Relaxed),20);assert_eq!(executor.returns.load(Ordering::Relaxed),20);assert_eq!(executor.flows.load(Ordering::Relaxed),2);
    }

    #[test]
    fn lazy_retained_connected_held_successor_cold_and_late_fault_equal() {
        let (reference,opening,pairing,initial,_)=held_receiving_seeded_stream();
        let field=opening.resident.field.clone();
        let data:Vec<_>=(0..30).map(|i|i%4).collect();
        let mut old=opening.clone();let mut new=opening.clone();
        let mut old_exec=CountingExecution::new(false);old_exec.reuse=false;
        let new_exec=CountingExecution::new(false);
        let t=std::time::Instant::now();let old_r=old.receive_with_execution(&reference,&pairing,&data[..16],&old_exec).unwrap();let old_ns=t.elapsed().as_nanos();
        let t=std::time::Instant::now();let new_r=new.receive_with_execution(&reference,&pairing,&data[..16],&new_exec).unwrap();let new_ns=t.elapsed().as_nanos();
        assert_eq!(old.resident.continuing_state(0).unwrap(),new.resident.continuing_state(0).unwrap());assert_eq!(old.crib,new.crib);assert_eq!(old.pending_checkpoint(),new.pending_checkpoint());
        assert_eq!((new_r.accepted,new_r.published,new_r.pending),(16,10,6));
        assert_eq!(old_r.epochs[0].outcome,new_r.epochs[0].outcome);assert_eq!(new_r.epochs[0].outcome,ObservedEpochOutcome::HeldReceiving);
        assert_eq!(old_r.epochs[0].energy,new_r.epochs[0].energy);
        assert_eq!(old_r.epochs[0].retained_section_return.as_ref().unwrap().source_reading(),new_r.epochs[0].retained_section_return.as_ref().unwrap().source_reading());
        assert_eq!(*old_exec.flow_readings.lock().unwrap(),*new_exec.flow_readings.lock().unwrap(),"actual full native returned rows equal");
        assert!(new_r.epochs[0].reads.iter().all(|r|r.combined.is_none() && r.scored_face.is_none()));
        for (a,b) in old_r.epochs[0].reads.iter().zip(&new_r.epochs[0].reads) { assert!(a.combined.is_some()); assert_eq!(a.scored_face.as_ref().unwrap(),&b.selected_scored_face.coarse_operands().unwrap());assert_eq!(a.code,b.code);assert_eq!(a.retained_class_return,b.retained_class_return); }
        let saved=new.resident.continuing_state(0).unwrap();
        let parsed=ContinuingState::from_text(&saved.to_text(),1<<40).unwrap();
        let resident=reference.mount_continued(&field,&Current::at_rest(&field),initial,&parsed).unwrap();
        let crib=ObservedCrib::from_unplaced_checkpoint(&field,resident.current(),10,&new.crib.unplaced_checkpoint().unwrap()).unwrap();
        let mut cold=ObservedStream::restore_checkpoint(resident,crib,&new.pending_checkpoint()).unwrap();
        for state in [&mut old,&mut new,&mut cold] { state.receive_with_execution(&reference,&pairing,&data[16..],&new_exec).unwrap(); }
        assert_eq!(old.resident.continuing_state(0).unwrap(),new.resident.continuing_state(0).unwrap());assert_eq!(cold.resident.continuing_state(0).unwrap(),new.resident.continuing_state(0).unwrap());
        assert_eq!(old.crib,new.crib);assert_eq!(cold.crib,new.crib);assert_eq!(old.pending_checkpoint(),new.pending_checkpoint());assert_eq!(cold.pending_checkpoint(),new.pending_checkpoint());
        let mut failed=opening;let before=failed.resident.continuing_state(0).unwrap();let pending=failed.pending_checkpoint();let crib=failed.crib.clone();
        let mut fault=CountingExecution::new(false);fault.refuse_aggregate_at=Some(2);
        assert!(matches!(failed.receive_with_execution(&reference,&pairing,&data[..20],&fault),Err(HnnError::CountOverflow)));
        assert_eq!(failed.resident.continuing_state(0).unwrap(),before);assert_eq!(failed.pending_checkpoint(),pending);assert_eq!(failed.crib,crib);
        println!("A19_CONNECTED actual_unique_classes30 first16/published10/pending6 host_reference_first_ns={old_ns} lazy_first_ns={new_ns} same_full_native_M_crib_pending=true held_full_flow_equal=true cold_exact=true late_fault_rollback=true diagnostics_explicitly_deferred=true old_forward_return_aggregate={}/{}/{} new_with_cold_and_later_branches={}/{}/{}",old_exec.forwards.load(Ordering::Relaxed),old_exec.returns.load(Ordering::Relaxed),old_exec.flows.load(Ordering::Relaxed),new_exec.forwards.load(Ordering::Relaxed),new_exec.returns.load(Ordering::Relaxed),new_exec.flows.load(Ordering::Relaxed));
    }

}

impl ObservedStream {
    pub fn select_native_current_prepared_input(&mut self,pairing:&PairingDeclaration)->Result<(),HnnError>{
        if !self.pending.is_empty()||self.scope!=ObservedEpochDepositionScope::LocalReceivingReturnWithHeldMap{return Err(refuse("native model selection is fresh at its one held local receiving owner"));}
        self.resident.select_native_current_prepared_input(pairing)
    }
    pub fn select_native_quadratic_work_prepared_input(&mut self,pairing:&PairingDeclaration)->Result<(),HnnError>{
        if !self.pending.is_empty()||self.scope!=ObservedEpochDepositionScope::LocalReceivingReturnWithHeldMap{return Err(refuse("native work policy selected before actual input"));}
        self.resident.select_native_quadratic_work_prepared_input(pairing)
    }
    pub fn receive_native_current(&mut self,reference:&Reference,pairing:&PairingDeclaration,classes:&[usize],bits:u32)->Result<Vec<crate::hnn::reference::native_context::NativeReceivingSectionEvent>,HnnError>{
        self.receive_native_current_diagnosed(reference,pairing,classes,bits,&mut |_|{})
    }
    pub fn receive_native_current_diagnosed(&mut self,reference:&Reference,pairing:&PairingDeclaration,classes:&[usize],bits:u32,observe:&mut dyn FnMut(&crate::hnn::reference::native_context::NativeContextEvent))->Result<Vec<crate::hnn::reference::native_context::NativeReceivingSectionEvent>,HnnError>{
        if self.resident.prepared_input.as_ref().is_none_or(|p|p.context_chart()!=prepared_input::ContextChart::LaggedReceiverBoundaryV1||p.mode()!=prepared_input::PrefixMode::Training){return Err(refuse("actual native section delivery requires its native training model"));}
        let mut next=self.clone();let mut frontier=next.pending_frontier(pairing)?;let mut sections=Vec::new();
        for &class in classes{
            if next.accepted_cells()? >= next.resident.field.population(){return Err(refuse("native input respects its declared source horizon"));}
            let boundary=PairedObservation::admit(&next.resident.field,&next.resident.constitution,pairing)?;
            let encoded=boundary.encode(&[class])?;let step=frontier.step(&next.resident.field,&encoded,0)?;
            next.pending.push(class);if next.pending.len()>next.bound{return Err(refuse("native pending remains bounded by the original physical section"));}
            if step.ticks[next.resident.admitted[0].ring()]!=0||step.carry_out{
                sections.push(reference.observe_native_current_section_diagnosed(&mut next.resident,&mut next.crib,pairing,&next.pending,bits,observe)?);
                next.pending.clear();next.bound=Self::finite_bound(&next.resident)?;frontier=next.resident.current.clone();
            }
        }
        let next=Self::restore(next.resident,next.crib,next.scope,next.pending)?;*self=next;Ok(sections)
    }
    /// Querying a native partial prefix consumes its pending cells exactly once on the private
    /// frozen fork. They are conditioning testimony, never synthetic material observations.
    pub fn native_current_query_fork(&self,reference:&Reference,pairing:&PairingDeclaration,bits:u32)->Result<(Resident,ObservedCrib),HnnError>{
        let mut resident=self.resident.clone();let mut crib=self.crib.clone();resident.freeze_prepared_forecast()?;
        for &class in &self.pending{reference.continue_native_current_forecast(&mut resident,&mut crib,pairing,class,bits)?;}
        Ok((resident,crib))
    }
}

impl ObservedStream {
    /// An actual contact-only event precedes any new R section; it cannot cross an accepted
    /// unfinished interval or silently rebind a prediction produced under earlier material.
    pub fn observe_native_current_contact(&mut self,reference:&Reference,pairing:&PairingDeclaration,class:usize,bits:u32)->Result<crate::hnn::reference::native_context::NativeContextEvent,HnnError>{
        if !self.pending.is_empty()||self.scope!=ObservedEpochDepositionScope::LocalReceivingReturnWithHeldMap{return Err(refuse("native contact publication requires its closed held-local source frontier"));}
        let mut next=self.clone();let event=reference.observe_native_current_contact(&mut next.resident,&mut next.crib,pairing,class,bits)?;
        next.bound=Self::finite_bound(&next.resident)?;let next=Self::restore(next.resident,next.crib,next.scope,next.pending)?;*self=next;Ok(event)
    }
}
