//! Native model prediction from the common Resident's actual prepared opening.
use super::*;
use std::sync::Arc;

/// Explicit execution scope; neither branch is a fallback on execution/admission failure.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum NativeExecutionChart {
    Declared,
    ExactUnsplit,
    /// Executed declared charts/splits with genuine requested paired error evidence.
    RepresentedV1,
}

/// Read-only counter domains of ONE continuing native source. The source history is
/// cumulative; the aeon-local count intentionally resets at close. Their difference
/// is the explicit cumulative origin of the current aeon, derived from the saved
/// native operands rather than a new mutable clock or a rewritten history.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct NativeSourceFrontier {
    source_cells: u64,
    aeon_cells: u64,
    aeon_origin: u64,
}
impl NativeSourceFrontier {
    pub(super) fn from_counts(source_cells:u64,aeon_cells:u64)->Result<Self,HnnError>{
        let aeon_origin=source_cells.checked_sub(aeon_cells).ok_or(HnnError::Unadmitted{
            reason:"native source history contains its complete current aeon",
        })?;
        Ok(Self{source_cells,aeon_cells,aeon_origin})
    }
    pub fn source_cells(self)->u64{self.source_cells}
    pub fn aeon_cells(self)->u64{self.aeon_cells}
    pub fn aeon_origin(self)->u64{self.aeon_origin}
    fn admit_one_ingress(self,after:Self,returned_cells:u64,closed:bool)->Result<(),HnnError>{
        let wanted=self.source_cells.checked_add(1).ok_or(HnnError::CountOverflow)?;
        let local=if closed{0}else{self.aeon_cells.checked_add(1).ok_or(HnnError::CountOverflow)?};
        let origin=if closed{wanted}else{self.aeon_origin};
        if returned_cells!=wanted||after.source_cells!=wanted||after.aeon_cells!=local||after.aeon_origin!=origin{
            return Err(HnnError::Unadmitted{reason:"native event ingests its class exactly once in matching cumulative and aeon-local domains"});
        }
        Ok(())
    }
}
impl Resident {
    /// No Word, arrival or clock mutation. Cold and warm residents read the same
    /// cumulative SourceMoment and explicit saved aeon-local state.
    pub fn native_source_frontier(&self)->Result<NativeSourceFrontier,HnnError>{
        let (id,local)=self.continuing().ok_or(HnnError::Unadmitted{reason:"one continuing native source frontier"})?;
        let source=self.moment(&id).ok_or(HnnError::Unadmitted{reason:"the continuing native source moment remains open"})?;
        NativeSourceFrontier::from_counts(source.cells(),local)
    }
}

impl Reference {
    /// One complete native Word, without q/tree/population reads or a second source ingress.
    /// The resident is borrowed until its score/draw/actual return consumes this producer.
    pub fn prepare_native_current_prediction<'a>(
        &self,
        resident: &'a Resident,
        chart: NativeExecutionChart,
        bits: u32,
    ) -> Result<crate::hnn::word::native_prediction::NativePredictionWord<'a>, HnnError> {
        self.prepare_native_current_prediction_on(resident,chart,bits,None)
    }
    /// Explicit real execution realization. No host forward fallback is selected.
    pub fn prepare_native_current_prediction_with_execution<'a>(&self,resident:&'a Resident,bits:u32,execution:&dyn crate::hnn::word::native_prediction::NativePredictionExecution)->Result<crate::hnn::word::native_prediction::NativePredictionWord<'a>,HnnError>{
        self.prepare_native_current_prediction_on(resident,NativeExecutionChart::RepresentedV1,bits,Some(execution))
    }
    fn prepare_native_current_prediction_on<'a>(&self,resident:&'a Resident,chart:NativeExecutionChart,bits:u32,execution:Option<&dyn crate::hnn::word::native_prediction::NativePredictionExecution>)->Result<crate::hnn::word::native_prediction::NativePredictionWord<'a>,HnnError>{
        resident.admit_no_participating_world()?;
        let represented=resident.prepared_input.as_ref().is_some_and(|p|p.work_receipt_policy().represented());
        if represented!=(chart==NativeExecutionChart::RepresentedV1) && (represented||chart==NativeExecutionChart::RepresentedV1){
            return Err(HnnError::Unadmitted{reason:"native represented prediction cannot switch its declared execution policy"});
        }
        if !resident.pending.is_empty() || !resident.staged.is_empty() || resident.arrived.is_some()
        {
            return Err(HnnError::Unadmitted {
                reason: "native model contact prediction needs its ordinary committed cut with no open return handles",
            });
        }
        if let Some(lag) = resident
            .prepared_input
            .as_ref()
            .and_then(|p| p.lagged.as_ref())
        {
            if resident.carried.as_ref().map(|c| c.ticks) != Some(lag.reached_tick()) {
                return Err(HnnError::Unadmitted {
                    reason: "lagged native context belongs to the actual complete carried crossing",
                });
            }
        }
        let (moment, _) = resident.continuing().ok_or(HnnError::Unadmitted {
            reason: "one native model source moment",
        })?;
        let phases = resident.admitted.first().ok_or(HnnError::Unadmitted {
            reason: "one native model receiver",
        })?;
        let field = &resident.field;
        let theta = &resident.constitution;
        let (ratio, opening, _) = self.prepare_refine(
            resident,
            &moment,
            phases,
            &crate::hnn::ring::modes::ModeView::whole(),
            field,
            theta,
        )?;
        let mut charts = resident.reception_charts();
        let mut word = match chart {
            NativeExecutionChart::Declared | NativeExecutionChart::RepresentedV1 => ratio.open_on(field, theta, &mut charts, &opening)?,
            NativeExecutionChart::ExactUnsplit => Word::open_received_view_exact(
                field,
                theta,
                &resident.current,
                ratio.moment(),
                &opening,
                ratio.view(),
            )?,
        };
        if let Some(cut) = ratio.prepared_input() {
            word = cut.apply(field, theta, &ratio, word).map_err(|source|{
                if matches!(&source,HnnError::NativePreparationRefusal{..}){
                    HnnError::NativePreparationRefusal{evidence:resident.prepared_input.as_ref().expect("same admitted input owner").native_refusal_reading(cut),source:Box::new(source)}
                }else{source}
            })?;
        } else {
            word.bind_source_producer(theta, &resident.current, Arc::new(ratio.moment().clone()))?;
        }
        if chart==NativeExecutionChart::RepresentedV1 {word.request_response_error_evidence();}
        let receiver = field
            .receivers()
            .iter()
            .position(|r| r.ring == phases.ring())
            .ok_or(HnnError::MissingReceivingMap {
                ring: phases.ring(),
            })?;
        let declaration=word.declare_native_prediction(receiver,&mut resident.native_rank.lock())?;
        let predictor=if let Some(execution)=execution{
            let record=execution.forward_native(field,theta,&ratio,&mut charts,&opening,declaration.phases())?;
            declaration.read_external(word,record,bits)?
        }else{declaration.run_and_read(word,bits)?};
        Ok(predictor.with_prepared_cut(ratio.prepared_input().cloned()).with_charts(charts))
    }
}

/// Inspection of one actual event. Contact-only is explicit; this does not claim an R-only
/// epoch consumer, CUDA execution or a native-language command has been joined.
pub struct NativeContextEvent {
    pub prediction: crate::hnn::word::native_prediction::NativePredictionReading,
    pub scores: Vec<crate::ratio::algebraic::ExactInterval>,
    pub forward: WordBalance,
    pub preparation: Option<crate::hnn::word::action::PortPreparationReceipt>,
    pub contact: Option<crate::hnn::word::native_prediction::NativeContactPublication>,
    pub input: observed::IngestClassReceipt,
    pub selected_class: usize,
    pub draw: Option<crate::receiver::release::ReleaseReturn>,
    /// The native contact ladder, on an event that publishes contact material.
    pub reread: Option<NativeRereadReceipt>,
}
impl Resident {
    pub(crate) fn native_context_chart(&self) -> Result<Option<Encoded>, HnnError> {
        let Some(p) = self.prepared_input.as_ref().filter(|p| {
            p.context_chart() == prepared_input::ContextChart::LaggedReceiverBoundaryV1
        }) else {
            return Ok(None);
        };
        let pairing = crate::hnn::paired::PairingDeclaration::Family {
            table: p.pairs.clone(),
        };
        let chart = crate::hnn::encoding::observed::PairedObservation::admit(
            &self.field,
            &self.constitution,
            &pairing,
        )?
        .encode(&[])?;
        Ok(Some(chart))
    }
}
impl Reference {
    /// A declared contact-only actual event at a closed native cut. It consumes ONE new
    /// exterior class after its prediction. It cannot certify an aggregate of older openings.
    pub fn observe_native_current_contact(
        &self,
        resident: &mut Resident,
        crib: &mut observed::ObservedCrib,
        pairing: &crate::hnn::paired::PairingDeclaration,
        class: usize,
        bits: u32,
    ) -> Result<NativeContextEvent, HnnError> {
        self.native_current_event(
            resident,
            crib,
            pairing,
            NativeInput::Class(class),
            bits,
            true,
            true,
            None,
        )
    }
    /// Explicit causal-control arm: consume the same actual native target return,
    /// actual ingress and original M/lag formation, withholding only contact material
    /// publication. No output policy/controller selects this arm implicitly.
    pub fn observe_native_current_without_contact_material(&self,resident:&mut Resident,crib:&mut observed::ObservedCrib,pairing:&crate::hnn::paired::PairingDeclaration,class:usize,bits:u32)->Result<NativeContextEvent,HnnError>{
        self.native_current_event(resident,crib,pairing,NativeInput::Class(class),bits,true,false,None)
    }
    /// Same F/prefix computation on a frozen forecast fork. The chosen class is a hypothesis,
    /// not a material-forming observation. Contact, receiving and M moments remain fixed.
    pub fn continue_native_current_forecast(
        &self,
        resident: &mut Resident,
        crib: &mut observed::ObservedCrib,
        pairing: &crate::hnn::paired::PairingDeclaration,
        class: usize,
        bits: u32,
    ) -> Result<NativeContextEvent, HnnError> {
        self.native_current_event(
            resident,
            crib,
            pairing,
            NativeInput::Class(class),
            bits,
            false,
            false,
            None,
        )
    }
    /// Actual original contact return through an explicitly selected realization.
    pub fn observe_native_current_contact_with_execution(&self,resident:&mut Resident,crib:&mut observed::ObservedCrib,pairing:&crate::hnn::paired::PairingDeclaration,class:usize,bits:u32,execution:&dyn crate::hnn::word::native_prediction::NativePredictionExecution)->Result<NativeContextEvent,HnnError>{
        self.native_current_event(resident,crib,pairing,NativeInput::Class(class),bits,true,true,Some(execution))
    }
    pub fn continue_native_current_forecast_with_execution(&self,resident:&mut Resident,crib:&mut observed::ObservedCrib,pairing:&crate::hnn::paired::PairingDeclaration,class:usize,bits:u32,execution:&dyn crate::hnn::word::native_prediction::NativePredictionExecution)->Result<NativeContextEvent,HnnError>{
        self.native_current_event(resident,crib,pairing,NativeInput::Class(class),bits,false,false,Some(execution))
    }
    fn native_current_event(
        &self,
        resident: &mut Resident,
        crib: &mut observed::ObservedCrib,
        pairing: &crate::hnn::paired::PairingDeclaration,
        choice: NativeInput<'_>,
        bits: u32,
        actual: bool,
        publish_contact: bool,
        execution:Option<&dyn crate::hnn::word::native_prediction::NativePredictionExecution>,
    ) -> Result<NativeContextEvent, HnnError> {
        let mut next = resident.clone();
        let mut next_crib = crib.clone();
        let input = next.prepared_input.as_ref().ok_or(HnnError::Unadmitted {
            reason: "native prediction needs its explicit fresh context owner",
        })?;
        if input.context_chart() != prepared_input::ContextChart::LaggedReceiverBoundaryV1
            || actual != (input.mode() == prepared_input::PrefixMode::Training)
        {
            return Err(HnnError::Unadmitted {
                reason: "native event keeps explicit observed versus frozen hypothetical lineage",
            });
        }
        let source_frontier = next.native_source_frontier()?;
        let boundary = crate::hnn::encoding::observed::PairedObservation::admit(
            &next.field,
            &next.constitution,
            pairing,
        )?;
        if boundary.immutable_identity_text() != input.boundary_identity {
            return Err(HnnError::Unadmitted {
                reason: "native event uses its unchanged original input chart",
            });
        }
        if let NativeInput::Class(class) = &choice {
            boundary.encode(&[*class])?;
        }
        let chart = boundary.encode(&[])?;
        let chart_policy=if next.prepared_input.as_ref().is_some_and(|p|p.work_receipt_policy().represented()){NativeExecutionChart::RepresentedV1}else{NativeExecutionChart::ExactUnsplit};
        let predictor=if let Some(execution)=execution{self.prepare_native_current_prediction_with_execution(&next,bits,execution)?}else{self.prepare_native_current_prediction(
            &next,
            chart_policy,
            bits,
        )?};
        let draw = match choice {
            NativeInput::Class(_) => None,
            NativeInput::Key(key) => Some(predictor.draw(0, key)?),
        };
        let class =
            match choice {
                NativeInput::Class(c) => c,
                NativeInput::Key(_) => draw.as_ref().and_then(|d| d.drawn_class()).ok_or(
                    HnnError::Unadmitted {
                        reason: "native CDF retains an unresolved key without hypothesis ingress",
                    },
                )?,
            };
        let target = boundary.encode(&[class])?;
        let prepared = predictor
            .prepared_cut()
            .cloned()
            .ok_or(HnnError::Unadmitted {
                reason: "one kept original native preparation cut",
            })?;
        let prediction = predictor.reading();
        let role = if actual {
            prepared_input::PrefixRole::Observed
        } else {
            input.forecast_role
        };
        let lag = predictor.lagged_boundary(role)?;
        let (carry, forward, preparation) = predictor.forward_receipt()?;
        let reached_charts=predictor.prepared_charts().cloned().unwrap_or_else(||next.reception_charts());
        let mut reread = None;
        let (scores, contact, material, carry, charts) = if actual && publish_contact {
            let returned = predictor.observe(&target)?;
            let scores = returned.scores().to_vec();
            let mut charts = reached_charts;
            let receipt = self.native_contact_reread(&next, &returned, &prediction, &target, chart_policy, bits, execution)?;
            let published = returned.publish_contact_carry_at(&mut charts, receipt.admitted)?;
            reread = Some(receipt);
            (scores, Some(published), None, None, charts)
        } else {
            let scores=if actual {let returned=predictor.observe(&target)?;returned.scores().to_vec()}else{let scores=predictor.score(&target)?;drop(predictor);scores};
            (
                scores,
                None,
                Some(next.constitution.clone()),
                Some(carry),
                reached_charts,
            )
        };
        let (material, carry) = match &contact {
            Some(p) => (p.constitution.clone(), p.carry.clone()),
            None => (
                material.expect("frozen material"),
                carry.expect("executed carry"),
            ),
        };
        let point = crate::holon::HolonState {
            commit: material.commit(),
            configuration: carry,
        };
        next.publish_reception(Some(material), point, Some(charts), None, &chart)?;
        let ingested =
            self.ingest_class_continuing(&mut next, &mut next_crib, pairing, class, None)?;
        source_frontier.admit_one_ingress(next.native_source_frontier()?,ingested.cells,ingested.close.is_some())?;
        let input = next.prepared_input.as_mut().expect("same material owner");
        if actual {
            input.after_actual(prepared, class)?;
        } else {
            input.after_forecast(class)?;
        }
        input.install_reached_lag(lag)?;
        *resident = next;
        *crib = next_crib;
        Ok(NativeContextEvent {
            prediction,
            scores,
            forward,
            preparation,
            contact,
            input: ingested,
            selected_class: class,
            draw,
            reread,
        })
    }

    /// [definition; agent-inferred, October 22; the plan's §16] **The native contact step is
    /// certified by rereading the same comparison.** The a priori curvature envelope of the
    /// represented contact route (`C = ½·response²`, about `2^42` on the Athena fixture) sized every
    /// step at `2^-52..2^-37`, below the factors' fine unit, so nothing moved. Here each candidate
    /// of the native ladder (`NativePredictionReturn::reread_ladder`: the covector-scale start, then
    /// halvings) is read by the same prediction: the same opening, source, prepared input, frame,
    /// receiver and target, entered through the candidate material. It is admitted only on
    /// [`decide`]'s exact strict improvement of that comparison (code and phase excess), with the
    /// code enclosures refined to the face's finest grain when they overlap. The first admitted
    /// halving is published; with none, the certified step is published as before. The represented
    /// first-variation enclosure is read beside each candidate (`first_variation_refused`) and is
    /// not a gate on a reread candidate: its error charges exceed the stored pairing on the
    /// fixture, where the exact reread still certifies a strict decrease.
    ///
    /// [`decide`]: crate::hnn::word::continuation::decide
    #[allow(clippy::too_many_arguments)]
    fn native_contact_reread(
        &self,
        resident: &Resident,
        returned: &crate::hnn::word::native_prediction::NativePredictionReturn,
        prediction: &crate::hnn::word::native_prediction::NativePredictionReading,
        target: &Encoded,
        chart: NativeExecutionChart,
        bits: u32,
        execution: Option<&dyn crate::hnn::word::native_prediction::NativePredictionExecution>,
    ) -> Result<NativeRereadReceipt, HnnError> {
        use crate::hnn::word::continuation::decide;
        use crate::hnn::word::native_prediction::native_objective;
        const FINEST: u32 = 128;
        let field = &resident.field;
        let lift = resident.current.lift().to_vec();
        let ring = prediction.receiver;
        let (before, excess) = native_objective(field, &lift, ring, &prediction.waves, target, bits)?;
        let mut receipt = NativeRereadReceipt {
            before: before.clone(),
            excess: excess.clone(),
            trials: Vec::new(),
            admitted: None,
        };
        let mut judge = |halvings: u32, theta: &crate::hnn::constitution::Constitution, refused: bool| -> Result<bool, HnnError> {
            let mut fork = resident.clone();
            fork.constitution = theta.clone();
            let waves = {
                let read = match execution {
                    Some(execution) => self.prepare_native_current_prediction_with_execution(&fork, bits, execution)?,
                    None => self.prepare_native_current_prediction(&fork, chart, bits)?,
                };
                read.reading().waves
            };
            let witness = waves == prediction.waves;
            let (mut after, after_excess) = native_objective(field, &lift, ring, &waves, target, bits)?;
            let mut reading_bits = bits;
            let mut decision = decide(&before, &excess, &after, &after_excess, witness);
            if bits < FINEST
                && matches!(
                    decision,
                    Err(crate::hnn::word::continuation::AdmissionRefusal::Overlap
                        | crate::hnn::word::continuation::AdmissionRefusal::EqualEndpoints)
                )
            {
                let (fine_before, _) = native_objective(field, &lift, ring, &prediction.waves, target, FINEST)?;
                let (fine_after, _) = native_objective(field, &lift, ring, &waves, target, FINEST)?;
                decision = decide(&fine_before, &excess, &fine_after, &after_excess, witness);
                after = fine_after;
                reading_bits = FINEST;
            }
            let admitted = decision.is_ok();
            receipt.trials.push(NativeRereadTrial {
                halvings,
                reading: Some(NativeRereadReading { after, excess: after_excess, reading_bits, decision }),
                first_variation_refused: refused,
            });
            Ok(admitted)
        };
        let admitted = returned.reread_ladder(&mut judge)?;
        receipt.admitted = admitted;
        Ok(receipt)
    }
}

/// [definition; agent-inferred, October 22] The native contact ladder as read: the producing
/// comparison's code and phase excess, each candidate's reread, and the halving published.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeRereadReceipt {
    pub before: crate::ratio::algebraic::ExactInterval,
    pub excess: Rat,
    pub trials: Vec<NativeRereadTrial>,
    /// The first admitted halving of the covector-scale start; `None` publishes the certified step,
    /// which keeps its first-variation gate.
    pub admitted: Option<u32>,
}

/// One candidate of the ladder.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeRereadTrial {
    pub halvings: u32,
    /// The candidate's reread.
    pub reading: Option<NativeRereadReading>,
    /// The represented first-variation enclosure could not certify this candidate's direction. It
    /// is a reading beside the reread, not a gate: the exact strict decrease certifies the step.
    pub first_variation_refused: bool,
}

/// The candidate's comparison at its opening: its code at `reading_bits`, its phase excess, and the
/// exact decision against the producing comparison.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativeRereadReading {
    pub after: crate::ratio::algebraic::ExactInterval,
    pub excess: Rat,
    pub reading_bits: u32,
    pub decision: Result<crate::hnn::word::continuation::Admitted, crate::hnn::word::continuation::AdmissionRefusal>,
}

/// Private and single-use: the last actual return has reached its original Word,
/// but its source ingress cannot advance Current until R publication at that cut.
struct NativeFinalArrival {
    prepared: prepared_input::PreparedInputCut,
    lag: prepared_input::LaggedReceiverBoundary,
    prediction: crate::hnn::word::native_prediction::NativePredictionReading,
    scores: Vec<crate::ratio::algebraic::ExactInterval>,
    forward: WordBalance,
    preparation: Option<crate::hnn::word::action::PortPreparationReceipt>,
    class: usize,
}
impl NativeFinalArrival {
    fn admit_original(&self,resident:&Resident)->Result<(),HnnError>{
        let source=resident.native_source_frontier()?.source_cells();
        if source!=self.prepared.source_cells || source!=self.prediction.source_cells
            || self.prepared.commit!=resident.constitution.commit()
            || self.prepared.commit!=self.prediction.producing_commit
            || self.prepared.lift!=resident.current.lift()
            || self.lag.produced_source_cells()!=source {
            return Err(HnnError::Unadmitted{reason:"the final native arrival retains its original Word/cut/lag before R publication"});
        }Ok(())
    }
}

/// One physical receiver barrier. Only NEW actual inputs after the preceding contact cut
/// enter this R-only section. No old prediction is rebound and no C/K/D step is staged.
pub struct NativeReceivingSectionEvent {
    pub events: Vec<NativeContextEvent>,
    pub publication: crate::hnn::constitution::DepositReading,
    pub start_source: u64,
    pub end_source: u64,
    pub declared_section_cells: u64,
    pub contact_prefix_cells: u64,
    /// Actual original Word cut at which the R-only successor was published.
    pub publication_source: u64,
    pub original_final_commit: u64,
    pub receiving_commit: u64,
    pub blind_carry_preserved: bool,
    pub aeon_closed: bool,
}
impl Reference {
    pub fn observe_native_current_section(
        &self,
        resident: &mut Resident,
        crib: &mut observed::ObservedCrib,
        pairing: &crate::hnn::paired::PairingDeclaration,
        classes: &[usize],
        bits: u32,
    ) -> Result<NativeReceivingSectionEvent, HnnError> {
        self.observe_native_current_section_diagnosed(resident,crib,pairing,classes,bits,&mut |_|{})
    }
    pub fn observe_native_current_section_diagnosed(&self,resident:&mut Resident,crib:&mut observed::ObservedCrib,pairing:&crate::hnn::paired::PairingDeclaration,classes:&[usize],bits:u32,observe:&mut dyn FnMut(&NativeContextEvent))->Result<NativeReceivingSectionEvent,HnnError>{
        use crate::hnn::constitution::{
            Locus,
            epoch::{ObservedNormalEpochStage, partition_exponent},
        };
        let mut next = resident.clone();
        let mut next_crib = crib.clone();
        next.admit_exact_current()?;
        let original_frontier=next.native_source_frontier()?;
        let start=original_frontier.source_cells();
        let receiver = next
            .admitted
            .first()
            .ok_or(HnnError::Unadmitted {
                reason: "one native receiver section",
            })?
            .ring();
        let width = next.field.rings()[..receiver]
            .iter()
            .try_fold(1u64, |n, r| {
                n.checked_mul(r.period()).ok_or(HnnError::CountOverflow)
            })?;
        // Physical scheduling remains aeon-local; publication identities and the
        // retained-statistic crossing index remain cumulative across close.
        let remainder = original_frontier.aeon_cells() % width;
        let wanted = width - remainder;
        if classes.len() as u64 != wanted {
            return Err(HnnError::Unadmitted {
                reason: "native R consumes exactly the NEW suffix to the original physical receiver barrier",
            });
        }
        if next.prepared_input.as_ref().is_none_or(|p| {
            p.context_chart() != prepared_input::ContextChart::LaggedReceiverBoundaryV1
                || p.mode() != prepared_input::PrefixMode::Training
        }) {
            return Err(HnnError::Unadmitted {
                reason: "native R is an actual-input consequence of its versioned native model",
            });
        }
        let mut packets = Vec::new();
        let mut events = Vec::new();
        let producing = next.constitution.clone();
        let mut final_arrival = None;
        for (station,&class) in classes.iter().enumerate() {
            let boundary = crate::hnn::encoding::observed::PairedObservation::admit(
                &next.field,
                &next.constitution,
                pairing,
            )?;
            let target = boundary.encode(&[class])?;
            let chart = boundary.encode(&[])?;
            let predictor = self.prepare_native_current_prediction(
                &next,
                if next.prepared_input.as_ref().is_some_and(|p|p.work_receipt_policy().represented()){NativeExecutionChart::RepresentedV1}else{NativeExecutionChart::ExactUnsplit},
                bits,
            )?;
            let prepared = predictor
                .prepared_cut()
                .cloned()
                .ok_or(HnnError::Unadmitted {
                    reason: "the actual native R Word keeps its original preparation",
                })?;
            let lag = predictor.lagged_boundary(prepared_input::PrefixRole::Observed)?;
            let (carry, forward, preparation) = predictor.forward_receipt()?;
            let prediction = predictor.reading();
            let reached_charts=predictor.prepared_charts().cloned();
            let returned = predictor.observe(&target)?;
            let scores = returned.scores().to_vec();
            packets.push(returned.into_receiving_packet()?);
            next.publish_reception(
                None,
                crate::holon::HolonState {
                    commit: next.constitution.commit(),
                    configuration: carry,
                },
                reached_charts,
                None,
                &chart,
            )?;
            if station+1==classes.len(){
                let arrival=NativeFinalArrival{prepared,lag,prediction,scores,forward,preparation,class};
                arrival.admit_original(&next)?;
                final_arrival=Some(arrival);
                break;
            }
            let input =
                self.ingest_class_step_deferred(&mut next, &mut next_crib, pairing, class, None)?;
            let owner = next
                .prepared_input
                .as_mut()
                .expect("same native context owner");
            owner.after_actual(prepared, class)?;
            owner.install_reached_lag(lag)?;
            if next.constitution != producing {
                return Err(HnnError::Unadmitted {
                    reason: "no material commit can rebind the native R section's earlier predictions",
                });
            }
            let event=NativeContextEvent {
                prediction,
                scores,
                forward,
                preparation,
                contact: None,
                input,
                selected_class: class,
                draw: None,
                reread: None,
            };observe(&event);events.push(event);
        }
        let final_arrival=final_arrival.ok_or(HnnError::Unadmitted{reason:"one actual final returned arrival per native section"})?;
        final_arrival.admit_original(&next)?;
        if next.constitution!=producing{return Err(HnnError::Unadmitted{reason:"all native section packets keep the same original material"});}
        let (_, deposits, records) =
            crate::hnn::word::native_prediction::NativeRPacket::section(packets)?;
        let tree = producing
            .landmarks(receiver)
            .ok_or(HnnError::Unadmitted {
                reason: "the native R publication retains its existing unused legacy tree",
            })?
            .clone();
        let retained = std::iter::once(Locus::ReceivingMap(receiver)).collect();
        let period = next.field.ring(receiver).period();
        // ArrivalContext has two block crossing counters, not a Single-law counter.
        // The actual original source frontier owns this physical receiver section.
        let index = start / width;
        let exponent = partition_exponent(producing.observed_epoch_grain(receiver)?, width, index)?;
        let pair_speed = |_a: usize,
                          _b: usize,
                          _p: &crate::hnn::moment::PairPort,
                          _m: [&[Vec<Rat>]; 3]|
         -> Result<[Rat; 2], HnnError> {
            Err(HnnError::Unadmitted {
                reason: "native R-only publication cannot request a source pair update",
            })
        };
        let execution = crate::hnn::reference::observed::HostObservedEpochExecution;
        let mut stage = ObservedNormalEpochStage::new(
            &producing,
            &deposits,
            receiver,
            period,
            wanted,
            width,
            index,
            exponent,
            &retained,
            tree,
            &pair_speed,
            &records,
            &execution,
            false,
        )?
        .for_local_receiving_hold()?;
        let candidate = stage
            .stage_local_receiving_with_hold(&mut |_| {})
            .map_err(|f| HnnError::NativeEpochRefusal{source:Box::new(f.error),evidence:Box::new(f.evidence)})?;
        let (material, publication) = candidate.admit_receiving()?;
        let chart = next.native_context_chart()?.ok_or(HnnError::Unadmitted {
            reason: "native section retains its original input chart",
        })?;
        let carry = next.carried.clone().ok_or(HnnError::Unadmitted {
            reason: "native R publishes after its actual blind carried endpoint",
        })?;
        let publication_frontier=next.native_source_frontier()?;
        let publication_source=publication_frontier.source_cells();
        let original_final_commit=final_arrival.prediction.producing_commit;
        let receiving_commit=material.commit();
        let original_carry=carry.clone();
        next.publish_receiving_translation(
            material.clone(),
            crate::holon::HolonState {
                commit: material.commit(),
                configuration: carry,
            },
            &chart,
        )?;
        if next.carried.as_ref()!=Some(&original_carry) || next.native_source_frontier()?!=publication_frontier{return Err(HnnError::Unadmitted{reason:"R-only publication preserves its original full blind carry and pre-ingress source frontier"});}
        // The genuine new boundary is admitted against the R successor. Nothing
        // rewrites the original prediction, prepared material cut, target or lag.
        let NativeFinalArrival{prepared,lag,prediction,scores,forward,preparation,class}=final_arrival;
        let input=self.ingest_class_step_deferred(&mut next,&mut next_crib,pairing,class,None)?;
        let owner=next.prepared_input.as_mut().expect("same native context owner");
        owner.after_actual(prepared,class)?;
        owner.install_reached_lag(lag)?;
        let final_event=NativeContextEvent{prediction,scores,forward,preparation,contact:None,input,selected_class:class,draw:None,reread:None};
        observe(&final_event);events.push(final_event);
        let final_frontier=next.native_source_frontier()?;
        let end=final_frontier.source_cells();
        if end != start.checked_add(wanted).ok_or(HnnError::CountOverflow)? || end % width != 0 {
            return Err(HnnError::Unadmitted {
                reason: "native R closes the original section without replay, flush or target omission",
            });
        }
        let aeon_closed=next.aeon.awaiting;
        if aeon_closed {
            self.close_deferred_native_input(&mut next, &mut next_crib, pairing)?;
            let closed=next.native_source_frontier()?;
            if closed.source_cells()!=end||closed.aeon_cells()!=0||closed.aeon_origin()!=end{
                return Err(HnnError::Unadmitted{reason:"native aeon close preserves cumulative source history and advances only its aeon origin"});
            }
        }
        *resident = next;
        *crib = next_crib;
        Ok(NativeReceivingSectionEvent {
            events,
            publication,
            start_source: start,
            end_source: end,
            declared_section_cells: width,
            contact_prefix_cells: remainder,
            publication_source,
            original_final_commit,
            receiving_commit,
            blind_carry_preserved: true,
            aeon_closed,
        })
    }
}

#[derive(Clone, Copy)]
enum NativeInput<'a> {
    Class(usize),
    Key(&'a Rat),
}
impl Reference {
    /// The one F producer draws, scores and advances its actual frozen hypothesis prefix.
    pub fn release_native_current_forecast(
        &self,
        resident: &mut Resident,
        crib: &mut observed::ObservedCrib,
        pairing: &crate::hnn::paired::PairingDeclaration,
        key: &Rat,
        bits: u32,
    ) -> Result<NativeContextEvent, HnnError> {
        if resident
            .prepared_input
            .as_ref()
            .is_none_or(|p| p.forecast_role != prepared_input::PrefixRole::Hypothesized)
        {
            return Err(HnnError::Unadmitted {
                reason: "native release is explicitly hypothetical after frozen conditioning",
            });
        }
        self.native_current_event(resident, crib, pairing, NativeInput::Key(key), bits, false, false,None)
    }
}

impl Resident{pub fn native_rank_reuse_reading(&self)->(u64,u64){let c=self.native_rank.lock();(c.hits,c.misses)}}

#[cfg(test)]
mod frontier_tests {
    use super::*;
    #[test]
    fn native_source_counter_domains_preserve_history_and_origins(){
        for origin in [0,30,60,90,30000] {
            let before=NativeSourceFrontier::from_counts(origin,0).unwrap();
            let after=NativeSourceFrontier::from_counts(origin+1,1).unwrap();
            before.admit_one_ingress(after,origin+1,false).unwrap();
            assert_eq!(after.aeon_origin(),origin);
            if origin>0{assert!(before.admit_one_ingress(after,1,false).is_err());}
            let before_close=NativeSourceFrontier::from_counts(origin+29,29).unwrap();
            let after_close=NativeSourceFrontier::from_counts(origin+30,0).unwrap();
            before_close.admit_one_ingress(after_close,origin+30,true).unwrap();
            assert!(before_close.admit_one_ingress(after_close,origin+30,false).is_err());
            assert!(before.admit_one_ingress(NativeSourceFrontier::from_counts(origin+1,0).unwrap(),origin+1,false).is_err());
        }
        assert!(NativeSourceFrontier::from_counts(1,2).is_err());
        assert!(NativeSourceFrontier::from_counts(u64::MAX,0).unwrap().admit_one_ingress(NativeSourceFrontier::from_counts(0,0).unwrap(),0,true).is_err());
    }
}
