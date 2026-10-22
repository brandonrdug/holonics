//! Actual observed-epoch execution through the existing resident card word.
//!
//! A single actor owns its CUDA context and retained words. Its public handle is
//! Send + Sync without moving any Card, Rc, device buffer or context between
//! threads. The opaque observed word names the very forward record consumed by
//! its reverse; dropping a rejected/unconsumed handle retires that record.
//! Source moments and reception openings are uploaded from the shared native
//! owner on each forward. Immutable material/publication and its checked chart
//! store are shared only within that owner's actual batch scope. Faces,
//! certificates, composition and publication remain exact host phases. This is
//! an explicit hybrid observed executor.

use std::fmt;
use num_traits::Zero;
use std::sync::{Arc, Weak, Mutex, mpsc};

use holonics::hnn::constitution::{EpochProducerRecordReading, EpochRecordFlowReading};
use holonics::hnn::reference::observed::{
    ObservedEpochExecution, ObservedEpochForwardContext, ObservedEpochForwardWord,
    ObservedEpochWord,
};
use holonics::hnn::ring::TubePassage;
use holonics::hnn::{RatioCovector, Released, Word};
use holonics::ratio::linear::ExactRatMatrix;

use super::*;

fn unavailable() -> HnnError {
    HnnError::Unadmitted {
        reason: "the selected CUDA observed executor is unavailable; no native fallback is selected",
    }
}

use holonics::hnn::word::native_prediction::{NativePredictionExecution,NativeExecutedPrediction,NativeExecutedPath,NativeExecutedReturn};

type Reply<T> = mpsc::Sender<Result<T, HnnError>>;

enum Request {
    Forward {
        field: Box<Field>,
        constitution: Box<Constitution>,
        ratio: Box<PendingRatio>,
        charts: Charts,
        opening: Box<WordOpening>,
        scope: Option<Arc<()>>,
        force_error_evidence: bool,
        native_phases:Option<ReceivingPhases>,
        validate_error_reference: bool,
        reply: Reply<ForwardReading>,
    },
    Return {
        id: u64,
        covector: RatioCovector,
        map: ExactRatMatrix,
        phases: ReceivingPhases,
        reply: Reply<WordReturn>,
    },
    Aggregate {
        rows: usize,
        columns: usize,
        grain: u32,
        epoch_cells: u64,
        epoch: u64,
        heard_cells: u64,
        records: Vec<EpochProducerRecordReading>,
        reply: Reply<EpochRecordFlowReading>,
    },
    Retire(u64),
}

struct NativeForwardParts{operands:holonics::hnn::propagation::Operands,actual:NativeExecutedPath,fresh:NativeExecutedPath}
struct ForwardReading {
    native:Option<NativeForwardParts>,
    source_preparation: Option<holonics::hnn::word::action::PortPreparationReceipt>,
    id: u64,
    producing_commit: u64,
    charts: Charts,
    readings: Vec<ChartReading>,
    faces: Faces,
    anchors: Vec<Vec<Rat>>,
    reception_end: ReceptionCarry,
    released: Released,
    passages: Vec<TubePassage>,
}

/// Scoped realization counters; no law or checkpoint consumes them. Subset counts
/// are identified explicitly, not added to their totals. No global sync census.
#[derive(Clone,Copy,Debug,Default)]
pub struct ObservedDeviceReading {
    pub successful_forwards:u64,
    pub successful_returns:u64,
    pub native_dispatch_attempts:u64,
    pub native_full_tick_forwards:u64,
    pub native_full_tick_returns:u64,
    pub native_reverse_launches:u64,
    pub fresh_response_reverse_subset:u64,
    pub source_preparation_packets:u64,
    pub source_preparation_host_ns:u128,
    pub mounted_execute_ns:u128,
    pub response_operands_host_ns:u128,
    pub forward_shared_setup_ns:u128,
    pub fresh_path_ns:u128,
    pub fresh_error_trace_ns:u128,
    pub actual_path_ns:u128,
    pub actual_error_trace_ns:u128,
    pub response_error_trace_calls:u64,
    pub response_error_reference_calls:u64,
    pub response_error_reference_ns:u128,
    pub native_word_forward_launches:u64,
    pub fresh_response_forward_subset:u64,
    pub forward_phase_transfer_octets:u64,
    pub response_forward_transfer_subset_octets:u64,
}

struct Client {
    reading:Arc<Mutex<ObservedDeviceReading>>,
    sender: Option<mpsc::Sender<Request>>,
    worker: Option<std::thread::JoinHandle<()>>,
}

impl Client {
    fn send(&self, request: Request) -> Result<(), HnnError> {
        self.sender
            .as_ref()
            .ok_or_else(unavailable)?
            .send(request)
            .map_err(|_| unavailable())
    }
}

impl Drop for Client {
    fn drop(&mut self) {
        // Closing the final sender drains queued retirement messages, then the
        // actor drops every word and its card before this owner returns.
        drop(self.sender.take());
        if let Some(worker) = self.worker.take() {
            let _ = worker.join();
        }
    }
}

/// An explicitly selected CUDA observed executor. Its one ordered actor owns the
/// context; callers and parallel return workers exchange owned native operands.
#[derive(Clone)]
pub struct ObservedEpochDevice {
    client: Arc<Client>,
    force_error_evidence: bool,
    validate_error_reference: bool,
}

impl fmt::Debug for ObservedEpochDevice {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ObservedEpochDevice")
            .finish_non_exhaustive()
    }
}

impl ObservedEpochDevice {
    /// Open and verify the selected card inside its owning actor. Failure is
    /// returned before this executor can be selected by an observed passage.
    pub fn open(ordinal: i32) -> Result<Self, HnnError> {
        let (sender, receiver) = mpsc::channel();
        let reading=Arc::new(Mutex::new(ObservedDeviceReading::default()));
        let actor_reading=Arc::clone(&reading);
        let (ready_tx, ready_rx) = mpsc::channel();
        let worker = std::thread::Builder::new()
            .name("hnn-observed-card".into())
            .spawn(move || actor(ordinal, receiver, ready_tx,actor_reading))
            .map_err(|_| unavailable())?;
        match ready_rx.recv().map_err(|_| unavailable()) {
            Ok(Ok(())) => Ok(Self {
                force_error_evidence: false,
                validate_error_reference: false,
                client: Arc::new(Client {
                    reading,
                    sender: Some(sender),
                    worker: Some(worker),
                }),
            }),
            failure => {
                drop(sender);
                let _ = worker.join();
                match failure {
                    Ok(Err(error)) | Err(error) => Err(error),
                    Ok(Ok(())) => unreachable!(),
                }
            }
        }
    }

    /// Explicit report request; does not alter material or prediction policy.
    pub fn with_response_error_evidence(mut self)->Self {self.force_error_evidence=true;self}
    /// Explicit CODE reference check on the SAME retained records, not another forward.
    pub fn with_response_error_reference_validation(mut self)->Self {self.force_error_evidence=true;self.validate_error_reference=true;self}
    pub fn realization_reading(&self)->ObservedDeviceReading{*self.client.reading.lock().unwrap_or_else(|e|e.into_inner())}

    fn forward_reading(
        &self,
        field: &Field,
        constitution: &Constitution,
        ratio: &PendingRatio,
        charts: &Charts,
        opening: &WordOpening,
        scope: Option<Arc<()>>,
        native_phases:Option<ReceivingPhases>,
    ) -> Result<ForwardReading, HnnError> {
        let (reply, result) = mpsc::channel();
        if native_phases.is_some(){self.client.reading.lock().unwrap_or_else(|e|e.into_inner()).native_dispatch_attempts+=2;}
        self.client
            .send(Request::Forward {
                field: Box::new(field.clone()),
                constitution: Box::new(constitution.clone()),
                ratio: Box::new(ratio.clone()),
                charts: charts.clone(),
                opening: Box::new(opening.clone()),
                scope,
                force_error_evidence: self.force_error_evidence||native_phases.is_some(),
                native_phases,
                validate_error_reference:self.validate_error_reference,
                reply,
            })
            .map_err(|_| unavailable())?;
        result.recv().map_err(|_| unavailable())?
    }
}

struct DeviceWord {
    id: Option<u64>,
    client: Arc<Client>,
    readings: Vec<ChartReading>,
    passages: Vec<TubePassage>,
}

impl fmt::Debug for DeviceWord {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("ObservedCardWord")
            .field("id", &self.id)
            .finish()
    }
}

impl Drop for DeviceWord {
    fn drop(&mut self) {
        if let Some(id) = self.id.take() {
            // A discarded transaction or a failed later forward releases its
            // earlier producing records without an adjoint or any publication.
            let _ = self.client.send(Request::Retire(id));
        }
    }
}

impl ObservedEpochWord for DeviceWord {
    fn charts(&self) -> Vec<ChartReading> {
        self.readings.clone()
    }

    fn tube_passages(&self) -> Result<Vec<TubePassage>, HnnError> {
        Ok(self.passages.clone())
    }

    fn return_at(
        mut self: Box<Self>,
        _field: &Field,
        _execution: &dyn ObservedEpochExecution,
        covector: &RatioCovector,
        map: &ExactRatMatrix,
        phases: &ReceivingPhases,
    ) -> Result<WordReturn, HnnError> {
        let id = self.id.take().ok_or_else(unavailable)?;
        let (reply, result) = mpsc::channel();
        self.client
            .send(Request::Return {
                id,
                covector: covector.clone(),
                map: map.clone(),
                phases: phases.clone(),
                reply,
            })
            .map_err(|_| unavailable())?;
        result.recv().map_err(|_| unavailable())?
    }
}

impl ObservedEpochDevice {
    fn forward_on_scope(
        &self,
        field: &Field,
        constitution: &Constitution,
        ratio: &PendingRatio,
        charts: &mut Charts,
        opening: &WordOpening,
        scope: Option<Arc<()>>,
    ) -> Result<ObservedEpochForwardWord, HnnError> {
        let reading = self.forward_reading(field, constitution, ratio, charts, opening, scope,None)?;
        *charts = reading.charts;
        Ok(ObservedEpochForwardWord {
            source_preparation: reading.source_preparation,
            forward_span: None,
            producing_commit: reading.producing_commit,
            word: Box::new(DeviceWord {
                id: Some(reading.id),
                client: Arc::clone(&self.client),
                readings: reading.readings,
                passages: reading.passages,
            }),
            faces: reading.faces,
            anchors: reading.anchors,
            reception_end: reading.reception_end,
            released: reading.released,
        })
    }
}

impl NativeExecutedReturn for DeviceWord {
    fn return_native(mut self:Box<Self>,covector:&RatioCovector,map:&ExactRatMatrix,phases:&ReceivingPhases)->Result<WordReturn,HnnError>{
        let id=self.id.take().ok_or_else(unavailable)?;let(reply,result)=mpsc::channel();
        self.client.reading.lock().unwrap_or_else(|e|e.into_inner()).native_dispatch_attempts+=2;
        self.client.send(Request::Return{id,covector:covector.clone(),map:map.clone(),phases:phases.clone(),reply})?;
        result.recv().map_err(|_|unavailable())?
    }
}
impl NativePredictionExecution for ObservedEpochDevice{
    fn attempted_native_operations(&self)->u64{self.realization_reading().native_dispatch_attempts}
    fn forward_native(&self,field:&Field,constitution:&Constitution,ratio:&PendingRatio,charts:&mut Charts,opening:&WordOpening,phases:&ReceivingPhases)->Result<NativeExecutedPrediction,HnnError>{
        let reading=self.forward_reading(field,constitution,ratio,charts,opening,None,Some(phases.clone()))?;
        *charts=reading.charts;let native=reading.native.ok_or_else(unavailable)?;
        Ok(NativeExecutedPrediction{operands:native.operands,actual:native.actual,fresh:native.fresh,reception_end:reading.reception_end,released:reading.released,source_preparation:reading.source_preparation,
            returned:Box::new(DeviceWord{id:Some(reading.id),client:self.client.clone(),readings:reading.readings,passages:reading.passages})})
    }
}

impl ObservedEpochExecution for ObservedEpochDevice {
    fn admit_prepared_input(&self)->Result<(),HnnError>{Ok(())}
    fn forward(
        &self,
        field: &Field,
        constitution: &Constitution,
        ratio: &PendingRatio,
        charts: &mut Charts,
        opening: &WordOpening,
    ) -> Result<ObservedEpochForwardWord, HnnError> {
        self.forward_on_scope(field, constitution, ratio, charts, opening, None)
    }

    fn forward_scoped(
        &self,
        context: &mut ObservedEpochForwardContext<'_, '_>,
        ratio: &PendingRatio,
        charts: &mut Charts,
        opening: &WordOpening,
    ) -> Result<ObservedEpochForwardWord, HnnError> {
        let scope = context.scope_token();
        self.forward_on_scope(
            context.field(),
            context.constitution(),
            ratio,
            charts,
            opening,
            Some(scope),
        )
    }

    fn pull_back(
        &self,
        _word: Word<'_>,
        _covector: &RatioCovector,
        _map: &ExactRatMatrix,
        _phases: &ReceivingPhases,
    ) -> Result<WordReturn, HnnError> {
        Err(HnnError::Unadmitted {
            reason: "the CUDA observed executor returns only its own retained card forward record",
        })
    }

    #[allow(clippy::too_many_arguments)]
    fn aggregate_records(
        &self,
        _locus: LinearLocus,
        rows: usize,
        columns: usize,
        receiver_grain: u32,
        epoch_cells: u64,
        epoch: u64,
        heard_cells: u64,
        records: &[EpochProducerRecordReading],
    ) -> Result<EpochRecordFlowReading, HnnError> {
        let (reply, result) = mpsc::channel();
        self.client
            .send(Request::Aggregate {
                rows,
                columns,
                grain: receiver_grain,
                epoch_cells,
                epoch,
                heard_cells,
                records: records.to_vec(),
                reply,
            })
            .map_err(|_| unavailable())?;
        result.recv().map_err(|_| unavailable())?
    }
}

struct RetainedWord<'c> {
    word: ExecutedWord<'c>,
    field: Field,
    phases: ReceivingPhases,
    map: ExactRatMatrix,
    native:bool,
}

/// Read the same displacement series as native `Word::tube_passages`, directly
/// from this word's verified CUDA forward record. The publication's cached
/// resonator operands are precisely those consumed when its WordPlan was formed;
/// this reads no replacement native trajectory and seeds no new solve.
fn executed_tube_passages(
    word: &ExecutedWord<'_>,
    field: &Field,
) -> Result<Vec<TubePassage>, HnnError> {
    let plan = &word.word.plan;
    let record = &word.word.record;
    let operands = word.word.publication.loci.resonator_operands(field)?;
    let mut passages = Vec::new();
    for (ring, operands) in operands.iter().enumerate() {
        let Some(operands) = operands.as_ref().filter(|operands| operands.reads_tube()) else {
            continue;
        };
        let refuse = || HnnError::Resonator {
            ring,
            what: "the CUDA tube passage requires every actual pre-tick and final displacement of its producing word",
        };
        let loaded = plan
            .resonators
            .iter()
            .find(|loaded| loaded.ring == ring)
            .ok_or_else(refuse)?;
        if loaded.width != operands.width()
            || loaded.phases != operands.phases()
            || loaded.saturation.is_none()
            || loaded
                .rows
                .checked_add(loaded.width)
                .is_none_or(|end| end > plan.n)
        {
            return Err(refuse());
        }
        let full_ticks = plan.steps.checked_sub(1).ok_or_else(refuse)?;
        let mut displacements = Vec::with_capacity(full_ticks.saturating_add(1));
        for tick in 0..full_ticks {
            let start = tick
                .checked_mul(plan.n)
                .and_then(|start| start.checked_add(loaded.rows))
                .ok_or_else(refuse)?;
            let end = start.checked_add(loaded.width).ok_or_else(refuse)?;
            let values = record.resonator_u.get(start..end).ok_or_else(refuse)?;
            displacements.push(
                values
                    .iter()
                    .map(|&value| crate::hnn::dyadic::value(BigInt::from(value), plan.lw))
                    .collect::<Vec<_>>(),
            );
        }
        let end = loaded.rows.checked_add(loaded.width).ok_or_else(refuse)?;
        let values = record
            .resonator_final_u
            .get(loaded.rows..end)
            .ok_or_else(refuse)?;
        displacements.push(
            values
                .iter()
                .map(|&value| crate::hnn::dyadic::value(BigInt::from(value), plan.lw))
                .collect::<Vec<_>>(),
        );
        passages.push(operands.passage(displacements.iter().map(Vec::as_slice))?);
    }
    // Empty is justified only by the actual publication's lack of eligible
    // resonator operands, never by an absent or malformed device record.
    Ok(passages)
}

/// Validate the already admitted phase operand without running a new rank
/// experiment at contemporary material. Rank and depth belong to its declaring
/// receiver, exactly as on the shared native observed path.
fn admit_observed_phases(field: &Field, phases: &ReceivingPhases) -> Result<(), HnnError> {
    let refuse = || HnnError::Unadmitted {
        reason: "the observed execution phases are a declared receiving restriction of this field",
    };
    let Some(ring) = field.rings().get(phases.ring()) else {
        return Err(refuse());
    };
    let rows = ring
        .width()
        .checked_mul(phases.aperture())
        .ok_or(HnnError::CountOverflow)?;
    let columns = field.sources().iter().try_fold(0usize, |width, &source| {
        width
            .checked_add(field.ring(source).width())
            .ok_or(HnnError::CountOverflow)
    })?;
    if phases.aperture() == 0
        || phases
            .first_epoch()
            .checked_add(phases.aperture())
            .is_none()
        || field.first_epoch(phases.ring()) != Some(phases.first_epoch())
        || phases.grain() != holonics::hnn::field::receiver_grain(phases.tolerance())?
        || phases.rank() < phases.aperture()
        || phases.rank() > rows.min(columns)
        || phases.observation_partition() != field.receiving_context(phases.ring())
    {
        return Err(refuse());
    }
    for receiver in field.receivers() {
        if receiver.ring == phases.ring()
            && phases.aperture() <= receiver.aperture
            && phases.grain() == holonics::hnn::field::receiver_grain(&receiver.tolerance)?
        {
            return Ok(());
        }
    }
    Err(refuse())
}

/// This mounted value is only an execution facade. Its current, address, ledger,
/// pending handles and tree are never consulted by `Mounted::execute`; the actual
/// current, moment and opening are supplied by each pending ratio. Only the
/// immutable field/material/publication and the checked chart store are reused.
struct ScopedMount<'c> {
    scope: Weak<()>,
    mounted: Mounted<'c>,
    charts: Charts,
}

#[allow(clippy::too_many_arguments)]
fn prepare_observed_mount<'c>(
    card: &'c Card,
    mounts: &mut Vec<ScopedMount<'c>>,
    scope: Option<&Arc<()>>,
    field: &Field,
    constitution: &Constitution,
    current: &Current,
    phases: &ReceivingPhases,
    charts: &Charts,
) -> Result<ScopedMount<'c>, HnnError> {
    admit_observed_phases(field, phases)?;
    charts.validate_for(field)?;
    let key = scope.map(Arc::downgrade);
    if let Some(key) = &key {
        if let Some(at) = mounts.iter().position(|mount| mount.scope.ptr_eq(key)) {
            // Remove before work: any failure discards the mutable device facade.
            // A later attempt must restore its actual supplied native chart operand.
            let mut mount = mounts.swap_remove(at);
            if mount.mounted.field != *field || mount.mounted.constitution != *constitution {
                return Err(HnnError::Unadmitted {
                    reason: "an observed execution scope preserves its immutable field and constitution",
                });
            }
            let preparation = mount.mounted.store.ring_preparations();
            if mount.charts != *charts {
                mount.mounted.store = ChartStore::continued(card, field, charts)?;
                mount.charts = charts.clone();
            }
            if let Some(preparation) = preparation {
                mount.mounted.store.reuse_ring_preparations(preparation);
            }
            return Ok(mount);
        }
    }
    let port = Resident::new(card, 1, constitution.budget());
    // These are the shared native owner's actual admitted phases, validated
    // above. Re-declaring observability here would add a new admission experiment
    // and one exact host basis word per source coordinate to every device word.
    let mut mounted = port.mount_with_family(
        field,
        current,
        constitution.clone(),
        Some(vec![phases.clone()]),
    )?;
    mounted.store = ChartStore::continued(card, field, charts)?;
    Ok(ScopedMount {
        scope: key.unwrap_or_default(),
        mounted,
        charts: charts.clone(),
    })
}

fn actor(ordinal: i32, receiver: mpsc::Receiver<Request>, ready: Reply<()>, realization:Arc<Mutex<ObservedDeviceReading>>) {
    // No context, module, stream or device pointer crosses this thread boundary.
    let card = match Card::open(ordinal) {
        Ok(card) => card,
        Err(error) => {
            let _ = ready.send(Err(device(error)));
            return;
        }
    };
    if ready.send(Ok(())).is_err() {
        return;
    }
    let mut words = BTreeMap::new();
    let mut next = 0u64;
    let mut mounts = Vec::new();
    while let Ok(request) = receiver.recv() {
        // A proof cannot extend its native immutable batch's lifetime. A request
        // owns its token until reply; an expired batch is retired at this boundary.
        mounts.retain(|mount: &ScopedMount<'_>| mount.scope.strong_count() != 0);
        match request {
            Request::Forward {
                field,
                constitution,
                ratio,
                charts,
                opening,
                scope,
                force_error_evidence,
                native_phases,
                validate_error_reference,
                reply,
            } => {
                let result = (|| {
                    let id = next;
                    next = next.checked_add(1).ok_or(HnnError::CountOverflow)?;
                    let current = ratio.current(&field)?;
                    if ratio.commit() != constitution.commit() {
                        return Err(HnnError::Unadmitted {
                            reason: "the observed execution ratio binds its producing constitution commit",
                        });
                    }
                    let mut mounted_scope = prepare_observed_mount(
                        &card,
                        &mut mounts,
                        scope.as_ref(),
                        &field,
                        &constitution,
                        &current,
                        native_phases.as_ref().unwrap_or_else(||ratio.phases()),
                        &charts,
                    )?;
                    let mounted = &mut mounted_scope.mounted;
                    let moment = ResidentMoment::restored(&card, &field, &current, ratio.moment())
                        .map_err(device)?
                        .snapshot()
                        .map_err(device)?;
                    let opening = match *opening {
                        WordOpening::Rest => CardOpening::Rest,
                        WordOpening::Received { carry, absorption } => CardOpening::Received {
                            carry: Rc::new(CardCarry::restored(&card, &field, carry)?),
                            absorption,
                        },
                    };
                    let publication = Rc::clone(&mounted.publication);
                    let traffic_before=mounted.traffic();let execute_started=std::time::Instant::now();
                    let (word, faces, active) =
                        if native_phases.is_some(){mounted.execute_with_native_ticks(&ratio,&moment,&publication,&card,&opening,true,validate_error_reference,native_phases.as_ref())?}else if force_error_evidence {mounted.execute_with_response_evidence(&ratio,&moment,&publication,&card,&opening,true,validate_error_reference)?} else { mounted.execute(&ratio, &moment, &publication, &card, &opening)? };
                    let execute_ns=execute_started.elapsed().as_nanos();let traffic_after=mounted.traffic();
                    {
                        let mut m=realization.lock().unwrap_or_else(|e|e.into_inner());
                        m.successful_forwards+=1;m.native_full_tick_forwards+=u64::from(native_phases.is_some());
                        m.source_preparation_packets+=u64::from(word.source_preparation.is_some());
                        m.source_preparation_host_ns+=word.source_preparation_host_ns;
                        m.mounted_execute_ns+=execute_ns;
                        m.response_operands_host_ns+=word.response_operands_host_ns;
                        m.forward_shared_setup_ns+=word.word.forward_cost.shared_setup_ns;
                        m.fresh_path_ns+=word.word.forward_cost.fresh_path_ns;
                        m.fresh_error_trace_ns+=word.word.forward_cost.fresh_error_trace_ns;
                        m.actual_path_ns+=word.word.forward_cost.actual_path_ns;
                        m.actual_error_trace_ns+=word.word.forward_cost.actual_error_trace_ns;
                        m.response_error_trace_calls+=word.word.forward_cost.response_error_trace_calls;
                        m.response_error_reference_calls+=word.word.forward_cost.response_error_reference_calls;
                        m.response_error_reference_ns+=word.word.forward_cost.response_error_reference_ns;
                        m.native_word_forward_launches+=traffic_after.word_count-traffic_before.word_count;
                        m.fresh_response_forward_subset+=traffic_after.response_word_count-traffic_before.response_word_count;
                        m.forward_phase_transfer_octets+=traffic_after.words-traffic_before.words;
                        m.response_forward_transfer_subset_octets+=traffic_after.response_words-traffic_before.response_words;
                    }
                    let anchors = readout::anchors(&word.word.plan, &word.word.record);
                    let reception_end =
                        CardCarry::ended(&word.word, opening.ticks(), Absorption::Nothing)?.host;
                    let executed = Executed {
                        contacts: word
                            .operators
                            .iter()
                            .map(|op| (&op.operator, &op.norm))
                            .collect(),
                        readings: &word.readings,
                    };
                    let released=if native_phases.is_some(){readout::released_native(&word.word.plan,&active.loci,&word.word.record,&executed,word.word.response_producing_operands().ok_or_else(unavailable)?)?}else{readout::released(&word.word.plan,&active.loci,&word.word.record,&executed)?};
                    let native=if let Some(native_phases)=&native_phases{
                        let full=native_phases.junction_steps();
                        let operands=word.word.response_producing_operands().ok_or_else(unavailable)?.clone();
                        let actual=readout::native_path(&word.word.plan,word.word.native_actual_record().ok_or_else(unavailable)?,word.word.response_actual_opening())?;
                        let (fp,fr)=word.word.response_plan_record().ok_or_else(unavailable)?;
                        let fresh=readout::native_path(fp,fr,None)?;
                        if released.balances.len()!=full{return Err(unavailable());}
                        if released.end!=reception_end.change||released.ticks!=full{return Err(unavailable());}
                        Some(NativeForwardParts{operands,actual,fresh})
                    }else{None};
                    let passages = executed_tube_passages(&word, &field)?;
                    let map = mounted
                        .constitution
                        .receiving_map(ratio.phases().ring())
                        .ok_or(HnnError::MissingReceivingMap {
                            ring: ratio.phases().ring(),
                        })?
                        .clone();
                    let exported_charts = mounted.store.continuing_charts()?;
                    let reading = ForwardReading {
                        native,
                        source_preparation: word.source_preparation.clone(),
                        id,
                        producing_commit: ratio.commit(),
                        charts: exported_charts.clone(),
                        readings: word.readings.clone(),
                        faces,
                        anchors,
                        reception_end,
                        released,
                        passages,
                    };
                    // Only a successful verified export becomes the next reuse
                    // operand. The scope owns no source, target or word history.
                    mounted_scope.charts = exported_charts;
                    if scope.is_some() {
                        mounts.push(mounted_scope);
                    }
                    words.insert(
                        id,
                        RetainedWord {
                            word,
                            field: *field,
                            phases: native_phases.as_ref().unwrap_or_else(||ratio.phases()).clone(),
                            map,
                            native:native_phases.is_some(),
                        },
                    );
                    Ok(reading)
                })();
                // A vanished caller cannot leave an unreachable record behind.
                if let Err(mpsc::SendError(Ok(reading))) = reply.send(result) {
                    words.remove(&reading.id);
                }
            }
            Request::Return {
                id,
                covector,
                map,
                phases,
                reply,
            } => {
                let result = (|| {
                    let mut retained = words.remove(&id).ok_or_else(unavailable)?;
                    if retained.map != map || retained.phases != phases {
                        return Err(HnnError::Unadmitted {
                            reason: "the observed return preserves its producing map and receiving phases",
                        });
                    }
                    let back=pull_back_word(&retained.field, &mut retained.word, &covector, &phases)?;
                    {let mut m=realization.lock().unwrap_or_else(|e|e.into_inner());m.successful_returns+=1;m.native_reverse_launches+=if retained.word.word.response_plan_record().is_some(){2}else{1};m.fresh_response_reverse_subset+=u64::from(retained.word.word.response_plan_record().is_some());m.native_full_tick_returns+=u64::from(retained.native);}
                    Ok(back)
                })();
                let _ = reply.send(result);
            }
            Request::Aggregate {
                rows,
                columns,
                grain,
                epoch_cells,
                epoch,
                heard_cells,
                records,
                reply,
            } => {
                let result = card
                    .aggregate_epoch_records(
                        rows,
                        columns,
                        grain,
                        epoch_cells,
                        epoch,
                        heard_cells,
                        &records,
                    )
                    .map(|execution| execution.flow)
                    .map_err(device);
                let _ = reply.send(result);
            }
            Request::Retire(id) => {
                words.remove(&id);
            }
        }
    }
    // The map drops before its borrowed card. Failed transactions publish nothing.
}

#[cfg(test)]
mod tests {
    use super::*;
    use holonics::geometry::RatVec3;
    use holonics::geometry::screw::ScrewGenerator;
    use holonics::hnn::field::{CribDeclaration, ReceiverDeclaration};
    use holonics::hnn::paired::{PairedCarrier, PairingDeclaration};
    use holonics::hnn::reference::observed::ObservedCrib;
    use holonics::hnn::{ContactDeclaration, FieldDeclaration, RingDeclaration};
    use holonics::ratio::{integer, rat};

    fn ring(period: u64, lock: Vec<u64>) -> RingDeclaration {
        RingDeclaration {
            period,
            screw: ScrewGenerator::new(RatVec3::from_i64(0, 0, 1), RatVec3::zero()),
            placements: (0..period)
                .map(|node| FieldDeclaration::quarter_turn(node, period))
                .collect(),
            lock,
            reflector: (0..period)
                .map(|p| ((period - p) % period) as usize)
                .collect(),
            admittance: integer(2),
            initial: 0,
        }
    }

    // The native observed epoch fixture, including the same symmetric source
    // prior. Its next fixed-medium read after the first section reaches the
    // lawful Contact(0,-98) operator at D=2^101, L_c=30, S=131.
    fn opening() -> (
        holonics::hnn::Reference,
        holonics::hnn::reference::Resident,
        ObservedCrib,
        PairingDeclaration,
    ) {
        let contact = |from, to, exponent| ContactDeclaration {
            from,
            to,
            channel: vec![(0, 0), (1, 1)],
            admittance: integer(2),
            exponent: integer(exponent),
        };
        let field = Field::declare(
            FieldDeclaration {
                founded: Vec::new(),
                founding: false,
                rings: vec![ring(4, vec![0, 2]), ring(3, vec![0]), ring(3, vec![])],
                contacts: vec![contact(0, 1, 2), contact(1, 2, 0)],
                loops: Vec::new(),
                sources: vec![0],
                offsets: vec![1],
                alphabet: 4,
                step: integer(1),
                exponent_grain: 1,
                receivers: vec![ReceiverDeclaration {
                    ring: 2,
                    aperture: 1,
                    tolerance: rat(1, 16),
                    depth: 2,
                    prior: holonics::compression::landmark::context::StopPrior::half(),
                    mass: 1,
                    base: holonics::compression::landmark::context::BaseMeasure::Even,
                    receiving_prior: 0,
                }],
                crib: CribDeclaration {
                    window: 16,
                    offset: 1,
                },
                population: 1 << 16,
                lattice: Default::default(),
            }
            .by_lattice_rule(),
        )
        .unwrap();
        let pairing = PairingDeclaration::Family {
            table: vec![(0, 1), (1, 0), (2, 3), (3, 2)],
        };
        let free = ExactRatMatrix::shaped(
            8,
            4,
            (0..8)
                .map(|row| {
                    (0..4)
                        .map(|column| {
                            if (row == 2 && column == 0) || (row == 3 && column == 2) {
                                rat(1, 32)
                            } else {
                                integer(0)
                            }
                        })
                        .collect()
                })
                .collect(),
        )
        .unwrap();
        let source = PairedCarrier::complete_port(&field, 0, &pairing, &free).unwrap();
        let carrier = PairedCarrier::admit(&field, 0, &pairing, &source).unwrap();
        let constitution = Constitution::initial(&field, 1 << 40)
            .unwrap()
            .with_symmetric_source(0, source, carrier.symmetry())
            .unwrap();
        let reference = holonics::hnn::Reference::new(16, 1 << 40);
        let resident = reference
            .mount_with(&field, &Current::at_rest(&field), constitution)
            .unwrap();
        (reference, resident, ObservedCrib::new(0), pairing)
    }

    #[test]
    fn observed_facade_admits_held_phases_and_rejects_another_declared_family() {
        let (_, resident, _, _) = opening();
        let phases = &resident.admitted()[0];
        admit_observed_phases(resident.field(), phases).unwrap();
        let mut declaration = resident.field().declaration().clone();
        declaration.receivers[0].tolerance = rat(1, 8);
        declaration.lattice.clear();
        let different = Field::declare(declaration.by_lattice_rule()).unwrap();
        assert!(admit_observed_phases(&different, phases).is_err());
        let mut declaration = resident.field().declaration().clone();
        declaration.receivers[0].ring = 0;
        declaration.lattice.clear();
        let different = Field::declare(declaration.by_lattice_rule()).unwrap();
        assert!(admit_observed_phases(&different, phases).is_err());
    }

    fn execute_prepared<'c>(
        mount: &mut ScopedMount<'c>,
        card: &'c Card,
        ratio: &PendingRatio,
    ) -> (ExecutedWord<'c>, Faces) {
        let current = ratio.current(&mount.mounted.field).unwrap();
        let moment = ResidentMoment::restored(card, &mount.mounted.field, &current, ratio.moment())
            .unwrap()
            .snapshot()
            .unwrap();
        let publication = Rc::clone(&mount.mounted.publication);
        let (word, faces, _) = mount
            .mounted
            .execute(ratio, &moment, &publication, card, &CardOpening::Rest)
            .unwrap();
        mount.charts = mount.mounted.store.continuing_charts().unwrap();
        (word, faces)
    }

    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn actual_scoped_mount_reuses_publication_reconciles_charts_and_refuses_rebinding() {
        let card = Card::open(0).unwrap();
        let (_, resident, _, _) = opening();
        let (field, constitution, current, phases) = (
            resident.field(),
            resident.constitution(),
            resident.current(),
            &resident.admitted()[0],
        );
        let moment = SourceMoment::open(field, current);
        let ratio = PendingRatio::produce(
            current,
            &moment,
            resident.address(),
            phases,
            constitution.commit(),
        )
        .unwrap();
        let token = Arc::new(());
        let mut mounts = Vec::new();
        let empty = Charts::new();
        let mut first = prepare_observed_mount(
            &card,
            &mut mounts,
            Some(&token),
            field,
            constitution,
            current,
            phases,
            &empty,
        )
        .unwrap();
        let publication = Rc::clone(&first.mounted.publication);
        let (first_word, first_faces) = execute_prepared(&mut first, &card, &ratio);
        assert!(
            executed_tube_passages(&first_word, field)
                .unwrap()
                .is_empty(),
            "the actual unsaturated publication has no eligible tube passage"
        );
        let verified = first.charts.clone();
        mounts.push(first);
        let mut reused = prepare_observed_mount(
            &card,
            &mut mounts,
            Some(&token),
            field,
            constitution,
            current,
            phases,
            &verified,
        )
        .unwrap();
        assert!(Rc::ptr_eq(&publication, &reused.mounted.publication));
        let (reused_word, reused_faces) = execute_prepared(&mut reused, &card, &ratio);
        assert_eq!(reused_faces, first_faces);
        assert!(
            reused_word
                .readings
                .iter()
                .filter(|read| matches!(read.key, ChartKey::Ring(_)))
                .all(
                    |read| read.start == holonics::hnn::chart::ChartStart::Reused
                        && read.steps == 0
                )
        );
        assert_eq!(
            first_word.word.record.logits,
            reused_word.word.record.logits
        );
        mounts.push(reused);

        // A supplied changed chart operand must replace the device store. It
        // cannot inherit a proof whose input ring charts are absent now.
        let mut reset = prepare_observed_mount(
            &card,
            &mut mounts,
            Some(&token),
            field,
            constitution,
            current,
            phases,
            &empty,
        )
        .unwrap();
        assert!(Rc::ptr_eq(&publication, &reset.mounted.publication));
        let (reset_word, reset_faces) = execute_prepared(&mut reset, &card, &ratio);
        assert_eq!(reset_faces, first_faces);
        assert!(
            reset_word
                .readings
                .iter()
                .filter(|read| matches!(read.key, ChartKey::Ring(_)))
                .all(|read| read.start == holonics::hnn::chart::ChartStart::Transpose)
        );
        let verified = reset.charts.clone();
        mounts.push(reset);

        // A new authenticated batch has its own publication and starts from the
        // supplied charts. Equal material never manufactures scoped provenance.
        let other_token = Arc::new(());
        let mut other = prepare_observed_mount(
            &card,
            &mut mounts,
            Some(&other_token),
            field,
            constitution,
            current,
            phases,
            &verified,
        )
        .unwrap();
        assert!(!Rc::ptr_eq(&publication, &other.mounted.publication));
        let (other_word, other_faces) = execute_prepared(&mut other, &card, &ratio);
        assert_eq!(other_faces, first_faces);
        assert!(
            other_word
                .readings
                .iter()
                .filter(|read| matches!(read.key, ChartKey::Ring(_)))
                .all(|read| read.start != holonics::hnn::chart::ChartStart::Reused)
        );
        mounts.push(other);

        let changed = Constitution::initial(field, constitution.budget()).unwrap();
        assert_ne!(&changed, constitution);
        assert!(
            prepare_observed_mount(
                &card,
                &mut mounts,
                Some(&other_token),
                field,
                &changed,
                current,
                phases,
                &verified,
            )
            .is_err()
        );
        let malformed = Charts::from_entries([(
            ChartKey::Ring(0),
            holonics::hnn::chart::ChartWords::of_coordinates(
                1,
                1,
                field.word_lattice().unwrap().chart_exponent(),
                &[BigInt::from(0)],
            )
            .unwrap(),
        )])
        .unwrap();
        assert!(
            prepare_observed_mount(
                &card,
                &mut mounts,
                Some(&token),
                field,
                constitution,
                current,
                phases,
                &malformed,
            )
            .is_err()
        );
    }

    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn actual_observed_pump_tube_passages_read_card_displacements_and_refuse_missing_records() {
        use holonics::hnn::port::ExecutionPort;
        use holonics::hnn::reference::observed::HostObservedEpochExecution;
        use holonics::hnn::ring::{PumpDeclaration, PumpStep, ResonatorMaterial, TubeCentre};
        let card = Card::open(0).unwrap();
        let (reference, mut resident, _, pairing) = opening();
        let field = resident.field().clone();
        let boundary = holonics::hnn::encoding::observed::PairedObservation::admit(
            &field,
            resident.constitution(),
            &pairing,
        )
        .unwrap();
        let (moment, _) = reference
            .ingest(&mut resident, None, &boundary.encode(&[1]).unwrap())
            .unwrap();
        let width = field.ring(0).width();
        let material = ResonatorMaterial::new(
            ExactRatMatrix::identity(width)
                .unwrap()
                .scaled(&integer(16)),
            ExactRatMatrix::zero(width, width).unwrap(),
            ExactRatMatrix::zero(width, width).unwrap(),
            Some(
                PumpDeclaration::new(
                    rat(1, 8),
                    holonics::holon::parametron::Carrier::new(integer(1), integer(0)).unwrap(),
                    PumpStep::Stand,
                )
                .unwrap(),
            ),
        )
        .unwrap()
        .with_symmetric_saturation(rat(1, 65536))
        .unwrap();
        let constitution = resident
            .constitution()
            .clone()
            .with_ring_resonator(&field, 0, material)
            .unwrap();
        let phases = &resident.admitted()[0];
        let ratio = PendingRatio::produce(
            resident.current(),
            resident.moment(&moment).unwrap(),
            resident.address(),
            phases,
            constitution.commit(),
        )
        .unwrap();
        let native = HostObservedEpochExecution
            .forward(
                &field,
                &constitution,
                &ratio,
                &mut Charts::new(),
                &WordOpening::Rest,
            )
            .unwrap();
        let expected = native.word.tube_passages().unwrap();
        assert!(!expected.is_empty());
        assert!(expected.iter().any(|passage| {
            passage
                .distance(TubeCentre::Origin)
                .is_some_and(|distance| distance > &integer(0))
        }));
        let mut mount = prepare_observed_mount(
            &card,
            &mut Vec::new(),
            None,
            &field,
            &constitution,
            resident.current(),
            phases,
            &Charts::new(),
        )
        .unwrap();
        let (mut executed, _) = execute_prepared(&mut mount, &card, &ratio);
        assert_eq!(executed_tube_passages(&executed, &field).unwrap(), expected);
        let complete = executed.word.record.clone();
        executed.word.record.resonator_final_u.clear();
        assert!(matches!(
            executed_tube_passages(&executed, &field),
            Err(HnnError::Resonator { ring: 0, .. })
        ));
        executed.word.record = complete;
        executed.word.record.resonator_u.clear();
        assert!(matches!(
            executed_tube_passages(&executed, &field),
            Err(HnnError::Resonator { ring: 0, .. })
        ));
    }

    #[test]
    #[ignore = "needs the CUDA card; run alone with --include-ignored --test-threads=1"]
    fn actual_observed_card_words_returns_and_grouped_deposits_match_native_s131_sections() {
        let execution = ObservedEpochDevice::open(0).unwrap();
        let (reference, mut host, mut host_crib, pairing) = opening();
        let mut device = host.clone();
        let mut device_crib = host_crib.clone();
        for section in 0..2 {
            let expected = reference
                .observe_epoch_continuing_at_cuts(
                    &mut host,
                    &mut host_crib,
                    &pairing,
                    &[0; 32],
                    None,
                    &[],
                    false,
                )
                .unwrap();
            let actual = reference
                .observe_epoch_continuing_at_cuts_with_execution(
                    &mut device,
                    &mut device_crib,
                    &pairing,
                    &[0; 32],
                    None,
                    &[],
                    false,
                    &execution,
                )
                .unwrap();
            assert_eq!(actual.consumed, expected.consumed, "section {section}");
            assert_eq!(actual.comparison_commit, expected.comparison_commit);
            assert_eq!(actual.partition_exponent, expected.partition_exponent);
            assert_eq!(actual.reads, expected.reads);
            assert_eq!(actual.deposit, expected.deposit);
            assert_eq!(actual.precision, expected.precision);
            assert_eq!(device.constitution(), host.constitution());
            assert_eq!(device.current(), host.current());
            assert_eq!(device.carried(), host.carried());
            assert_eq!(device.charts(), host.charts());
            assert_eq!(device_crib, host_crib);
            assert_eq!(
                device.continuing_state(0).unwrap().to_text(),
                host.continuing_state(0).unwrap().to_text()
            );
        }
        // Last owner drop joins the actor after every retained word is retired.
        drop(execution);
    }
}
