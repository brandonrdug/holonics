//! One source-bound native predictive receiver. Scoring, draw and return borrow ONE face.
//! The legacy tree/mixture is neither a constructor operand nor a selected fallback here.
use super::*;
use crate::hnn::receiving::RetainedStationReturn;
use crate::hnn::receiving::native_current::NativeCurrentFace;
use crate::ratio::algebraic::ExactInterval;
use crate::receiver::release::ReleaseReturn;
use num_bigint::BigInt;
use num_traits::One;

pub const LAW: &str = "native-current-prediction-v1";
pub use super::material_ray::PhysicalRayReading as NativePhysicalRayReading;

/// Consumes the actual Word; callers cannot construct a face, change the predictor or rebind y.
pub struct NativePredictionWord<'a> {
    word: Word<'a>,
    prepared: Option<crate::hnn::reference::prepared_input::PreparedInputCut>,
    charts:Option<Charts>,
    phases: ReceivingPhases,
    map: ExactRatMatrix,
    faces: Vec<NativeCurrentFace>,
    features: Vec<Vec<Rat>>,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NativePredictionReading {
    pub law: &'static str,
    /// The actual execution declaration; never an exact-unsplit equivalence claim.
    pub execution_lattice: Option<crate::hnn::chart::WordLattice>,
    pub producing_commit: u64,
    pub opened_at: usize,
    pub source_cells: u64,
    pub receiver: usize,
    pub features: Vec<Vec<Rat>>,
    pub waves: Vec<Vec<Rat>>,
    pub masses: Vec<Vec<ExactInterval>>,
}
pub struct NativePredictionReturn {
    represented_policy:bool,
    reading: NativePredictionReading,
    scores: Vec<ExactInterval>,
    stations: Vec<RetainedStationReturn>,
    back: crate::hnn::port::WordReturn,
    pub(crate) cut: continuation::ContactCut,
    pub(crate) covector: crate::hnn::ratio::RatioCovector,
    phases: ReceivingPhases,
    producer: crate::hnn::constitution::Constitution,
    anchor: Vec<BigInt>,
    reach: crate::hnn::constitution::Reach,
}
impl NativePredictionReturn {
    pub fn reading(&self) -> &NativePredictionReading {
        &self.reading
    }
    pub fn scores(&self) -> &[ExactInterval] {
        &self.scores
    }
    pub fn stations(&self) -> &[RetainedStationReturn] {
        &self.stations
    }
    /// Actual factor publication only. Unsupported paired/split input is refused, not rerouted.
    pub fn publish_contact_carry(
        self,
        charts: &mut Charts,
    ) -> Result<NativeContactPublication, HnnError> {
        self.cut.publish_native_comparison(
            self.represented_policy,
            self.reading,
            &self.stations,
            &self.back,
            &self.phases,
            &self.covector,
            charts,
        )
    }
}
/// No Word tape is retained. The complete actual contact successor carries forward once.
pub struct NativeContactPublication {
    pub prediction: NativePredictionReading,
    pub constitution: crate::hnn::constitution::Constitution,
    pub carry: ReceptionCarry,
    pub publication: crate::hnn::constitution::DepositReading,
    pub continuation: continuation::ContinuationReceipt,
    pub actual_alignment: Rat,
    pub actual_error_charge: Rat,
    pub paired_readout_norm: Rat,
    /// Explicit physical-reference first variation against the original represented face.
    /// None on the preserved exact route; never a finite represented-score claim.
    pub physical_reference:Option<NativePhysicalRayReading>,
}

/// Private admitting input, issued only by the actual native Word comparison consumer.
#[derive(Clone, Debug)]
pub(crate) struct NativeContactWitness {
    pub(super) field: Field,
    pub(super) current: Current,
    pub(super) source: std::sync::Arc<crate::hnn::moment::SourceMoment>,
    pub(super) geometry: crate::hnn::port::PairedReturnGeometry,
    pub(super) phases: ReceivingPhases,
    pub(super) opened_at: usize,
    pub(super) reads: Vec<(Vec<Rat>, Vec<Rat>)>,
    pub(super) producing: crate::hnn::constitution::Constitution,
    pub(super) deposit: crate::hnn::port::Deposit,
    pub(super) readout_norm: Rat,
    pub(super) error_l1: Rat,
    pub(super) component_errors:Vec<Vec<Rat>>,
    pub(super) represented:Option<std::sync::Arc<super::material_ray::PhysicalContactProof>>,
}
impl NativeContactWitness {
    pub(crate) fn represented(&self)->bool{self.represented.is_some()}
    pub(crate) fn deposit(&self)->&crate::hnn::port::Deposit{&self.deposit}
    pub(crate) fn physical_refusal(&self,stage:&'static str,reading:NativePhysicalRayReading)->HnnError{
        HnnError::RepresentedNativeRayNotAdmitted{source_cells:self.source.cells(),commit:self.producing.commit(),stage,reading:Box::new(reading)}
    }
    pub(crate) fn physical_query(&self,o:&crate::hnn::propagation::Operands,
        direction:&super::material_ray::ContactDirections,extent:&super::material_ray::ContactDirections)
        ->Result<NativePhysicalRayReading,HnnError>{
        self.geometry.admit_native_contact(&self.field,&self.reads,o,&self.phases,self.opened_at)?;
        self.represented.as_ref().ok_or(HnnError::Unadmitted{reason:"physical represented ray requires its original stage issuer"})?
            .query(self,o,direction,extent,&self.component_errors)
    }
    pub(crate) fn admit_cut(
        &self,
        field: &Field,
        current: &Current,
        source: &std::sync::Arc<crate::hnn::moment::SourceMoment>,
    ) -> Result<(), HnnError> {
        if field != &self.field
            || current != &self.current
            || !std::sync::Arc::ptr_eq(source, &self.source)
        {
            return Err(HnnError::Unadmitted {
                reason: "native contact proof keeps the actual original source/field/frame/clock owner",
            });
        }
        Ok(())
    }
    pub(crate) fn admit_span(
        &self,
        operands: &crate::hnn::propagation::Operands,
        opened_at: usize,
        reach: &crate::hnn::constitution::Reach,
    ) -> Result<(), HnnError> {
        if opened_at != self.opened_at
            || reach.receiver != self.phases.ring()
            || reach.stations != self.phases.epochs().map(|j| j as u64).collect::<Vec<_>>()
        {
            return Err(HnnError::Unadmitted {
                reason: "native paired propagation gain keeps the actual opening and complete original receiving cut",
            });
        }
        self.geometry.admit_native_contact(
            &self.field,
            &self.reads,
            operands,
            &self.phases,
            opened_at,
        )
    }
    pub(crate) fn admit(
        &self,
        theta: &crate::hnn::constitution::Constitution,
        deposit: &crate::hnn::port::Deposit,
    ) -> Result<(), HnnError> {
        if theta != &self.producing || deposit != &self.deposit {
            return Err(HnnError::Unadmitted {
                reason: "native paired contact witness binds complete producing material and exact reached return",
            });
        }
        Ok(())
    }
    pub(crate) fn readout_norm(&self) -> &Rat {
        &self.readout_norm
    }
    pub(crate) fn error_charge(&self, squared_response: &Rat) -> Rat {
        &self.error_l1 * crate::holon::deposition::sqrt_ceiling(squared_response, 64)
    }
}
pub(crate) struct NativePredictionDeclaration{
    id:std::sync::Arc<()>,field:Field,theta:crate::hnn::constitution::Constitution,current:Current,
    source:std::sync::Arc<crate::hnn::moment::SourceMoment>,ops:crate::hnn::propagation::Operands,
    opening:EndChange,opened_at:usize,phases:ReceivingPhases,
}
impl NativePredictionDeclaration{
    fn admit(&self,word:&Word<'_>)->Result<(),HnnError>{
        let valid=word.native_source.as_ref().is_some_and(|(theta,current,source,_)|theta==&self.theta&&current==&self.current&&std::sync::Arc::ptr_eq(source,&self.source));
        if !valid||word.field!=&self.field||word.operands!=self.ops||word.opened_at()!=self.opened_at||!word.native_declaration_id.as_ref().is_some_and(|id|std::sync::Arc::ptr_eq(id,&self.id)){return Err(HnnError::Unadmitted{reason:"native declaration cannot rebind Word/source/current/material/clock"});}Ok(())
    }
    pub(crate) fn run_and_read<'a>(self,mut word:Word<'a>,bits:u32)->Result<NativePredictionWord<'a>,HnnError>{
        self.admit(&word)?;
        if word.complete_unrun_opening()?!=self.opening{return Err(HnnError::Unadmitted{reason:"native declaration keeps complete prepared opening"});}
        word.run(self.phases.junction_steps())?;word.native_current_prediction_declared(self,bits)
    }
}
impl<'a> Word<'a> {
    /// Read only already-executed stations; never runs or reinjects the source.
    pub fn native_current_prediction(
        mut self,
        receiver: usize,
        bits: u32,
    ) -> Result<NativePredictionWord<'a>, HnnError> {
        let (theta, current, _, _) = self.native_source.as_ref().ok_or(HnnError::Unadmitted {
            reason: "native prediction requires the actual source-producing Word",
        })?;
        let decl = self
            .field
            .receivers()
            .get(receiver)
            .ok_or(HnnError::Unadmitted {
                reason: "native prediction names an admitted receiver",
            })?;
        let phases = ReceivingPhases::declare(self.field, theta, current, decl)?;
        self.read_native_current(phases,bits)
    }
    pub(crate) fn declare_native_prediction(&mut self,receiver:usize,cache:&mut crate::hnn::receiving::NativeRankCache)->Result<NativePredictionDeclaration,HnnError>{
        let (theta,current,_,_)=self.native_source.as_ref().ok_or(HnnError::Unadmitted{reason:"declaring capability requires actual native producer"})?;
        let decl=self.field.receivers().get(receiver).ok_or(HnnError::Unadmitted{reason:"native declaration receiver"})?;
        let phases=cache.declare(self.field,theta,current,decl)?;self.issue_native_declaration(phases)
    }
    fn issue_native_declaration(&mut self,phases:ReceivingPhases)->Result<NativePredictionDeclaration,HnnError>{
        let (theta,current,source,_)=self.native_source.as_ref().ok_or(HnnError::Unadmitted{reason:"native declaration source"})?;
        if self.ticks()!=0||self.is_ended()||self.native_declaration_id.is_some(){return Err(HnnError::Unadmitted{reason:"same-cut declaration seals the one complete unrun prepared Word"});}
        let opening=self.complete_unrun_opening()?;let id=std::sync::Arc::new(());self.native_declaration_id=Some(id.clone());
        Ok(NativePredictionDeclaration{id,field:self.field.clone(),theta:theta.clone(),current:current.clone(),source:source.clone(),ops:self.operands.clone(),opening,opened_at:self.opened_at(),phases})
    }
    fn native_current_prediction_declared(mut self,cap:NativePredictionDeclaration,bits:u32)->Result<NativePredictionWord<'a>,HnnError>{
        cap.admit(&self)?;
        self.read_native_current(cap.phases,bits)
    }
    fn read_native_current(mut self,phases:ReceivingPhases,bits:u32)->Result<NativePredictionWord<'a>,HnnError>{
        let theta=&self.native_source.as_ref().ok_or(HnnError::Unadmitted{reason:"actual native source"})?.0;
        let map = theta
            .receiving_map(phases.ring())
            .ok_or(HnnError::MissingReceivingMap {
                ring: phases.ring(),
            })?
            .clone();
        if theta.receiving_layout(phases.ring())
            != Some(crate::hnn::constitution::ReceivingLayout::ArrivalContext {
                source_width: self.field.ring(phases.ring()).width(),
            })
        {
            return Err(HnnError::Unadmitted {
                reason: "native contextual predictor requires declared paired source/context layout",
            });
        }
        self.prepare_response()?;
        let response = self.response().expect("native response prepared");
        let mut faces = Vec::new();
        let mut features = Vec::new();
        for tick in phases.epochs() {
            let actual = self
                .anchor(tick, phases.ring())
                .ok_or(HnnError::WordEnded {
                    ticks: self.ticks(),
                })?;
            let fresh = &response
                .records
                .get(tick)
                .ok_or(HnnError::WordEnded {
                    ticks: self.ticks(),
                })?
                .anchors[phases.ring()];
            let mut feature = fresh.clone();
            feature.extend(actual.iter().zip(fresh).map(|(a, s)| a - s));
            let wave = map.apply(&feature)?;
            faces.push(NativeCurrentFace::at(wave, bits)?);
            features.push(feature);
        }
        Ok(NativePredictionWord {
            word: self,
            prepared: None,
            charts:None,
            phases,
            map,
            faces,
            features,
        })
    }
}
impl NativePredictionWord<'_> {
    pub(crate) fn with_charts(mut self,charts:Charts)->Self{self.charts=Some(charts);self}
    pub(crate) fn prepared_charts(&self)->Option<&Charts>{self.charts.as_ref()}

    pub(crate) fn with_prepared_cut(
        mut self,
        cut: Option<crate::hnn::reference::prepared_input::PreparedInputCut>,
    ) -> Self {
        self.prepared = cut;
        self
    }
    pub(crate) fn prepared_cut(
        &self,
    ) -> Option<&crate::hnn::reference::prepared_input::PreparedInputCut> {
        self.prepared.as_ref()
    }
    pub fn reading(&self) -> NativePredictionReading {
        let (theta, _, source, _) = self
            .word
            .native_source
            .as_ref()
            .expect("issued native producer");
        NativePredictionReading {
            law: LAW,
            execution_lattice:self.word.operands.lattice().copied(),
            producing_commit: theta.commit(),
            opened_at: self.word.opened_at(),
            source_cells: source.cells(),
            receiver: self.phases.ring(),
            features: self.features.clone(),
            waves: self.faces.iter().map(|f| f.wave().to_vec()).collect(),
            masses: self.faces.iter().map(|f| f.masses().to_vec()).collect(),
        }
    }
    /// The pre-target reached contrast. It can prepare only a later input, never this Word.
    pub(crate) fn lagged_boundary(
        &self,
        role: crate::hnn::reference::prepared_input::PrefixRole,
    ) -> Result<crate::hnn::reference::prepared_input::LaggedReceiverBoundary, HnnError> {
        let (theta, current, source, _) =
            self.word.native_source.as_ref().expect("native producer");
        if self.features.len() != 1 {
            return Err(HnnError::Unadmitted {
                reason: "one reached native context boundary in this causal chart",
            });
        }
        crate::hnn::reference::prepared_input::LaggedReceiverBoundary::issued(
            self.word.field,
            self.phases.ring(),
            source.cells(),
            theta.commit(),
            self.word
                .opened_at()
                .checked_add(self.word.ticks())
                .ok_or(HnnError::CountOverflow)?,
            current.lift(),
            &self.features[0],
            role,
        )
    }
    pub fn forward_receipt(
        &self,
    ) -> Result<
        (
            ReceptionCarry,
            WordBalance,
            Option<action::PortPreparationReceipt>,
        ),
        HnnError,
    > {
        let released = self.word.released()?;
        let balance = WordBalance::of(&released);
        if !balance.closes() {
            return Err(HnnError::Unadmitted {
                reason: "native full-tick forward retains its exact executed balance",
            });
        }
        let prep = self.word.source_preparation().cloned();
        if prep.as_ref().is_some_and(|p| !p.closes()) {
            return Err(HnnError::Unadmitted {
                reason: "native preparation work closes once before the first executed tick",
            });
        }
        Ok((self.word.reception_end()?, balance, prep))
    }
    pub fn draw(&self, station: usize, key: &Rat) -> Result<ReleaseReturn, HnnError> {
        let face = self.faces.get(station).ok_or(HnnError::Unadmitted {
            reason: "native release at an original produced station",
        })?;
        crate::receiver::release::draw(face.masses(), key).map_err(|_| HnnError::Unadmitted {
            reason: "native receiver draw reads its produced CDF",
        })
    }
    pub fn score(
        &self,
        targets: &crate::hnn::encoding::Encoded,
    ) -> Result<Vec<ExactInterval>, HnnError> {
        self.word.field.admit(targets)?;
        if targets.len() != self.faces.len() {
            return Err(HnnError::Unadmitted {
                reason: "one actual target for each native prediction",
            });
        }
        self.faces
            .iter()
            .zip(targets.classes_read())
            .map(|(f, t)| f.score(t))
            .collect()
    }
    pub fn observe(
        self,
        targets: &crate::hnn::encoding::Encoded,
    ) -> Result<NativePredictionReturn, HnnError> {
        let scores = self.score(targets)?;
        let represented_policy=self.prepared.as_ref().is_some_and(|p|p.native_lagged&&p.work_policy.represented());
        let reading = self.reading();
        let stations = self
            .faces
            .iter()
            .zip(targets.classes_read())
            .map(|(f, t)| f.returned(t))
            .collect::<Result<Vec<_>, _>>()?;
        let (_, current, _, _) = self
            .word
            .native_source
            .as_ref()
            .expect("native source owner");
        let (_, _, source, support) = self
            .word
            .native_source
            .as_ref()
            .expect("native source owner");
        let locus = crate::hnn::constitution::Locus::ReceivingMap(self.phases.ring());
        let diamond =
            crate::hnn::retention::Diamond::opened(self.word.field, &self.phases, support);
        if !diamond.retains(self.word.field, locus) {
            return Err(HnnError::Unadmitted {
                reason: "native return actually reaches its declared receiver",
            });
        }
        let occupied = self
            .word
            .field
            .sources()
            .iter()
            .map(|&g| {
                (0..self.word.field.ring(g).placements().len()).try_fold(0u64, |n, p| {
                    Ok::<_, HnnError>(
                        n + u64::from(source.phase_counts(g, p)?.iter().any(|&x| x != 0)),
                    )
                })
            })
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .max()
            .unwrap_or(0);
        let reach = crate::hnn::constitution::Reach {
            receiver: self.phases.ring(),
            stations: self.phases.epochs().map(|j| j as u64).collect(),
            entries: vec![0],
            phases: occupied,
            loci: std::iter::once(locus).collect(),
            passages: Vec::new(),
        };
        let producer = self
            .word
            .native_source
            .as_ref()
            .expect("native source owner")
            .0
            .clone();
        let anchor = current.lift().to_vec();
        let phases = crate::hnn::ratio::target_phases(
            self.word.field,
            current.lift(),
            self.phases.ring(),
            targets,
        )?;
        let covector =
            crate::hnn::ratio::RatioCovector::native_current(&reading.waves, &phases, &stations)?;
        let returned = self
            .word
            .return_contact(&covector, &self.map, &self.phases)?;
        let cut = returned
            .forward
            .into_present()
            .ok_or(HnnError::Unadmitted {
                reason: "actual native contact cut",
            })?;
        let back = returned
            .pullback
            .into_present()
            .ok_or(HnnError::Unadmitted {
                reason: "actual native same-Word return",
            })?;
        if back.reads.iter().map(|(f, _)| f).ne(self.features.iter()) {
            return Err(HnnError::Unadmitted {
                reason: "native return preserves complete actual/fresh producing feature",
            });
        }
        Ok(NativePredictionReturn {
            represented_policy,
            reading,
            scores,
            stations,
            back,
            cut,
            covector,
            phases: self.phases,
            producer,
            anchor,
            reach,
        })
    }
}

/// One actual consumed Word return. No public constructor and no retained Word tape.
pub(crate) struct NativeRPacket {
    producer: crate::hnn::constitution::Constitution,
    reading: NativePredictionReading,
    station: RetainedStationReturn,
    sample: crate::hnn::constitution::Sample,
    positive: Vec<Rat>,
    foil: Vec<Rat>,
    phase: Vec<Rat>,
    anchor: Vec<BigInt>,
    reach: crate::hnn::constitution::Reach,
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct NativeRSection {
    ring: usize,
    commit: u64,
    map: ExactRatMatrix,
    stations: Vec<RetainedStationReturn>,
    predictions: Vec<NativePredictionReading>,
    anchors: Vec<Vec<BigInt>>,
}
impl NativePredictionReturn {
    pub(crate) fn into_receiving_packet(self) -> Result<NativeRPacket, HnnError> {
        if self.stations.len() != 1 || self.back.reads.len() != 1 {
            return Err(HnnError::Unadmitted {
                reason: "one native R return per actual aperture-one Word",
            });
        }
        let station = self.stations[0].clone();
        let descent = self.covector.descent(0);
        let mut positive = vec![Rat::zero(); descent.len()];
        positive[2 * station.target] = Rat::one();
        let mut foil = vec![Rat::zero(); descent.len()];
        let mut phase = foil.clone();
        for i in 0..descent.len() {
            if i % 2 == 0 {
                foil[i] = &positive[i] - &descent[i];
            } else {
                phase[i] = descent[i].clone();
            }
        }
        let sample = crate::hnn::constitution::Sample {
            weight: Rat::one(),
            feature: self.back.reads[0].0.clone(),
            covector: descent,
            masses: Some(station.normalized_representative.clone()),
        };
        if self.reading.features != vec![sample.feature.clone()] {
            return Err(HnnError::Unadmitted {
                reason: "native R retains the actual Word's complete paired feature",
            });
        }
        Ok(NativeRPacket {
            producer: self.producer,
            reading: self.reading,
            station,
            sample,
            positive,
            foil,
            phase,
            anchor: self.anchor,
            reach: self.reach,
        })
    }
}
impl NativeRPacket {
    pub(crate) fn section(
        packets: Vec<Self>,
    ) -> Result<
        (
            std::sync::Arc<NativeRSection>,
            Vec<crate::hnn::port::Deposit>,
            Vec<crate::hnn::constitution::epoch::EpochReceivingRecord>,
        ),
        HnnError,
    > {
        use crate::hnn::constitution::epoch::{EpochReceivingLaw, EpochReceivingRecord};
        use crate::hnn::constitution::{LinearLocus, LinearStep, Locus, Reach};
        let first = packets.first().ok_or(HnnError::Unadmitted {
            reason: "a nonempty actual native receiving section",
        })?;
        let ring = first.reading.receiver;
        let theta = &first.producer;
        let map = theta
            .receiving_map(ring)
            .ok_or(HnnError::MissingReceivingMap { ring })?
            .clone();
        for (at, p) in packets.iter().enumerate() {
            if &p.producer != theta
                || p.reading.execution_lattice!=first.reading.execution_lattice
                || p.reading.receiver != ring
                || p.reading.producing_commit != theta.commit()
                || p.reading.source_cells
                    != first
                        .reading
                        .source_cells
                        .checked_add(at as u64)
                        .ok_or(HnnError::CountOverflow)?
            {
                return Err(HnnError::Unadmitted {
                    reason: "native R section preserves each original consecutive source cut at ONE producing material",
                });
            }
        }
        let origin = std::sync::Arc::new(NativeRSection {
            ring,
            commit: theta.commit(),
            map: map.clone(),
            stations: packets.iter().map(|p| p.station.clone()).collect(),
            predictions: packets.iter().map(|p| p.reading.clone()).collect(),
            anchors: packets.iter().map(|p| p.anchor.clone()).collect(),
        });
        let mut deposits = Vec::new();
        let mut records = Vec::new();
        for (at, p) in packets.into_iter().enumerate() {
            let law = EpochReceivingLaw::native(
                std::sync::Arc::clone(&origin),
                at,
                &p.sample,
                &p.positive,
                &p.foil,
                &p.phase,
            )?;
            records.push(EpochReceivingRecord {
                law,
                feature: p.sample.feature.clone(),
                positive: p.positive,
                foil: p.foil,
                phase: p.phase,
            });
            deposits.push(
                crate::hnn::port::Deposit::new(
                    origin.commit,
                    vec![LinearStep {
                        locus: LinearLocus::Receiving(ring),
                        samples: vec![p.sample],
                    }],
                    Vec::new(),
                    vec![Locus::ReceivingMap(ring)],
                )
                .with_reach(p.reach),
            );
        }
        Ok((origin, deposits, records))
    }
}

impl NativeRSection {
    pub(crate) fn ring(&self) -> usize {
        self.ring
    }
    pub(crate) fn commit(&self) -> u64 {
        self.commit
    }
    pub(crate) fn map(&self) -> &ExactRatMatrix {
        &self.map
    }
    pub(crate) fn stations(&self) -> &[RetainedStationReturn] {
        &self.stations
    }
    pub(crate) fn predictions(&self) -> &[NativePredictionReading] {
        &self.predictions
    }
    pub(crate) fn anchors(&self) -> &[Vec<BigInt>] {
        &self.anchors
    }
}
