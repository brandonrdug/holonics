//! Opt-in joint finite-read modulus. SOURCE ONLY: uncompiled and untested.
//!
//! This module is deliberately not called by publication, release, or a CLI. A
//! declaration has to be sealed on the existing pre-target native producer. Its
//! result is a local, conditional response bound, never permission to move a
//! factor or a claim about a different learning history / every admitted future.
use super::*;
use crate::hnn::constitution::{Carrier, Constitution, Lattice, Locus, NativeRoundingFoundingSeal};
use crate::hnn::field::{ConstitutionRead, Field};
use crate::hnn::moment::SourceMoment;
use crate::hnn::port::PairedReadDefect;
use crate::hnn::receiving::ReceivingPhases;
use crate::hnn::word::native_prediction::NativeContactPublication;
use crate::hnn::Current;
use crate::ratio::algebraic::ExactInterval;
use std::sync::Arc;

pub(crate) const MODULUS: &str = "native-joint-rounding-read-modulus-v1";
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReadUnits { InterleavedWaveCoordinates, NativeProbabilityMass }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReadNorm { ComponentwiseAbsolute, WholeBlockEuclidean }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ComparisonGrade {
    Physical,
    PhysicalHistoryVersusRepresentedLanded,
    RepresentedVersusRepresented,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ReleaseAccounting {
    PastPlusCurrentStroke,
    EntireRemainingFutureAnchor,
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum OpeningScope { SameActualPreparedOpening, UncertainPastPhysicalOpening }
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum RequestedGuarantee {
    ContinuousFixedOpening,
    SameDiscreteRelease,
    CompleteHeldMomentumSuccessor,
    EveryAdmittedFuture,
}
/// No default tolerance, ingress range, resource ceiling, or future is selected.
#[derive(Clone, Debug)]
pub(crate) struct ModulusResources {
    pub integer_bits: u64,
    pub live_operand_bits: u64,
    /// Conservative sum of preflight arithmetic payloads, not an RSS measurement.
    pub arithmetic_bit_work: u64,
    pub material_entries: usize,
    pub schedule_steps: usize,
    pub additional_levels: u32,
}
#[derive(Clone, Debug)]
pub(crate) struct ModulusRequest {
    pub units: ReadUnits,
    pub norm: ReadNorm,
    pub grade: ComparisonGrade,
    pub accounting: ReleaseAccounting,
    pub opening_scope: OpeningScope,
    pub guarantee: RequestedGuarantee,
    /// Complete coordinate-radius matrices about the ORIGINAL factors. This
    /// fixed domain covers both compared centers/boxes, not a gradient ray.
    pub domain: ContactDirections,
    pub tolerances: Vec<Vec<Rat>>,
    pub resources: ModulusResources,
}
#[derive(Debug)]
pub(crate) enum ModulusObstruction {
    Invalid(&'static str),
    Native(HnnError),
    Resource { stage: &'static str, required: u64, limit: u64 },
    MissingHistoricalRelease { contact: usize, clock: u64 },
    MissingOpeningStateProof,
    MissingMonotoneFutureAnchor,
    UnsupportedReadNorm,
    MissingUniformRepresentedHistoryFloor,
    MissingDiscreteBoundaryMargin,
    MissingHeldMomentumDomain,
    UnsupportedFuture,
    DomainDoesNotCover { contact: usize, family: usize, entry: usize },
    /// Failure of this upper enclosure, not a physical impossibility theorem.
    UnattainableEnclosure { station: usize, row: usize, floor: Rat, demand: Rat, read: Box<ReadPolynomial> },
    RefinementCeiling { station: usize, row: usize, ceiling: u32, upper: Rat, demand: Rat, read: Box<ReadPolynomial> },
}
impl From<HnnError> for ModulusObstruction {
    fn from(e: HnnError) -> Self { Self::Native(e) }
}
impl From<crate::ratio::linear::ExactLinearError> for ModulusObstruction {
    fn from(e:crate::ratio::linear::ExactLinearError)->Self { Self::Native(HnnError::from(e)) }
}
type Result<T> = std::result::Result<T, ModulusObstruction>;

struct Arithmetic { limits: ModulusResources, spent: u64 }
impl Arithmetic {
    fn new(limits: &ModulusResources) -> Result<Self> {
        if limits.integer_bits < 64 || limits.live_operand_bits == 0
            || limits.arithmetic_bit_work == 0 || limits.material_entries == 0
            || limits.schedule_steps == 0 || u64::from(limits.additional_levels) >= limits.integer_bits {
            return Err(ModulusObstruction::Invalid("finite explicit modulus resources"));
        }
        Ok(Self { limits: limits.clone(), spent: 0 })
    }
    fn reserve(&mut self, bits: u64) -> Result<()> {
        let next=self.spent.checked_add(bits).ok_or(ModulusObstruction::Resource {
            stage:"arithmetic payload overflow",required:u64::MAX,limit:self.limits.arithmetic_bit_work })?;
        if next>self.limits.arithmetic_bit_work { return Err(ModulusObstruction::Resource {
            stage:"arithmetic bit work",required:next,limit:self.limits.arithmetic_bit_work }); }
        self.spent=next; Ok(())
    }
    fn values<'a>(&mut self, values:impl IntoIterator<Item=&'a Rat>)->Result<()> {
        let mut sum=0u64;
        for q in values {
            let n=q.numer().bits();let d=q.denom().bits();
            if n>self.limits.integer_bits || d>self.limits.integer_bits {
                return Err(ModulusObstruction::Resource {stage:"operand integer",required:n.max(d),limit:self.limits.integer_bits});
            }
            sum=sum.checked_add(n).and_then(|s|s.checked_add(d)).ok_or(ModulusObstruction::Resource {
                stage:"operand extent",required:u64::MAX,limit:self.limits.live_operand_bits})?;
        }
        if sum>self.limits.live_operand_bits {return Err(ModulusObstruction::Resource {
            stage:"live operand payload",required:sum,limit:self.limits.live_operand_bits});}
        self.reserve(sum)
    }
    fn operation(&mut self,n:u64,d:u64)->Result<()> {
        if n>self.limits.integer_bits || d>self.limits.integer_bits {return Err(ModulusObstruction::Resource {
            stage:"arithmetic integer preflight",required:n.max(d),limit:self.limits.integer_bits});}
        self.reserve(n.saturating_add(d))
    }
    fn add(&mut self,a:&Rat,b:&Rat)->Result<Rat> {
        let n=a.numer().bits().saturating_add(b.denom().bits())
            .max(b.numer().bits().saturating_add(a.denom().bits())).saturating_add(1);
        self.operation(n,a.denom().bits().saturating_add(b.denom().bits()))?;Ok(a+b)
    }
    fn mul(&mut self,a:&Rat,b:&Rat)->Result<Rat> {
        self.operation(a.numer().bits().saturating_add(b.numer().bits()),a.denom().bits().saturating_add(b.denom().bits()))?;Ok(a*b)
    }
    fn sqrt(&mut self,a:&Rat)->Result<Rat> {
        if a<&Rat::zero(){return Err(ModulusObstruction::Invalid("negative norm square"));}
        self.operation(a.numer().bits().saturating_add(128),a.denom().bits().saturating_add(128))?;
        Ok(sqrt_ceiling(a,64))
    }
    fn norm(&mut self,m:&ExactRatMatrix)->Result<Rat> {
        let mut sum=Rat::zero();
        for q in m.entries(){let v=self.mul(q,q)?;sum=self.add(&sum,&v)?;}
        self.sqrt(&sum)
    }
    fn dyadic(&mut self,exponent:u32)->Result<Rat>{
        self.operation(1,u64::from(exponent).saturating_add(1))?;
        Ok(Rat::new(BigInt::one(),BigInt::one()<<exponent as usize))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct ChannelSnapshot {
    factors:[ExactRatMatrix;3], scales:[Rat;3], carries:[Vec<Rat>;6], lattice:u32, clock:u64,
}
impl ChannelSnapshot {
    fn take(theta:&Constitution,contact:usize,work:&mut Arithmetic)->Result<Self>{
        let factors=[theta.contact_storage(contact),theta.contact_stiffness(contact),theta.contact_dissipation(contact)];
        let zero=Rat::zero();
        work.values(factors.iter().flat_map(|m|m.entries()).chain(theta.contact_scales(contact)))?;
        for family in 0..6 {
            let count=if family<3{factors[family].entries().len()}else{1};
            work.values((0..count).map(|i|theta.native_rounding_carry_at(contact,family,i).unwrap_or(&zero)))?;
        }
        Ok(Self {
            factors:std::array::from_fn(|i|factors[i].clone()),scales:theta.contact_scales(contact).clone(),
            carries:std::array::from_fn(|f|{
                let count=if f<3{factors[f].entries().len()}else{1};
                (0..count).map(|i|theta.native_rounding_carry_at(contact,f,i).cloned().unwrap_or_else(Rat::zero)).collect()
            }),
            lattice:theta.lattice(Locus::Channel(contact))?.exponent(),clock:theta.clock(Locus::Channel(contact)),
        })
    }
    fn matches(&self,theta:&Constitution,contact:usize)->bool{
        let factors=[theta.contact_storage(contact),theta.contact_stiffness(contact),theta.contact_dissipation(contact)];
        self.lattice==theta.lattice(Locus::Channel(contact)).map(|l|l.exponent()).unwrap_or(u32::MAX)
            &&self.clock==theta.clock(Locus::Channel(contact))&&self.scales==*theta.contact_scales(contact)
            &&(0..3).all(|f|&self.factors[f]==factors[f])
            &&(0..6).all(|f|self.carries[f].iter().enumerate().all(|(i,r)|{
                theta.native_rounding_carry_at(contact,f,i).map_or_else(||r.is_zero(),|x|x==r)
            }))
    }
}
/// An opaque, live provenance chain. There is deliberately no from-text or
/// from-used-state constructor. The optional founding constructor below is the
/// ONLY origin; labels on legacy checkpoints cannot mint historical accuracy.
#[derive(Clone, Debug)]
pub(crate) struct NativeReleaseHistory {
    field:Field, channels:Vec<ChannelSnapshot>, absolute_release:Vec<Rat>,
}
impl NativeReleaseHistory {
    pub(in crate::hnn) fn newly_founded(field:&Field,theta:&Constitution,limits:&ModulusResources,_origin:&NativeRoundingFoundingSeal)->Result<Self>{
        let mut work=Arithmetic::new(limits)?;
        let mut channels=Vec::new();let mut entries=0usize;
        for c in 0..field.contacts().len(){
            let count=[theta.contact_storage(c),theta.contact_stiffness(c),theta.contact_dissipation(c)].iter().map(|m|m.entries().len()).sum::<usize>();
            entries=entries.checked_add(count).ok_or(ModulusObstruction::Invalid("material extent overflow"))?;
            if entries>limits.material_entries{return Err(ModulusObstruction::Resource{stage:"material coordinates",required:entries as u64,limit:limits.material_entries as u64});}
            let snapshot=ChannelSnapshot::take(theta,c,&mut work)?;
            if snapshot.clock!=0||snapshot.carries.iter().flatten().any(|r|!r.is_zero()){
                return Err(ModulusObstruction::MissingHistoricalRelease{contact:c,clock:snapshot.clock});
            }
            channels.push(snapshot);
        }
        if entries>limits.material_entries{return Err(ModulusObstruction::Resource{stage:"material coordinates",required:entries as u64,limit:limits.material_entries as u64});}
        Ok(Self{field:field.clone(),absolute_release:vec![Rat::zero();channels.len()],channels})
    }
    fn admit(&self,field:&Field,theta:&Constitution)->Result<()> {
        if &self.field!=field||self.channels.len()!=field.contacts().len(){return Err(ModulusObstruction::Invalid("history field/chart"));}
        for(c,s)in self.channels.iter().enumerate(){if !s.matches(theta,c){return Err(ModulusObstruction::MissingHistoricalRelease{contact:c,clock:theta.clock(Locus::Channel(c))});}}
        Ok(())
    }
    /// Future owner hook only: checks a genuine completed native publication,
    /// then charges worst-case release at its EXISTING clock. The predecessor
    /// unit is the coarsest authenticated unit; a finer successor label alone
    /// cannot prove which unit an intermediate stroke actually released on.
    /// The current publisher does not call this hook.
    pub(in crate::hnn::word) fn record_native_publication(&mut self,witness:&crate::hnn::word::native_prediction::NativeContactWitness,
        original:&Constitution,published:&NativeContactPublication,limits:&ModulusResources)->Result<()> {
        witness.admit(original,witness.deposit())?;
        if witness.field!=self.field || published.prediction.opened_at!=witness.opened_at
            || published.prediction.source_cells!=witness.source.cells() || published.prediction.receiver!=witness.phases.ring(){
            return Err(ModulusObstruction::Invalid("historical successor is the original source-owned native contact"));
        }
        self.admit(&self.field,original)?;
        if published.prediction.producing_commit!=original.commit()
            ||original.commit().checked_add(1)!=Some(published.constitution.commit())
            ||published.publication.commit!=published.constitution.commit(){
            return Err(ModulusObstruction::Invalid("one original native publication"));
        }
        let mut work=Arithmetic::new(limits)?;work.values(self.absolute_release.iter())?;
        let mut channels=Vec::new();let mut errors=self.absolute_release.clone();
        for(c,old)in self.channels.iter().enumerate(){
            let next=ChannelSnapshot::take(&published.constitution,c,&mut work)?;
            if next.lattice<old.lattice||next.clock<old.clock||next.clock>old.clock.saturating_add(1){return Err(ModulusObstruction::Invalid("monotone actual release unit and once-only contact clock"));}
            if next.clock==old.clock {
                if next!=*old{return Err(ModulusObstruction::Invalid("no silent material change without contact crossing"));}
            }else{
                let precision=crate::hnn::constitution::gamma_length(next.clock);
                let exponent=old.lattice.checked_add(precision).and_then(|v|v.checked_add(1)).ok_or(ModulusObstruction::Invalid("release exponent"))?;
                let e=work.dyadic(exponent)?;errors[c]=work.add(&errors[c],&e)?;
            }
            channels.push(next);
        }
        work.values(errors.iter())?;self.channels=channels;self.absolute_release=errors;Ok(())
    }
    /// Lossless representation hook; never reads exterior release receipts.
    /// It is not authority to land a C/K carry or publish a held successor.
    pub(crate) fn record_rebase(&mut self,original:&Constitution,next:&Constitution,limits:&ModulusResources)->Result<()> {
        self.admit(&self.field,original)?;let mut work=Arithmetic::new(limits)?;let mut channels=Vec::new();
        for(c,old)in self.channels.iter().enumerate(){
            let n=ChannelSnapshot::take(next,c,&mut work)?;
            if n.clock!=old.clock||n.lattice<old.lattice{return Err(ModulusObstruction::Invalid("rebase preserves clock and never coarsens"));}
            for f in 0..6 {
                let x=if f<3{old.factors[f].entries()}else{std::slice::from_ref(&old.scales[f-3])};
                let y=if f<3{n.factors[f].entries()}else{std::slice::from_ref(&n.scales[f-3])};
                if x.len()!=y.len(){return Err(ModulusObstruction::Invalid("six-carrier rebase shape"));}
                for i in 0..x.len(){let a=work.add(&x[i],&old.carries[f][i])?;let b=work.add(&y[i],&n.carries[f][i])?;
                    if a!=b{return Err(ModulusObstruction::Invalid("six-carrier value plus carry conservation"));}}
            }
            channels.push(n);
        }
        self.channels=channels;Ok(())
    }
}

/// Sealed before y by NativePredictionDeclaration. No public fields can relabel
/// the read, tolerance, opening, domain or resource range after return.
pub(crate) struct DeclaredJointModulus {
    id:Arc<()>,field:Field,current:Current,source:Arc<SourceMoment>,commit:u64,
    opened_at:usize,phases:ReceivingPhases,opening:EndChange,request:ModulusRequest,
}
impl DeclaredJointModulus {
    #[allow(clippy::too_many_arguments)]
    pub(in crate::hnn::word) fn seal(id:&Arc<()>,field:&Field,current:&Current,source:&Arc<SourceMoment>,theta:&Constitution,
        opened_at:usize,phases:&ReceivingPhases,opening:&EndChange,request:ModulusRequest)->Result<Self>{
        let mut work=Arithmetic::new(&request.resources)?;
        if request.norm!=ReadNorm::ComponentwiseAbsolute{return Err(ModulusObstruction::UnsupportedReadNorm);}
        if request.opening_scope!=OpeningScope::SameActualPreparedOpening{return Err(ModulusObstruction::MissingOpeningStateProof);}
        if request.accounting!=ReleaseAccounting::PastPlusCurrentStroke{return Err(ModulusObstruction::MissingMonotoneFutureAnchor);}
        match request.guarantee {
            RequestedGuarantee::ContinuousFixedOpening=>{},
            RequestedGuarantee::SameDiscreteRelease=>return Err(ModulusObstruction::MissingDiscreteBoundaryMargin),
            RequestedGuarantee::CompleteHeldMomentumSuccessor=>return Err(ModulusObstruction::MissingHeldMomentumDomain),
            RequestedGuarantee::EveryAdmittedFuture=>return Err(ModulusObstruction::UnsupportedFuture),
        }
        if request.domain.len()!=field.contacts().len()||request.tolerances.len()!=phases.aperture(){return Err(ModulusObstruction::Invalid("complete material domain and declared station demands"));}
        let rows=theta.receiving_map(phases.ring()).ok_or(HnnError::MissingReceivingMap{ring:phases.ring()})?.rows();
        let expected=match request.units{ReadUnits::InterleavedWaveCoordinates=>rows,ReadUnits::NativeProbabilityMass=>rows/2};
        if rows%2!=0||request.tolerances.iter().any(|v|v.len()!=expected||v.iter().any(|q|q<=&Rat::zero())){return Err(ModulusObstruction::Invalid("explicit positive demands in declared native read units"));}
        work.values(request.tolerances.iter().flatten().chain(request.domain.iter().flatten().flat_map(|m|m.entries()))
            .chain(opening.storage.iter().flatten()).chain(opening.arrivals.iter().flatten().flatten())
            .chain(opening.states.iter().flatten().flatten()).chain(opening.resonators.iter().flatten().flatten().flatten()))?;
        if request.domain.iter().flatten().flat_map(|m|m.entries()).any(|q|q<&Rat::zero()){return Err(ModulusObstruction::Invalid("nonnegative joint domain radii"));}
        Ok(Self{id:id.clone(),field:field.clone(),current:current.clone(),source:source.clone(),commit:theta.commit(),opened_at,phases:phases.clone(),opening:opening.clone(),request})
    }
}
#[derive(Clone, Debug)]
pub(crate) struct RadiusReading {
    pub contact:usize,pub clock:u64,pub lattice:u32,pub historical_coordinate_bound:Rat,
    pub actual_factor_carry:[Vec<Rat>;3],pub actual_scale_carry:[Vec<Rat>;3],
    pub prospective_half_cell_plus_release:Rat,
}
#[derive(Clone, Debug)]
pub(crate) struct ReadPolynomial {
    pub station:usize,pub row:usize,pub numerical_floor:Rat,
    pub constant:Rat,pub linear:Rat,pub quadratic:Rat,pub demand:Rat,
}
#[derive(Clone, Debug)]
pub(crate) enum TargetResult {
    /// A modulus target only, not an attained lattice or physical admission.
    ConditionalTarget { additional_levels:u32, absolute_exponents:Vec<u32> },
    /// Authentic producing-point floor does not qualify a changed candidate.
    MissingUniformCandidateNumericalFloor,
    HeldCarryLimitsRepresentationOnly { required_levels:u32, common_attainable_levels:u32 },
}
#[derive(Clone, Debug)]
pub(crate) struct AttainmentReading {
    pub contact:usize,pub current_exponent:u32,pub requested_exponent:u32,
    pub arithmetic_attainable_exponent:u32,pub limiting_held_factor:Option<(Carrier,usize,Rat)>,
}
#[derive(Clone, Debug)]
pub(crate) struct JointModulusReading {
    pub law:&'static str,pub units:ReadUnits,pub norm:ReadNorm,pub grade:ComparisonGrade,pub accounting:ReleaseAccounting,pub commit:u64,
    pub source_cells:u64,pub opened_at:usize,pub receiver:usize,
    pub producing_current:Current,pub original_actual_opening:EndChange,
    pub original_station_ticks:Vec<usize>,pub declared_joint_domain:ContactDirections,
    pub actual_opening_norm:Rat,pub fresh_opening_norm:Rat,
    pub radii:Vec<RadiusReading>,pub reads:Vec<ReadPolynomial>,pub target:TargetResult,
    /// Read-only old-carry limiter. No target is staged or physically admitted.
    pub representation_only_attainment:Vec<AttainmentReading>,
    /// Conditional evaluation at the common attainable level, absent if the
    /// producing-point numerical floor cannot qualify a changed candidate.
    pub arithmetic_bounds_at_common_attainment:Option<Vec<Rat>>,
    pub current_absolute_exponents:Vec<u32>,pub arithmetic_bit_work:u64,
    /// Actual source-owned enclosures, never midpoint probability representatives.
    pub source_probability_intervals:Option<Vec<Vec<ExactInterval>>>,
    /// H grade only: enlarged current landed intervals, a joint-box overapproximation
    /// rather than a new normalized draw or evidence of a class-boundary margin.
    pub current_probability_image:Option<Vec<Vec<ExactInterval>>>,
    pub scalar_box_fallback_contacts:Vec<usize>,
    /// Fixed actual opening only; neither held-momentum nor discrete identity.
    pub fixed_opening_only:bool,pub discrete_boundary_certified:bool,
    /// The future publisher must authenticate its actual attained lattice and
    /// center/history boxes; a computed target never grants that ownership.
    pub candidate_domain_checked:bool,pub material_publication_admitted:bool,
}
#[derive(Clone)]
struct Polynomial { c:Rat,a:Rat,b:Rat }
impl Polynomial {
    fn zero()->Self{Self{c:Rat::zero(),a:Rat::zero(),b:Rat::zero()}}
    fn scale(&self,s:&Rat,w:&mut Arithmetic)->Result<Self>{Ok(Self{c:w.mul(&self.c,s)?,a:w.mul(&self.a,s)?,b:w.mul(&self.b,s)?})}
    fn add(&self,p:&Self,w:&mut Arithmetic)->Result<Self>{Ok(Self{c:w.add(&self.c,&p.c)?,a:w.add(&self.a,&p.a)?,b:w.add(&self.b,&p.b)?})}
}
fn evaluated(p:&ReadPolynomial,s:u32,w:&mut Arithmetic)->Result<Rat>{
    let t=w.dyadic(s)?;let tt=w.mul(&t,&t)?;let a=w.mul(&p.linear,&t)?;let b=w.mul(&p.quadratic,&tt)?;
    let v=w.add(&p.numerical_floor,&p.constant)?;let v=w.add(&v,&a)?;w.add(&v,&b)
}
fn row_norm(m:&ExactRatMatrix,row:usize,work:&mut Arithmetic)->Result<Rat>{
    let mut sum=Rat::zero();for j in 0..m.columns(){let q=m.get(row,j).ok_or(ModulusObstruction::Invalid("native decoder row"))?;let q=work.mul(q,q)?;sum=work.add(&sum,&q)?;}work.sqrt(&sum)
}

/// No Word execution. This reads original immutable pair records, not a response
/// along the actual gradient as a surrogate for the complete rounding box.
#[allow(clippy::too_many_arguments)]
pub(in crate::hnn::word) fn issue(plan:&DeclaredJointModulus,id:&Arc<()>,field:&Field,current:&Current,source:&Arc<SourceMoment>,
    theta:&Constitution,o:&Operands,phases:&ReceivingPhases,opened_at:usize,stages:&OriginalPairStages,
    defect:Option<&PairedReadDefect>,mass_intervals:&[Vec<ExactInterval>],history:Option<&NativeReleaseHistory>)->Result<JointModulusReading>{
    if !Arc::ptr_eq(&plan.id,id)||!Arc::ptr_eq(&stages.declaration,id)||&plan.field!=field||&plan.current!=current
        ||!Arc::ptr_eq(&plan.source,source)||plan.commit!=theta.commit()||plan.opened_at!=opened_at
        ||&plan.phases!=phases||stages.opened_at!=opened_at||stages.full_ticks!=phases.junction_steps(){
        return Err(ModulusObstruction::Invalid("same original declaration/source/current/frame/schedule"));
    }
    let request=&plan.request;let mut work=Arithmetic::new(&request.resources)?;
    let history=history.ok_or_else(||ModulusObstruction::MissingHistoricalRelease{contact:0,clock:theta.clock(Locus::Channel(0))})?;
    history.admit(field,theta)?;
    if request.grade==ComparisonGrade::RepresentedVersusRepresented{return Err(ModulusObstruction::MissingUniformRepresentedHistoryFloor);}
    if stages.full_ticks>request.resources.schedule_steps||stages.fixed_ticks.len()!=stages.full_ticks{return Err(ModulusObstruction::Resource {
        stage:"sealed schedule",required:stages.full_ticks as u64,limit:request.resources.schedule_steps as u64});}
    // The original stage issuer already authenticated this norm against the
    // SAME complete opening/declaration. Do not run a second physical/norm pass.
    let actual_ref=&stages.actual.opening_norm;
    work.values([actual_ref,&stages.fresh.opening_norm].into_iter().chain(&stages.fixed_ticks).chain(&stages.physical_ticks)
        .chain(stages.actual.contacts.iter().flatten().chain(stages.fresh.contacts.iter().flatten())
            .flat_map(|s|[&s.input_norm,&s.input_error,&s.solve_residual]))
        .chain(request.tolerances.iter().flatten()).chain(request.domain.iter().flatten().flat_map(|m|m.entries()))
        .chain(history.absolute_release.iter()).chain(history.channels.iter().flat_map(|c|c.factors.iter().flat_map(|m|m.entries())
            .chain(c.scales.iter()).chain(c.carries.iter().flatten()))))?;
    if let Some(d)=defect {
        work.values(d.fresh.iter().flatten().chain(d.actual.iter().flatten().flatten()))?;
    }
    let actual=actual_ref.clone();
    let mut radii=Vec::new();let mut forcing=Polynomial::zero();let mut contact_norm=Rat::one();let mut fallback=Vec::new();let mut entries=0usize;
    for(c,contact)in o.contacts().iter().enumerate(){
        let base=[theta.contact_storage(c),theta.contact_stiffness(c),theta.contact_dissipation(c)];
        let domain=&request.domain[c];
        if theta.contact_stiffness_signature(c).is_some_and(|v|v.iter().any(|s|!s)){return Err(ModulusObstruction::Invalid("ordinary positive Gram contact domain only"));}
        let snapshot=&history.channels[c];let next_clock=snapshot.clock.checked_add(1).ok_or(ModulusObstruction::Invalid("actual deposit clock overflow"))?;
        let k=crate::hnn::constitution::gamma_length(next_clock);
        let half=work.dyadic(snapshot.lattice.checked_add(1).ok_or(ModulusObstruction::Invalid("material half-cell exponent"))?)?;
        let tail=work.dyadic(snapshot.lattice.checked_add(k).and_then(|s|s.checked_add(1)).ok_or(ModulusObstruction::Invalid("fine-release exponent"))?)?;
        let h=work.add(&half,&tail)?;let s=&history.absolute_release[c];let cover=work.add(s,&h)?;
        let mut forms:Vec<Polynomial>=Vec::new();
        for f in 0..3 {
            if base[f].rows()!=domain[f].rows()||base[f].columns()!=domain[f].columns()||base[f].rows()!=contact.width(){return Err(ModulusObstruction::Invalid("original factor box shape"));}
            entries=entries.checked_add(base[f].entries().len()).ok_or(ModulusObstruction::Invalid("material extent"))?;
            if entries>request.resources.material_entries{return Err(ModulusObstruction::Resource{stage:"joint factor coordinates",required:entries as u64,limit:request.resources.material_entries as u64});}
            for(i,d)in domain[f].entries().iter().enumerate(){if d<&cover{return Err(ModulusObstruction::DomainDoesNotCover{contact:c,family:f,entry:i});}}
            let bn=work.norm(base[f])?;let dn=work.norm(&domain[f])?;let fbar=work.add(&bn,&dn)?;
            let count=Rat::from_integer(BigInt::from(base[f].entries().len()));let dimension=work.sqrt(&count)?;
            let sr=work.mul(&dimension,s)?;let hr=work.mul(&dimension,&h)?;
            let twice=work.mul(&int(2),&fbar)?;let c0=work.mul(&twice,&sr)?;let ss=work.mul(&sr,&sr)?;
            let c0=work.add(&c0,&ss)?;let fs=work.add(&fbar,&sr)?;let aa=work.mul(&int(2),&fs)?;let aa=work.mul(&aa,&hr)?;let bb=work.mul(&hr,&hr)?;
            forms.push(Polynomial{c:c0,a:aa,b:bb});
        }
        work.values(base.iter().flat_map(|m|m.entries()).chain(domain.iter().flat_map(|m|m.entries())))?;
        // Reuse the original envelope/resolvent. Pre-authorize dense scratch;
        // skipping this optional tightening keeps the genuine scalar envelope.
        let input_bits=base.iter().flat_map(|m|m.entries()).chain(domain.iter().flat_map(|m|m.entries()))
            .try_fold(0u64,|n,q|n.checked_add(q.numer().bits())?.checked_add(q.denom().bits()))
            .ok_or(ModulusObstruction::Invalid("box input extent"))?;
        let scalar=input_bits.saturating_mul((contact.width() as u64).saturating_pow(3)).saturating_mul(16);
        work.reserve(scalar)?;
        let dense=scalar.saturating_mul(4);
        let tighten=dense<=request.resources.live_operand_bits&&work.spent.checked_add(dense).is_some_and(|n|n<=request.resources.arithmetic_bit_work);
        if tighten{work.reserve(dense)?;}
        let (n,alpha,tightened)=joint_box_envelope(base,domain.each_ref(),o.step(),contact.conductance(),tighten)?;
        if !tightened{fallback.push(c);}
        work.values(alpha.iter().chain(std::iter::once(&n)))?;
        // Conservative overlapping-block embedding: no unproved max/disjoint claim.
        let one_plus=work.add(&Rat::one(),&n)?;contact_norm=work.add(&contact_norm,&one_plus)?;
        for f in 0..3{forcing=forcing.add(&forms[f].scale(&alpha[f],&mut work)?,&mut work)?;}
        radii.push(RadiusReading{contact:c,clock:snapshot.clock,lattice:snapshot.lattice,historical_coordinate_bound:s.clone(),
            actual_factor_carry:std::array::from_fn(|f|snapshot.carries[f].clone()),actual_scale_carry:std::array::from_fn(|f|snapshot.carries[f+3].clone()),prospective_half_cell_plus_release:h});
    }
    let map=theta.receiving_map(phases.ring()).ok_or(HnnError::MissingReceivingMap{ring:phases.ring()})?;
    let width=o.rings()[phases.ring()].width();
    if map.columns()!=width*2{return Err(ModulusObstruction::Invalid("original paired receiver columns"));}
    work.values(map.entries())?;
    let rows=map.to_rows();
    let rc=ExactRatMatrix::new(rows.iter().map(|r|r[width..].to_vec()).collect())?;
    let mut residual_rows=Vec::new();
    for r in &rows{let mut row=Vec::new();for(s,c)in r[..width].iter().zip(&r[width..]){row.push(work.add(s,&(-c))?);}residual_rows.push(row);}
    let rs=ExactRatMatrix::new(residual_rows)?;
    let mut projection_square=Rat::zero();for q in o.exact_weights(phases.ring()).iter(){let q=work.mul(q,q)?;projection_square=work.add(&projection_square,&q)?;}
    let projection=work.sqrt(&projection_square)?;
    let mut ea=Polynomial::zero();let mut ef=Polynomial::zero();let mut na=actual.clone();let mut nf=stages.fresh.opening_norm.clone();
    let mut reads=Vec::new();let mut station=0usize;
    for t in 0..=stages.full_ticks{
        if phases.epochs().any(|j|j==t){
            let mut waves=Vec::new();
            for row in 0..map.rows(){
                let ca=row_norm(&rc,row,&mut work)?;let ca=work.mul(&ca,&projection)?;
                let cf=row_norm(&rs,row,&mut work)?;let cf=work.mul(&cf,&projection)?;
                let p=ea.scale(&ca,&mut work)?.add(&ef.scale(&cf,&mut work)?,&mut work)?;
                let mut floor=Rat::zero();
                if request.grade==ComparisonGrade::PhysicalHistoryVersusRepresentedLanded{
                    let defect=defect.ok_or(ModulusObstruction::Invalid("authentic landed actual/fresh numerical floor absent"))?;
                    let a=defect.actual.as_ref().ok_or(ModulusObstruction::Invalid("actual numerical floor absent"))?;
                    if a.len()!=phases.aperture()||defect.fresh.len()!=phases.aperture()||a[station].len()!=width||defect.fresh[station].len()!=width{return Err(ModulusObstruction::Invalid("landed numerical floor station shape"));}
                    for i in 0..width{
                        if a[station][i]<Rat::zero()||defect.fresh[station][i]<Rat::zero(){return Err(ModulusObstruction::Invalid("negative numerical floor"));}
                        let x=work.mul(&rc.get(row,i).unwrap().abs(),&a[station][i])?;let y=work.mul(&rs.get(row,i).unwrap().abs(),&defect.fresh[station][i])?;
                        let xy=work.add(&x,&y)?;floor=work.add(&floor,&xy)?;
                    }
                }
                waves.push((p,floor));
            }
            match request.units{
                ReadUnits::InterleavedWaveCoordinates=>for(row,(p,e))in waves.into_iter().enumerate(){reads.push(ReadPolynomial{station,row,numerical_floor:e,constant:p.c,linear:p.a,quadratic:p.b,demand:request.tolerances[station][row].clone()});},
                ReadUnits::NativeProbabilityMass=>{
                    // 2*p_i*(1-p_i)*ln2 <= ln2/2 <7/20. Only even rows
                    // drive the real native base-two normalization.
                    let mut max=Polynomial::zero();let mut e=Rat::zero();
                    for(p,floor)in waves.iter().step_by(2){max.c=max.c.max(p.c.clone());max.a=max.a.max(p.a.clone());max.b=max.b.max(p.b.clone());e=e.max(floor.clone());}
                    let ln2=crate::hnn::executed::ln_two()?;
                    work.values([&ln2.lower,&ln2.upper])?;
                    let ratio=work.mul(&ln2.upper,&Rat::new(1.into(),2.into()))?;
                    if ratio<=Rat::zero()||ratio>=Rat::new(7.into(),20.into()){
                        return Err(ModulusObstruction::Invalid("owned ln2 enclosure for probability units"));
                    }
                    max=max.scale(&ratio,&mut work)?;e=work.mul(&e,&ratio)?;
                    for row in 0..map.rows()/2{reads.push(ReadPolynomial{station,row,numerical_floor:e.clone(),constant:max.c.clone(),linear:max.a.clone(),quadratic:max.b.clone(),demand:request.tolerances[station][row].clone()});}
                }
            }
            station+=1;
        }
        if t<stages.full_ticks{
            let fixed=&stages.fixed_ticks[t];if fixed<&Rat::zero(){return Err(ModulusObstruction::Invalid("negative fixed-stage operator bound"));}
            ea=ea.scale(fixed,&mut work)?;ef=ef.scale(fixed,&mut work)?;na=work.mul(&na,fixed)?;nf=work.mul(&nf,fixed)?;
            let force_a=forcing.scale(&na,&mut work)?;let force_f=forcing.scale(&nf,&mut work)?;
            ea=ea.scale(&contact_norm,&mut work)?.add(&force_a,&mut work)?;
            ef=ef.scale(&contact_norm,&mut work)?.add(&force_f,&mut work)?;
            na=work.mul(&na,&contact_norm)?;nf=work.mul(&nf,&contact_norm)?;
        }
    }
    if station!=phases.aperture(){return Err(ModulusObstruction::Invalid("complete original read schedule"));}
    let mut needed=0u32;
    for p in &reads{
        let constant=work.add(&p.numerical_floor,&p.constant)?;
        if constant>p.demand||(constant==p.demand&&(!p.linear.is_zero()||!p.quadratic.is_zero())){
            return Err(ModulusObstruction::UnattainableEnclosure{station:p.station,row:p.row,floor:constant,demand:p.demand.clone(),read:Box::new(p.clone())});
        }
        if evaluated(p,0,&mut work)?<=p.demand{continue;}
        let cap=request.resources.additional_levels;let at_cap=evaluated(p,cap,&mut work)?;
        if at_cap>p.demand{return Err(ModulusObstruction::RefinementCeiling{station:p.station,row:p.row,ceiling:cap,upper:at_cap,demand:p.demand.clone(),read:Box::new(p.clone())});}
        let(mut low,mut high)=(0,cap);while low<high{let mid=low+(high-low)/2;if evaluated(p,mid,&mut work)?<=p.demand{high=mid;}else{low=mid+1;}}needed=needed.max(low);
    }
    let mut source_intervals=None;let mut probability_image=None;
    if request.units==ReadUnits::NativeProbabilityMass {
        if mass_intervals.len()!=phases.aperture()||mass_intervals.iter().any(|v|v.len()!=map.rows()/2
            ||v.iter().any(|v|v.lower<Rat::zero()||v.upper>Rat::one()||v.lower>v.upper)){
            return Err(ModulusObstruction::Invalid("original native mass enclosures"));
        }
        work.values(mass_intervals.iter().flatten().flat_map(|i|[&i.lower,&i.upper]))?;
        source_intervals=Some(mass_intervals.to_vec());
        if request.grade==ComparisonGrade::PhysicalHistoryVersusRepresentedLanded {
            let mut image=Vec::new();
            for(j,v)in mass_intervals.iter().enumerate(){let mut row=Vec::new();for(c,i)in v.iter().enumerate(){
                let p=&reads[j*(map.rows()/2)+c];let bound=evaluated(p,0,&mut work)?;
                let lower=work.add(&i.lower,&(-&bound))?.max(Rat::zero());
                let upper=work.add(&i.upper,&bound)?.min(Rat::one());
                row.push(ExactInterval{lower,upper});
            }image.push(row);}
            probability_image=Some(image);
        }
    }
    let mut attainment=Vec::new();let mut common_attainable=needed;
    for r in &radii{
        let requested=r.lattice.checked_add(needed).ok_or(ModulusObstruction::Invalid("absolute target overflow"))?;
        let (at,limiting)=theta.native_rounding_attainable_lattice(r.contact,Lattice::new(requested))?;
        common_attainable=common_attainable.min(at.exponent()-r.lattice);
        attainment.push(AttainmentReading{contact:r.contact,current_exponent:r.lattice,requested_exponent:requested,
            arithmetic_attainable_exponent:at.exponent(),limiting_held_factor:limiting});
    }
    // For different attained units, min(levels) is a conservative common level.
    // A shortfall never receives the requested target's resolution predicate.
    let target=if request.grade==ComparisonGrade::PhysicalHistoryVersusRepresentedLanded&&needed>0{
        TargetResult::MissingUniformCandidateNumericalFloor
    }else if common_attainable<needed{
        TargetResult::HeldCarryLimitsRepresentationOnly{required_levels:needed,common_attainable_levels:common_attainable}
    }else{
        TargetResult::ConditionalTarget{additional_levels:needed,absolute_exponents:attainment.iter().map(|r|r.requested_exponent).collect()}
    };
    let attained_bounds=if request.grade==ComparisonGrade::PhysicalHistoryVersusRepresentedLanded&&common_attainable>0{None}
        else{Some(reads.iter().map(|p|evaluated(p,common_attainable,&mut work)).collect::<Result<Vec<_>>>()?)};
    work.values(reads.iter().flat_map(|p|[&p.numerical_floor,&p.constant,&p.linear,&p.quadratic,&p.demand]))?;
    work.values(request.domain.iter().flatten().flat_map(|m|m.entries())
        .chain(plan.opening.storage.iter().flatten()).chain(plan.opening.arrivals.iter().flatten().flatten())
        .chain(plan.opening.states.iter().flatten().flatten()).chain(plan.opening.resonators.iter().flatten().flatten().flatten()))?;
    Ok(JointModulusReading{law:MODULUS,units:request.units,norm:request.norm,grade:request.grade,accounting:request.accounting,commit:theta.commit(),source_cells:source.cells(),opened_at,receiver:phases.ring(),
        producing_current:current.clone(),original_actual_opening:plan.opening.clone(),original_station_ticks:phases.epochs().collect(),declared_joint_domain:request.domain.clone(),
        actual_opening_norm:actual,fresh_opening_norm:stages.fresh.opening_norm.clone(),
        current_absolute_exponents:radii.iter().map(|r|r.lattice).collect(),radii,reads,target,
        representation_only_attainment:attainment,arithmetic_bounds_at_common_attainment:attained_bounds,arithmetic_bit_work:work.spent,
        source_probability_intervals:source_intervals,current_probability_image:probability_image,
        scalar_box_fallback_contacts:fallback,fixed_opening_only:true,discrete_boundary_certified:false,candidate_domain_checked:false,material_publication_admitted:false})
}
