//! Bounded exact grade-two source work. This is not a coordinate or energy relaxation.
use super::*;
use num_bigint::BigInt;
use num_traits::Signed;

#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub struct NativeWorkBudget {pub aggregate_bits:u64,pub integer_bits:u64,pub coordinates:usize}
impl NativeWorkBudget {
    pub const V1:Self=Self{aggregate_bits:1_048_576,integer_bits:65_536,coordinates:128};
    pub(crate) fn admit(self)->Result<(),HnnError>{
        if self.aggregate_bits==0||self.aggregate_bits>Self::V1.aggregate_bits||self.integer_bits<64||self.integer_bits>Self::V1.integer_bits||self.coordinates==0||self.coordinates>128{return Err(HnnError::Unadmitted{reason:"declared finite native quadratic work budget"});}Ok(())
    }
}
#[derive(Clone,Copy,Debug,PartialEq,Eq)]
pub enum PreparationWorkPolicy {LegacyCoordinateV1,NativeQuadraticV1(NativeWorkBudget)}
#[derive(Clone,Debug,PartialEq,Eq)]
pub struct QuadraticWorkReading {
    pub policy:NativeWorkBudget,pub source_cells:u64,pub ring:usize,pub old:Vec<Rat>,pub added:Vec<Rat>,pub control:Vec<Rat>,pub metric:Rat,
    pub numerator_bound_bits:u64,pub denominator_bound_bits:u64,pub charged_arithmetic_bits:u64,
}
struct Arithmetic {policy:NativeWorkBudget,spent:u64}
impl Arithmetic {
    fn new(policy:NativeWorkBudget)->Result<Self,HnnError>{policy.admit()?;Ok(Self{policy,spent:0})}
    fn charge(&mut self,bits:u64,stage:&'static str)->Result<(),HnnError>{
        let next=self.spent.checked_add(bits).ok_or(HnnError::CountOverflow)?;
        if bits>self.policy.integer_bits||next>self.policy.aggregate_bits{return Err(HnnError::QuadraticWorkExtent{stage,requested_bits:bits,integer_limit:self.policy.integer_bits,aggregate_used:self.spent,aggregate_limit:self.policy.aggregate_bits});}
        self.spent=next;Ok(())
    }
    fn rational(&mut self,q:&Rat)->Result<(),HnnError>{self.charge(q.numer().bits(),"rational numerator")?;self.charge(q.denom().bits(),"rational denominator")}
    fn mul(&mut self,a:&BigInt,b:&BigInt)->Result<BigInt,HnnError>{self.charge(a.bits().checked_add(b.bits()).ok_or(HnnError::CountOverflow)?,"integer product")?;Ok(a*b)}
    fn add(&mut self,a:&BigInt,b:&BigInt)->Result<BigInt,HnnError>{self.charge(a.bits().max(b.bits()).checked_add(1).ok_or(HnnError::CountOverflow)?,"integer sum")?;Ok(a+b)}
    fn gcd(&mut self,a:&BigInt,b:&BigInt)->Result<BigInt,HnnError>{
        self.charge(a.bits(),"gcd input copy")?;self.charge(b.bits(),"gcd input copy")?;let mut a=a.clone();let mut b=b.clone();
        while !b.is_zero(){self.charge(a.bits().checked_add(b.bits()).ok_or(HnnError::CountOverflow)?,"gcd remainder")?;let r=&a%&b;a=b;b=r;}Ok(a)
    }
    fn quotient(&mut self,a:&BigInt,b:&BigInt)->Result<BigInt,HnnError>{self.charge(a.bits(),"exact quotient")?;Ok(a/b)}
    fn fraction(&mut self,n:BigInt,d:BigInt)->Result<Rat,HnnError>{
        let width=n.bits().checked_add(d.bits()).ok_or(HnnError::CountOverflow)?;
        // Input pair plus bounded gcd/division scratch and normalized pair. Each
        // normalization integer stays within its input pair's already admitted extent.
        for _ in 0..4{self.charge(width,"fraction normalization storage reservation")?;}
        Ok(Rat::new(n,d))
    }
}
fn metric(form:&PowerForm,ring:usize,b:&mut Arithmetic)->Result<Rat,HnnError>{
    let h=&form.step;let y=&form.admittances[ring];b.rational(h)?;b.rational(y)?;
    b.charge(h.numer().bits().checked_add(y.numer().bits()).ok_or(HnnError::CountOverflow)?,"metric numerator product")?;
    b.charge(h.denom().bits().checked_add(y.denom().bits()).and_then(|n|n.checked_add(3)).ok_or(HnnError::CountOverflow)?,"metric denominator product")?;
    Ok(h/integer(4)*y)
}
struct Derived {cross:Rat,quadratic:Rat,work:Rat,n_bits:u64,d_bits:u64}
fn derive(m:&[Rat],a:&[Rat],k:&Rat,b:&mut Arithmetic)->Result<Derived,HnnError>{
    if m.len()!=a.len()||m.is_empty()||m.len()>b.policy.coordinates||k<=&Rat::zero(){return Err(HnnError::Unadmitted{reason:"isotropic same-source quadratic work operands"});}
    let mut q=BigInt::one();
    for x in m.iter().chain(a){b.rational(x)?;b.charge(q.bits().max(x.denom().bits()),"LCM gcd")?;let g=b.gcd(&q,x.denom())?;let part=b.quotient(&q,&g)?;q=b.mul(&part,x.denom())?;}
    b.rational(k)?;
    let mut cross=BigInt::zero();let mut quadratic=BigInt::zero();let mut cross_abs=BigInt::zero();
    for (m,a) in m.iter().zip(a){
        let dm=b.quotient(&q,m.denom())?;let da=b.quotient(&q,a.denom())?;
        let mi=b.mul(m.numer(),&dm)?;let ai=b.mul(a.numer(),&da)?;
        let product=b.mul(&mi,&ai)?;let twice=b.mul(&BigInt::from(2),&product)?;
        b.charge(twice.bits(),"absolute cross")?;cross_abs=b.add(&cross_abs,&twice.abs())?;cross=b.add(&cross,&twice)?;
        let square=b.mul(&ai,&ai)?;quadratic=b.add(&quadratic,&square)?;
    }
    let bound=b.add(&cross_abs,&quadratic)?;b.charge(k.numer().bits(),"absolute metric")?;let bound=b.mul(&k.numer().abs(),&bound)?;
    let nc=b.mul(k.numer(),&cross)?;let nq=b.mul(k.numer(),&quadratic)?;let n=b.add(&nc,&nq)?;
    let q2=b.mul(&q,&q)?;let d=b.mul(k.denom(),&q2)?;let n_bits=bound.bits();let d_bits=d.bits();
    // Copies and normalization are also charged before allocation; cancellation cannot hide cost.
    b.charge(d.bits(),"cross denominator copy")?;let cd=d.clone();b.charge(d.bits(),"quadratic denominator copy")?;let qd=d.clone();
    let cross=b.fraction(nc,cd)?;let quadratic=b.fraction(nq,qd)?;let work=b.fraction(n,d)?;
    Ok(Derived{cross,quadratic,work,n_bits,d_bits})
}
/// A borrowed, private witness cannot outlive or rebind its authentic producer.
struct Witness<'a,'w>{baseline:&'a Word<'w>,producer:&'a ActionProducer,preparation:&'a PortPreparation,control:&'a[Rat],form:&'a PowerForm,added:Vec<Rat>,derived:Derived,budget:Arithmetic}
impl<'a,'w> Witness<'a,'w>{
    fn issue(producer:&'a ActionProducer,preparation:&'a PortPreparation,control:&'a[Rat],form:&'a PowerForm,baseline:&'a Word<'w>,policy:NativeWorkBudget)->Result<Self,HnnError>{
        if !producer.matches(baseline)||baseline.ticks()!=0||baseline.is_ended()||baseline.complete_unrun_opening()?!=producer.opening||form!=&PowerForm::read(baseline.field,&producer.constitution,&producer.current)?||form.resonators[preparation.ring].is_some(){return Err(HnnError::Unadmitted{reason:"quadratic work authentic complete source/metric opening"});}
        let mut budget=Arithmetic::new(policy)?;
        if preparation.map.rows()>policy.coordinates{return Err(HnnError::Unadmitted{reason:"bounded quadratic source dimension"});}
        // Preflight the rational matrix/control products and sums before map.apply allocates them.
        for i in 0..preparation.map.rows(){let mut sn=0u64;let mut sd=1u64;
            for (j,u) in control.iter().enumerate(){let x=preparation.map.get(i,j)?;let n=x.numer().bits().checked_add(u.numer().bits()).ok_or(HnnError::CountOverflow)?;let d=x.denom().bits().checked_add(u.denom().bits()).ok_or(HnnError::CountOverflow)?;
                budget.charge(n,"control product numerator")?;budget.charge(d,"control product denominator")?;
                let nn=sn.checked_add(d).ok_or(HnnError::CountOverflow)?.max(n.checked_add(sd).ok_or(HnnError::CountOverflow)?).checked_add(1).ok_or(HnnError::CountOverflow)?;
                sd=sd.checked_add(d).ok_or(HnnError::CountOverflow)?;sn=nn;budget.charge(sn,"control sum numerator")?;budget.charge(sd,"control sum denominator")?;}
        }
        let added=preparation.map.apply(control)?;
        let ring=preparation.ring;let k=metric(form,ring,&mut budget)?;
        let derived=derive(&producer.opening.storage[ring],&added,&k,&mut budget)?;
        Ok(Self{baseline,producer,preparation,control,form,added,derived,budget})
    }
    fn admit(mut self,producer:&ActionProducer,preparation:&PortPreparation,control:&[Rat],form:&PowerForm,baseline:&Word<'_>,max:&Rat,coordinate_bits:u64)->Result<Admitted,HnnError>{
        if !std::ptr::eq(self.baseline,baseline)||!std::ptr::eq(self.producer,producer)||!std::ptr::eq(self.preparation,preparation)||control!=self.control||form!=self.form||!producer.matches(baseline)||baseline.complete_unrun_opening()?!=producer.opening{return Err(HnnError::Unadmitted{reason:"quadratic work witness cannot rebind producer/frame/source/metric"});}
        self.budget.rational(&self.derived.work)?;self.budget.rational(max)?;
        admit_coordinates_and_magnitude(producer.source.cells(),&self.derived,&self.added,max,coordinate_bits)?;
        for q in producer.opening.storage[preparation.ring].iter().chain(&self.added).chain(control){self.budget.rational(q)?;}
        let k=metric(form,preparation.ring,&mut self.budget)?;self.budget.rational(&k)?;
        let reading=QuadraticWorkReading{policy:self.budget.policy,source_cells:producer.source.cells(),ring:preparation.ring,old:producer.opening.storage[preparation.ring].clone(),added:self.added.clone(),control:control.to_vec(),metric:k,numerator_bound_bits:self.derived.n_bits,denominator_bound_bits:self.derived.d_bits,charged_arithmetic_bits:self.budget.spent};
        Ok(Admitted{added:self.added,derived:self.derived,budget:self.budget,reading})
    }
}
fn admit_coordinates_and_magnitude(source_cells:u64,d:&Derived,added:&[Rat],max:&Rat,bits:u64)->Result<(),HnnError>{
    admit_class_preparation_bound(source_cells,&Rat::zero(),added,max,bits)?;
    if d.work.abs()>*max{return Err(HnnError::ClassPreparationBound{source_cells,work:(d.work.numer().bits().saturating_add(d.work.denom().bits())<=8192).then(||Box::new(d.work.clone())),max_abs_work:(max.numer().bits().saturating_add(max.denom().bits())<=8192).then(||Box::new(max.clone())),work_magnitude_exceeded:true,work_range_exceeded:false,added_range_exceeded:false,work_numerator_bits:d.work.numer().bits(),work_denominator_bits:d.work.denom().bits(),added_numerator_bits:added.iter().map(|x|x.numer().bits()).max().unwrap_or(0),added_denominator_bits:added.iter().map(|x|x.denom().bits()).max().unwrap_or(0),rational_bits:bits});}Ok(())
}
struct Admitted{added:Vec<Rat>,derived:Derived,budget:Arithmetic,reading:QuadraticWorkReading}
impl SourceClassPreparation{
    pub(crate) fn apply_quadratic<'c>(self,baseline:Word<'c>,control:&[Rat],max_abs_work:&Rat,rational_bits:u64,policy:NativeWorkBudget)->Result<(Word<'c>,PortPreparationReceipt),HnnError>{
        if !self.producer.matches(&baseline)||baseline.ticks()!=0||baseline.is_ended()||baseline.complete_unrun_opening()?!=self.producer.opening{return Err(HnnError::Unadmitted{reason:"class quadratic control consumes its whole unrun native source opening"});}
        self.boundary.check_material(&self.producer.constitution)?;
        if control.len()!=self.preparation.controls()||max_abs_work<&Rat::zero()||!(64..=4096).contains(&rational_bits)||control.iter().any(|q|q.numer().bits()>rational_bits||q.denom().bits()>rational_bits){return Err(HnnError::Unadmitted{reason:"unchanged quadratic class-coordinate control bounds"});}
        let form=PowerForm::read(baseline.field,&self.producer.constitution,&self.producer.current)?;
        let witness=Witness::issue(&self.producer,&self.preparation,control,&form,&baseline,policy)?;
        let mut admitted=witness.admit(&self.producer,&self.preparation,control,&form,&baseline,max_abs_work,rational_bits)?;
        let (mut word,mut receipt,_)=apply_control_added(self.producer,&self.preparation,&baseline,std::mem::take(&mut admitted.added),Some(&form))?;
        if receipt.work!=admitted.derived.work||receipt.cross!=admitted.derived.cross||receipt.quadratic!=admitted.derived.quadratic||!receipt.closes(){return Err(HnnError::Realization{what:"operand-derived quadratic work equals full before/after and cross/quadratic once"});}
        // Full-form outputs retain their existing domain; also account every stored receipt field.
        for q in [&receipt.before,&receipt.after,&receipt.work,&receipt.cross,&receipt.quadratic]{admitted.budget.rational(q)?;}
        admitted.reading.charged_arithmetic_bits=admitted.budget.spent;receipt.quadratic_work=Some(admitted.reading);
        word.response_source=baseline.response_source.clone().map(|mut s|{for(x,a)in s[self.preparation.ring].iter_mut().zip(&receipt.added){*x+=a;}s});
        word.response_opening_exact=baseline.response_opening_exact.clone().map(|mut o|{for(x,a)in o.storage[self.preparation.ring].iter_mut().zip(&receipt.added){*x+=a;}o});
        for q in [&receipt.before,&receipt.after,&receipt.work,&receipt.cross,&receipt.quadratic].into_iter().chain(receipt.added.iter()).chain(receipt.quadratic_work.as_ref().into_iter().flat_map(|r|r.old.iter().chain(&r.added).chain(&r.control).chain(std::iter::once(&r.metric)))){admitted.budget.rational(q)?;}
        if let Some(r)=receipt.quadratic_work.as_mut(){r.charged_arithmetic_bits=admitted.budget.spent;}
        word.source_preparation=Some(receipt.clone());Ok((word,receipt))
    }
}

#[cfg(test)]
mod controls{
    use super::*;
    #[test]
    #[ignore="one isolated finite CODE process with pre-reserved native attempts"]
    fn native_quadratic_carrier_and_rank_controls(){
        use crate::hnn::word::work;
        struct Meter;impl Drop for Meter{fn drop(&mut self){let c=work::process_native_calls();let t=c.forward_attempts+c.response_attempts+c.return_attempts+c.response_return_attempts;let j=format!("{{\"final\":true,\"total_attempts\":{t},\"forward_constructors\":{},\"response_companions\":{},\"actual_returns\":{},\"fresh_returns\":{}}}\n",c.forward_attempts,c.response_attempts,c.return_attempts,c.response_return_attempts);println!("QUADRATIC_CONTROL_COUNTER {j}");if let Some(p)=std::env::var_os("V93_NATIVE_COUNT_PATH"){std::fs::write(p,j).unwrap();}}}
        let _meter=Meter;work::limit_process_native_attempts(std::env::var("V93_NATIVE_ATTEMPT_LIMIT").unwrap().parse().unwrap());
        let captured=Rat::new("51564025503142025724633702171333565477839602018262442180103416381733773829048987453642701117582441066181057391566130098304758509976933898410653964848328685074019118599927583053254770629577698244842880393017724348808904362643832108931305119651518354414673594465825438666030285830918268463504266119585360990590528111".parse().unwrap(),"22047267733340713048940158349214507467643823909519974157522241104760090223066576032924786842675813207198282257472108484449990867834675484277115873809660291195993146826927099026296864779242370390778269105246036983513853630109287239444143229113361694201038019485686046577441025195335936000000000000000000000000000000".parse().unwrap());
        assert_eq!((captured.numer().bits(),captured.denom().bits()),(1043,1041));assert!(captured<integer(65536));assert!(admit_class_preparation_bound(7,&captured,&[],&integer(65536),1024).is_err());
        let p=(BigInt::one()<<522usize)-1;let q=(BigInt::one()<<523usize)-1;let x=Rat::new(p,q);
        let form=PowerForm{step:Rat::one(),admittances:vec![integer(4)],conductances:vec![],storage:vec![],stiffness:vec![],resonators:vec![None]};
        let mut b=Arithmetic::new(NativeWorkBudget::V1).unwrap();let d=derive(&[x.clone()],&[x.clone()],&Rat::one(),&mut b).unwrap();
        let full=form.ring_power(0,&[&x+&x])-form.ring_power(0,&[x.clone()]);assert_eq!(full,d.work);assert_eq!(&d.cross+&d.quadratic,d.work);assert_eq!((d.work.numer().bits(),d.work.denom().bits()),(1046,1046));assert!(d.work<Rat::one());
        assert!(admit_class_preparation_bound(0,&d.work,&[x.clone()],&integer(65536),1024).is_err());admit_coordinates_and_magnitude(0,&d,&[x.clone()],&integer(65536),1024).unwrap();
        let signed=derive(&[-&x],&[x.clone()],&Rat::one(),&mut Arithmetic::new(NativeWorkBudget::V1).unwrap()).unwrap();assert!(signed.cross<Rat::zero());assert_eq!(signed.work,-&x*&x);assert!(signed.n_bits>=signed.work.numer().bits());
        let physical=derive(&[Rat::zero()],&[integer(257)],&Rat::one(),&mut Arithmetic::new(NativeWorkBudget::V1).unwrap()).unwrap();assert!(matches!(admit_coordinates_and_magnitude(0,&physical,&[integer(257)],&integer(65536),1024),Err(HnnError::ClassPreparationBound{work_magnitude_exceeded:true,..})));
        let tiny=Rat::new(BigInt::one(),BigInt::one()<<1024usize);let r=derive(&[Rat::zero()],&[tiny.clone()],&Rat::one(),&mut Arithmetic::new(NativeWorkBudget::V1).unwrap()).unwrap();assert!(matches!(admit_coordinates_and_magnitude(0,&r,&[tiny],&integer(65536),1024),Err(HnnError::ClassPreparationBound{added_range_exceeded:true,..})));
        let exhausted=NativeWorkBudget{aggregate_bits:128,..NativeWorkBudget::V1};assert!(matches!(derive(&[x.clone()],&[x.clone()],&Rat::one(),&mut Arithmetic::new(exhausted).unwrap()),Err(HnnError::QuadraticWorkExtent{..})));
        println!("QUADRATIC_DATA wide_bits1046/1046 exact_power=true signed_cross=true legacy_refuses=true native_accepts=true physical_coordinate_resource_refusals=true bitwork={}",b.spent);
        // Genuine unrun native Word/source binding for authority negatives, not a supplied W.
        use crate::hnn::tests::support::{small_field,contact};use crate::hnn::{Constitution,Current};
        let field=small_field(&[2,3],vec![contact(0,1,2,0)],0);let mut theta=Constitution::initial(&field,crate::hnn::constitution::CAMPAIGN_ONE_BUDGET).unwrap();theta.bind_arrival_context_receiving(0).unwrap();let current=Current::at_rest(&field);
        let ops=Operands::exact_at_cut(&field,&theta,&current).unwrap();let source=Arc::new(SourceMoment::open(&field,&current));
        let mut word=Word::on_operands(&field,ops.clone(),field.rings().iter().map(|r|vec![Rat::zero();r.width()]).collect()).unwrap();word.bind_source_producer(&theta,&current,source.clone()).unwrap();
        let producer=ActionProducer::native_forward(&word).unwrap();let prep=PortPreparation::new(&field,0,ExactRatMatrix::identity(field.ring(0).width()).unwrap()).unwrap();let control=vec![Rat::one();prep.controls()];let form=PowerForm::read(&field,&theta,&current).unwrap();
        let w=Witness::issue(&producer,&prep,&control,&form,&word,NativeWorkBudget::V1).unwrap();let accepted=w.admit(&producer,&prep,&control,&form,&word,&integer(65536),1024).unwrap();assert!(accepted.derived.work<=integer(65536));
        let wrong=producer.clone();let w=Witness::issue(&producer,&prep,&control,&form,&word,NativeWorkBudget::V1).unwrap();assert!(w.admit(&wrong,&prep,&control,&form,&word,&integer(65536),1024).is_err());
        let mut wrong_opening=producer.clone();wrong_opening.opening.storage[0][0]+=Rat::one();assert!(Witness::issue(&wrong_opening,&prep,&control,&form,&word,NativeWorkBudget::V1).is_err());
        let mut wrong_metric=form.clone();wrong_metric.step+=Rat::one();assert!(Witness::issue(&producer,&prep,&control,&wrong_metric,&word,NativeWorkBudget::V1).is_err());
        let mut wrong_source=producer.clone();wrong_source.source=Arc::new((*source).clone());assert!(Witness::issue(&wrong_source,&prep,&control,&form,&word,NativeWorkBudget::V1).is_err());
        let mut wrong_frame=producer.clone();wrong_frame.current=Current::at(&field,vec![BigInt::one();field.rings().len()]).unwrap();assert!(Witness::issue(&wrong_frame,&prep,&control,&form,&word,NativeWorkBudget::V1).is_err());
        // Exact operator cache versus original declaration; changed operator must miss.
        let receiver=&field.receivers()[0];let old=ReceivingPhases::declare(&field,&theta,&current,receiver).unwrap();let mut cache=crate::hnn::receiving::NativeRankCache::default();let new=cache.declare(&field,&theta,&current,receiver).unwrap();assert_eq!(old,new);assert_eq!(cache.declare(&field,&theta,&current,receiver).unwrap(),new);assert_eq!((cache.hits,cache.misses),(1,1));
        let mut declaration=field.declaration().clone();declaration.contacts[0].admittance+=Rat::one();let changed=Field::declare(declaration).unwrap();let changed_theta=Constitution::initial(&changed,crate::hnn::constitution::CAMPAIGN_ONE_BUDGET).unwrap();let changed_current=Current::at_rest(&changed);assert_ne!(ops,Operands::exact_at_cut(&changed,&changed_theta,&changed_current).unwrap());cache.declare(&changed,&changed_theta,&changed_current,&changed.receivers()[0]).unwrap();assert_eq!(cache.misses,2);
        // Same actual native F/score/return/work/carry under legacy declaration and the new capability.
        fn native_read(field:&Field,theta:&Constitution,current:&Current,source:Arc<SourceMoment>,phases:&ReceivingPhases,cache:Option<&mut crate::hnn::receiving::NativeRankCache>)->(crate::hnn::word::native_prediction::NativePredictionReading,Vec<crate::ratio::algebraic::ExactInterval>,WordBalance,crate::hnn::word::ReceptionCarry,Vec<crate::hnn::receiving::RetainedStationReturn>){
            let mut w=Word::open_received_view_exact(field,theta,current,&source,&crate::hnn::word::WordOpening::Rest,&crate::hnn::ring::modes::ModeView::whole()).unwrap();w.bind_source_producer(theta,current,source).unwrap();
            let p=if let Some(cache)=cache{let cap=w.declare_native_prediction(0,cache).unwrap();cap.run_and_read(w,64).unwrap()}else{w.run(phases.junction_steps()).unwrap();w.native_current_prediction(0,64).unwrap()};
            let reading=p.reading();let(carry,balance,_)=p.forward_receipt().unwrap();let target=crate::hnn::tests::support::encoded(field,&[1]);let returned=p.observe(&target).unwrap();(reading,returned.scores().to_vec(),balance,carry,returned.stations().to_vec())
        }
        let uncached=native_read(&field,&theta,&current,source.clone(),&old,None);
        let cached=native_read(&field,&theta,&current,source.clone(),&old,Some(&mut cache));assert_eq!(uncached,cached);
        let cold=native_read(&field,&theta,&current,source.clone(),&old,Some(&mut Default::default()));assert_eq!(cached,cold);
        let cap=word.declare_native_prediction(0,&mut cache).unwrap();let mut other=Word::on_operands(&field,ops.clone(),field.rings().iter().map(|r|vec![Rat::zero();r.width()]).collect()).unwrap();other.bind_source_producer(&theta,&current,source.clone()).unwrap();assert!(cap.run_and_read(other,64).is_err());
        println!("QUADRATIC_AUTH producer_source_frame_metric_refuse=true rank_cached_uncached_equal=true operator_change_misses=true full_native_F_return_work_carry_equal=true cold_cache_equal=true wrong_word_refuses=true");
    }
}
