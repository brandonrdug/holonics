//! NativeRationalMomentsV1: bounded numerical denominators, separate from phase rows.
//! Old grouped arrays have no capability for this arithmetic. The represented W remains
//! on its original dyadic lattice; only exact statistics and transient proposals use it.
use super::*;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::hnn::constitution) struct NativeRationalBudget { pub integer_bits:u64, pub aggregate_bits:u64 }
impl NativeRationalBudget {
    pub(super) const V1:Self=Self{integer_bits:65536,aggregate_bits:1048576};
    pub(super) fn check(self,integer:u64,aggregate:u64)->Result<(),HnnError>{
        if self!=Self::V1 || integer>self.integer_bits || aggregate>self.aggregate_bits {
            return Err(HnnError::NativeRationalExtent{integer_bits:integer,integer_limit:self.integer_bits,aggregate_bits:aggregate,aggregate_limit:self.aggregate_bits});
        } Ok(())
    }
    /// Numeric bit extent of the retained array, including its cached L1.
    /// Local working-set checks add actual input arrays and transient copies.
    /// Whole-model retention still has the separate Constitution census.
    pub(super) fn payload(self,a:&EpochArray)->u64{
        a.values.iter().map(|x|x.bits()+1).sum::<u64>().saturating_add(a.denominator.bits())
            .saturating_add(a.numerator_l1_bound.bits()).saturating_add(a.row_divisors.iter().map(|x|u64::from(u64::BITS-x.leading_zeros())).sum::<u64>()).saturating_add(128)
    }
    pub(super) fn admit_view(self,a:&EpochArray,rat_copies:u64)->Result<(),HnnError>{
        let phase=a.row_divisors.iter().map(|d|u64::from(u64::BITS-d.leading_zeros())).max().unwrap_or(0);
        let d=a.denominator.bits().saturating_add(phase);let n=a.values.iter().map(BigInt::bits).max().unwrap_or(0);
        let view=a.values.iter().map(|v|v.bits().saturating_add(d).saturating_add(2)).sum::<u64>();
        self.check(n.max(d),self.payload(a).saturating_add(view.saturating_mul(rat_copies)).saturating_add(n.max(d).saturating_mul(12)))
    }
    pub(super) fn admit_rat_join(self,matrices:&[ExactRatMatrix])->Result<(),HnnError>{
        let bits=matrices.iter().flat_map(|m|m.entries()).map(|q|q.numer().bits().saturating_add(q.denom().bits()).saturating_add(2)).sum::<u64>();
        let limb=matrices.iter().flat_map(|m|m.entries()).map(|q|q.numer().bits().max(q.denom().bits())).max().unwrap_or(0);
        self.check(limb,bits.saturating_mul(2).saturating_add(limb.saturating_mul(12)))
    }
    pub(super) fn admit_array(self,a:&EpochArray)->Result<(),HnnError>{
        if !a.denominator.is_positive() || a.exponent!=0 || a.rows.checked_mul(a.columns)!=Some(a.values.len()) || a.row_divisors.len()!=a.rows || a.row_divisors.iter().any(|d|*d==0||d%2==0){return Err(refused("native rational array has canonical numerical denominator and semantic rows"));}
        let max=a.values.iter().map(BigInt::bits).max().unwrap_or(0).max(a.denominator.bits()).max(a.numerator_l1_bound.bits());
        let total=self.payload(a).saturating_add(max.saturating_mul(12));
        self.check(max,total)?;
        let mut common=a.denominator.clone();for v in &a.values{common=gcd(common,v.clone());}
        if common!=BigInt::one() || a.numerator_l1_bound!=a.values.iter().map(Signed::abs).sum(){return Err(refused("native rational coordinates and exact numerator census are canonical"));}Ok(())
    }
}
fn gcd(mut a:BigInt,mut b:BigInt)->BigInt{while !b.is_zero(){let r=&a%&b;a=b;b=r;}a.abs()}
impl EpochArray {
    pub(super) fn native_budget_with(&self,b:&Self)->Result<Option<NativeRationalBudget>,HnnError>{
        self.admit_grouped()?; b.admit_grouped()?;
        match(self.native_rational,b.native_rational){(Some(a),Some(b))if a!=b=>Err(refused("native rational operands keep the same resource declaration")),(Some(a),_)|(_,Some(a))=>Ok(Some(a)),_=>Ok(None)}
    }
    /// Every input is checked before LCM scaling/allocation; the aggregate includes
    /// inputs, denominator, scaled numerators and reduction scratch conservatively.
    pub(super) fn from_native_rows(rows:&[Vec<Rat>],divisors:Vec<u64>,b:NativeRationalBudget)->Result<Self,HnnError>{
        let n=rows.len();let m=rows.first().map_or(0,Vec::len);
        if rows.iter().any(|r|r.len()!=m)||divisors.len()!=n||divisors.iter().any(|d|*d==0||d%2==0){return Err(refused("native rational operand shape and semantic rows"));}
        let count=n.checked_mul(m).ok_or_else(extent)? as u64;
        let max_n=rows.iter().flatten().map(|q|q.numer().bits()).max().unwrap_or(0);
        let max_d=rows.iter().flatten().map(|q|q.denom().bits()).max().unwrap_or(0);
        let input=rows.iter().flatten().map(|q|q.numer().bits().saturating_add(q.denom().bits()).saturating_add(2)).sum::<u64>();
        b.check(max_n.max(max_d),input.saturating_add(max_n.max(max_d).saturating_mul(12)))?;
        let mut denominator=BigInt::one();
        for q in rows.iter().flatten(){
            let left=&denominator/gcd(denominator.clone(),q.denom().clone());
            let d=left.bits().saturating_add(q.denom().bits());
            let mut total_n=0u64;let mut largest=0u64;
            for (i,r) in rows.iter().enumerate(){for x in r{
                let bits=if x.is_zero(){0}else{x.numer().bits().saturating_add(d.saturating_sub(x.denom().bits().saturating_sub(1))).saturating_add(u64::from(u64::BITS-divisors[i].leading_zeros()))};
                total_n=total_n.saturating_add(bits+1);largest=largest.max(bits);
            }}
            let l1=largest.saturating_add(u64::from(u64::BITS-count.max(1).leading_zeros()));
            b.check(largest.max(d).max(l1),input.saturating_add(total_n).saturating_add(d).saturating_add(l1).saturating_add(largest.max(d).saturating_mul(12)))?;
            denominator=left*q.denom();
        }
        let mut values=Vec::with_capacity(count as usize);
        for (i,r) in rows.iter().enumerate(){for q in r{values.push(q.numer()*(&denominator/q.denom())*divisors[i]);}}
        Self::from_native_parts(n,m,values,denominator,divisors,b)
    }
    fn from_native_parts(rows:usize,columns:usize,mut values:Vec<BigInt>,mut denominator:BigInt,row_divisors:Vec<u64>,b:NativeRationalBudget)->Result<Self,HnnError>{
        let max=values.iter().map(BigInt::bits).max().unwrap_or(0);let l1=max.saturating_add(usize::BITS as u64-values.len().max(1).leading_zeros() as u64);
        let live=values.iter().map(|n|n.bits()+1).sum::<u64>().saturating_add(denominator.bits()).saturating_add(l1).saturating_add(12*max.max(denominator.bits()));
        b.check(max.max(denominator.bits()).max(l1),live)?;
        let mut common=denominator.clone();for v in &values{common=gcd(common,v.clone());}
        if common>BigInt::one(){denominator/=&common;for v in &mut values{*v/=&common;}}
        let a=Self{rows,columns,numerator_l1_bound:values.iter().map(Signed::abs).sum(),values,denominator,exponent:0,row_divisors,native_rational:Some(b)};
        b.admit_array(&a)?;Ok(a)
    }

    fn native_preflight(&self,other:&Self,b:NativeRationalBudget,count:usize,terms:usize,phase_bits:u64)->Result<(),HnnError>{
        // Every summand has one shared numerical denominator. Summation adds
        // log2(terms) numerator bits, not terms independent denominator products.
        let n=|a:&Self|a.values.iter().map(BigInt::bits).max().unwrap_or(0);
        let numerator=n(self).saturating_add(n(other)).max(n(self).saturating_add(other.denominator.bits())).max(n(other).saturating_add(self.denominator.bits()))
            .saturating_add(phase_bits).saturating_add(usize::BITS as u64-terms.max(1).leading_zeros() as u64).saturating_add(4);
        let denominator=self.denominator.bits().saturating_add(other.denominator.bits()).saturating_add(phase_bits);
        let inputs=b.payload(self).saturating_add(b.payload(other));
        // Shared D is allocated once. Dense output N plus at most six integer
        // product/sum/gcd scratch operands; no per-entry rational normalization.
        let total=(count as u64).saturating_add(6).saturating_mul(numerator).saturating_add(denominator.saturating_mul(6)).saturating_add(inputs);
        b.check(numerator.max(denominator),total)
    }

    pub(super) fn native_binary(&self,other:&Self,b:NativeRationalBudget,subtract:bool)->Result<Self,HnnError>{
        self.same_shape(other)?;
        let inputs=b.payload(self).saturating_add(b.payload(other));let scratch=self.denominator.bits().max(other.denominator.bits());b.check(scratch,inputs.saturating_add(12*scratch))?;
        let common=gcd(self.denominator.clone(),other.denominator.clone());
        let left=&other.denominator/&common;let right=&self.denominator/&common;
        let d=right.bits().saturating_add(other.denominator.bits());
        let mut sum=0u64;let mut largest=d;
        for (i,(x,y)) in self.values.iter().zip(&other.values).enumerate(){
            let row=i/self.columns;let div=common_odd(self.row_divisors[row],other.row_divisors[row])?;
            let a=x.bits().saturating_add(left.bits()).saturating_add(u64::from(u64::BITS-(div/self.row_divisors[row]).leading_zeros()));
            let c=y.bits().saturating_add(right.bits()).saturating_add(u64::from(u64::BITS-(div/other.row_divisors[row]).leading_zeros()));
            let n=a.max(c).saturating_add(1);largest=largest.max(n);sum=sum.saturating_add(n+1);
        }
        let l1=largest.saturating_add(usize::BITS as u64-self.values.len().max(1).leading_zeros() as u64);
        b.check(l1,inputs.saturating_add(sum).saturating_add(d).saturating_add(l1).saturating_add(12*largest))?;
        let denominator=&right*&other.denominator;
        let divisors=self.row_divisors.iter().zip(&other.row_divisors).map(|(a,c)|common_odd(*a,*c)).collect::<Result<Vec<_>,_>>()?;
        let left=&denominator/&self.denominator;let right=&denominator/&other.denominator;
        let values=self.values.iter().zip(&other.values).enumerate().map(|(i,(x,y))|{
            let row=i/self.columns;let a=x*&left*(divisors[row]/self.row_divisors[row]);let c=y*&right*(divisors[row]/other.row_divisors[row]);if subtract{a-c}else{a+c}
        }).collect();
        Self::from_native_parts(self.rows,self.columns,values,denominator,divisors,b)
    }
    pub(super) fn native_multiply(&self,other:&Self,b:NativeRationalBudget)->Result<Self,HnnError>{
        if self.columns!=other.rows{return Err(refused("native rational product meets its ports"));}
        let odd=other.row_divisors.iter().try_fold(1,|a,&v|common_odd(a,v))?;
        self.native_preflight(other,b,self.rows.checked_mul(other.columns).ok_or_else(extent)?,self.columns,u64::from(u64::BITS-odd.leading_zeros()))?;
        let denominator=&self.denominator*&other.denominator*odd;
        let mut values=vec![BigInt::zero();self.rows*other.columns];
        for i in 0..self.rows{for k in 0..self.columns{for j in 0..other.columns{values[i*other.columns+j]+=&self.values[i*self.columns+k]*&other.values[k*other.columns+j]*(odd/other.row_divisors[k]);}}}
        Self::from_native_parts(self.rows,other.columns,values,denominator,self.row_divisors.clone(),b)
    }
    pub(super) fn native_dot(&self,other:&Self,b:NativeRationalBudget)->Result<Self,HnnError>{
        self.same_shape(other)?;
        // Phase products are numerical here, never a new semantic period/u64.
        let mut odd=BigInt::one();for (a,c) in self.row_divisors.iter().zip(&other.row_divisors){let p=BigInt::from(*a)*c;
            b.check(odd.bits().saturating_add(p.bits()),b.payload(self).saturating_add(b.payload(other)).saturating_add(12*(odd.bits()+p.bits())))?;
            odd=(&odd/gcd(odd.clone(),p.clone()))*p;}
        self.native_preflight(other,b,1,self.values.len(),odd.bits())?;
        let numerator=self.values.iter().zip(&other.values).enumerate().map(|(i,(a,c))|a*c*(&odd/(BigInt::from(self.row_divisors[i/self.columns])*other.row_divisors[i/self.columns]))).sum();
        Self::from_native_parts(1,1,vec![numerator],&self.denominator*&other.denominator*odd,vec![1],b)
    }
    pub(super) fn native_scale(&self,q:&Rat,b:NativeRationalBudget)->Result<Self,HnnError>{
        let scalar=Self::from_native_rows(&[vec![q.clone()]],vec![1],b)?;self.native_preflight(&scalar,b,self.values.len(),1,0)?;
        Self::from_native_parts(self.rows,self.columns,self.values.iter().map(|v|v*q.numer()).collect(),&self.denominator*q.denom(),self.row_divisors.clone(),b)
    }

}
impl EpochLaw {
    /// Named exact embedding. Caller owns fresh native receiving declaration; it
    /// does not reinterpret archived legacy checkpoints or change prior/chart units.
    pub(super) fn into_native_rational(mut self)->Result<Self,HnnError>{
        if self.source_refinement||self.symmetry.is_some(){return Err(refused("native rational moments are scoped to receiving blocks"));}
        let b=NativeRationalBudget::V1;
        self.gram=EpochArray::from_native_rows(&self.gram.to_rows(),self.gram.row_divisors.clone(),b)?;
        self.news=EpochArray::from_native_rows(&self.news.to_rows(),self.news.row_divisors.clone(),b)?;
        self.native_rational=Some(b);Ok(self)
    }
    pub(super) fn native_direction(&self,news:&EpochArray,gram:&EpochArray,support:&[usize],b:NativeRationalBudget)->Result<(EpochArray,Vec<i64>),HnnError>{
        if gram.row_divisors.iter().any(|d|*d!=1){return Err(refused("native normal Gram has no semantic phase rows"));}
        let mut shares=vec![0;self.map.columns];let mut reached=vec![false;shares.len()];
        let input=b.payload(gram).saturating_add(b.payload(news));
        let max=gram.values.iter().map(BigInt::bits).max().unwrap_or(0).saturating_add(usize::BITS as u64-gram.rows.max(1).leading_zeros() as u64);
        b.check(max.max(gram.denominator.bits()),input.saturating_add(12*max.max(gram.denominator.bits())))?;
        for &j in support{if j>=shares.len(){return Err(refused("native rational direction has declared support"));}reached[j]=true;
            let mass:BigInt=(0..gram.rows).map(|i|gram.values[i*gram.columns+j].abs()).sum();if !mass.is_positive(){return Err(refused("reached native column has positive conductance"));}
            let mut k=mass.bits() as i64-gram.denominator.bits() as i64;
            let below=if k>=0{(&gram.denominator<<k as usize)<mass}else{gram.denominator<(&mass<<(-k) as usize)};
            if below{k+=1;}shares[j]=k;
        }
        let shift=support.iter().map(|j|shares[*j]).max().unwrap_or(0).max(0) as u64;
        let d=news.denominator.bits().saturating_add(shift);let mut sum=0u64;let mut largest=d;
        for (i,n) in news.values.iter().enumerate(){if reached[i%news.columns]{let bits=n.bits().saturating_add((shift as i64-shares[i%news.columns]) as u64);sum=sum.saturating_add(bits+1);largest=largest.max(bits);}}
        b.check(largest,input.saturating_add(sum).saturating_add(d).saturating_add(12*largest))?;
        let values=news.values.iter().enumerate().map(|(i,n)|if reached[i%news.columns]{n<<((shift as i64-shares[i%news.columns]) as usize)}else{BigInt::zero()}).collect();
        Ok((EpochArray::from_native_parts(news.rows,news.columns,values,&news.denominator<<shift as usize,news.row_divisors.clone(),b)?,shares))
    }
}

#[cfg(test)]
mod tests{
 use super::*;
 fn q(n:i64,d:i64)->Rat{Rat::new(n.into(),d.into())}
 #[test]
 fn native_rational_full_normal_phase_codec()->Result<(),HnnError>{
    let b=NativeRationalBudget::V1;
    let mut first=EpochLaw::founded(4,2,6,0)?.with_phase_rows(&[1,3],11)?.into_native_rational()?;
    first.receiving_refinement=Some(20);first.map_lattice=20;
    let samples=vec![Sample{weight:Rat::one(),feature:vec![q(-32,2187),q(3,5)],covector:vec![q(1,4),q(1,33),q(-1,4),q(-1,55)],masses:None},Sample{weight:Rat::one(),feature:vec![q(1,2),q(-1,5)],covector:vec![q(1,8),q(-1,77),q(-1,8),q(1,121)],masses:None}];
    let flow=EpochFlow::from_native_samples(4,2,6,10,0,2,&samples,&[1,3],11)?;
    let f=flow.gram.to_rows();let g=flow.covector.to_rows();
    for i in 0..2{for j in 0..2{assert_eq!(f[i][j],samples.iter().map(|s|&s.feature[i]*&s.feature[j]).sum());}}
    for i in 0..4{for j in 0..2{assert_eq!(g[i][j],samples.iter().map(|s|&s.covector[i]*&s.feature[j]).sum());}}
    assert_eq!(q(-32,2187)*q(-32,2187),q(1024,4782969));assert_eq!(q(-32,2187)*q(1,4),q(-8,2187));
    let parts=samples.iter().enumerate().map(|(i,s)|{
        let foil=if i==0{vec![q(3,4),Rat::zero(),q(1,4),Rat::zero()]}else{vec![q(7,8),Rat::zero(),q(1,8),Rat::zero()]};
        super::super::deposit::EpochReceivingRecord{law:EpochReceivingLaw::CoarseOdometerV1,feature:s.feature.clone(),positive:vec![Rat::one(),Rat::zero(),Rat::zero(),Rat::zero()],foil,phase:vec![Rat::zero(),s.covector[1].clone(),Rat::zero(),s.covector[3].clone()]}
    }).collect::<Vec<_>>();
    // Algebra-only split diagnostic, no manufactured native origin/certificate.
    let (positive,foil,phase)=super::super::deposit::receiving_series_in_carrier(&samples,&parts,4,2,11,true)?;
    assert_eq!(positive.subtract(&foil)?.add(&phase)?.to_rows(),flow.covector.to_rows());
    let fresh=first.fresh(&flow)?;assert!(fresh.alignment.scalar_ratio()?.is_positive());
    let h=first.gram.add(&flow.gram)?.to_rows();for j in 0..2{let mass:Rat=h.iter().map(|r|r[j].abs()).sum();let k=fresh.shares[j];let pow=if k>=0{Rat::from_integer(BigInt::one()<<k as usize)}else{Rat::new(1.into(),BigInt::one()<<(-k) as usize)};assert!(mass<=pow&&mass>pow/q(2,1));}
    let gain=EpochArray::from_dyadic_scalar(&q(1,64))?;
    let d=first.deposited_at(&flow,&gain,1.into(),1.into())?;assert!(!d.step.is_zero());
    let held=first.deposited_at(&flow,&gain,0.into(),1.into())?;assert!(held.step.is_zero());assert_eq!(held.successor.map,first.map);
    for successor in [&d.successor,&held.successor]{let rhs=first.map.multiply(&successor.gram)?.add(&first.news)?.add(&flow.covector.scalar_product(&gain)?)?;assert_eq!(successor.map.multiply(&successor.gram)?.add(&successor.news)?,rhs);let text=successor.encode_checkpoint();assert!(text.starts_with("epoch-law-native-rational-moments-v1"));assert_eq!(EpochLaw::decode_checkpoint(&text,&first,1<<24)?,*successor);assert_eq!(successor.news.row_divisors,vec![1,11,1,11]);assert!(EpochLaw::decode_checkpoint(&text.replace("65536 1048576","65535 1048576"),&first,1<<24).is_err());}
    let mut wrong=first.clone();wrong.news.row_divisors[1]=13;assert!(super::super::checkpoint::validate(&d.successor,&wrong).is_err());
    let shared=Rat::new(BigInt::from(3),(BigInt::one()<<521usize)+BigInt::from(17));
    let repeated=vec![vec![shared.clone();6];6];
    let compact=EpochArray::from_native_rows(&repeated,vec![1;6],b)?;assert_eq!(compact.to_rows(),repeated);assert!(compact.denominator.bits()<600);
    println!("RATIONAL_SHARED_DENOMINATOR resource_cap_unchanged=true numerical_D_bits={} entries36_not36independent_products=true",compact.denominator.bits());
    let huge=Rat::new(1.into(),(BigInt::one()<<80usize)+BigInt::from(3));let a=EpochArray::from_native_rows(&[vec![huge.clone()]],vec![1],b)?;assert_eq!(a.to_rows(),vec![vec![huge]]);
    let too_big=Rat::new(1.into(),BigInt::one()<<65537usize);assert!(EpochArray::from_native_rows(&[vec![too_big]],vec![1],b).is_err());
    // Old grouped admission and device packing still reject numerical odd factors.
    assert!(EpochArray::from_dyadic_matrix(&rows_matrix(&[vec![q(-32,2187)]])).is_err());
    let reading=super::super::device::EpochRecordFlowReading{gram:EpochSeriesReading::of(&flow.gram),covector:EpochSeriesReading::of(&flow.covector),support:flow.support.clone(),records:2,heard_cells:2,declared_cells:10,partition_exponent:flow.partition_exponent};assert!(super::super::device::epoch_record_flow_canonicalize(reading).is_err());
    // Dyadic subset embedding changes the declared carrier, never any numeric owner.
    let old=EpochLaw::founded(2,1,6,0)?.with_phase_rows(&[1],11)?;
    let s=vec![Sample{weight:Rat::one(),feature:vec![q(1,2)],covector:vec![q(1,4),q(1,22)],masses:None}];
    let records=s.iter().map(|s|EpochRecord::from_sample_with_phase_rows(s,&[1],11)).collect::<Result<Vec<_>,_>>()?;
    let of=EpochFlow::from_records(2,1,6,10,0,1,&records)?;let nf=EpochFlow::from_native_samples(2,1,6,10,0,1,&s,&[1],11)?;let native=old.clone().into_native_rational()?;
    let od=old.deposit(&of,&gain)?;let nd=native.deposit(&nf,&gain)?;
    for (a,c) in [(&od.successor.map,&nd.successor.map),(&od.successor.gram,&nd.successor.gram),(&od.successor.news,&nd.successor.news),(&od.step,&nd.step)]{assert_eq!(a.to_rows(),c.to_rows());}
    assert_eq!(od.fall.scalar_ratio()?,nd.fall.scalar_ratio()?);
    println!("NATIVE_RATIONAL_FULL_ROUTE_PASS feature=-32/2187 two_station_mixed_2_3_5 numerical_odd_gt_u64 phase_period11 support={:?} shares={:?} represented_delta={:?} H={:?} news={:?} held_once=true dyadic_subset_equal=true cold_exact=true device_refuses=true",flow.support,fresh.shares,d.step.to_rows(),d.successor.gram.to_rows(),d.successor.news.to_rows());Ok(())
 }
}

#[cfg(test)]
mod resource_controls{
 use super::*;
 #[test]
 fn native_rational_resource_width6()->Result<(),HnnError>{
    let b=NativeRationalBudget::V1;
    let d=(BigInt::one()<<768usize)+BigInt::from(17);
    let v=(0..6).map(|i|Rat::new((BigInt::one()<<766usize)+BigInt::from(i*2+1),d.clone())).collect::<Vec<_>>();
    let h=(0..6).map(|i|(0..6).map(|j|&v[i]*&v[j]+if i==j{Rat::one()}else{Rat::zero()}).collect()).collect::<Vec<_>>();
    let mut law=EpochLaw::founded(4,6,6,0)?.with_phase_rows(&[1,3],11)?.into_native_rational()?;law.receiving_refinement=Some(20);
    law.gram=EpochArray::from_native_rows(&h,vec![1;6],b)?;
    let gram_limb=law.gram.values.iter().map(BigInt::bits).max().unwrap();assert!(gram_limb>=1535);
    let (minor,temp,live)=super::super::checkpoint::native_bareiss_workspace(&law,b)?;
    let old=gram_limb.saturating_mul(2640).saturating_add(8800);assert!(old>b.aggregate_bits&&live<=b.aggregate_bits);
    let text=law.encode_checkpoint();assert_eq!(EpochLaw::decode_checkpoint(&text,&law,1<<24)?,law);
    let news=EpochArray::from_native_rows(&vec![vec![Rat::new(1.into(),3.into());6];4],vec![1,11,1,11],b)?;
    let support=(0..6).collect::<Vec<_>>();let (direction,shares)=law.native_direction(&news,&law.gram,&support,b)?;
    let n=news.to_rows();let actual=direction.to_matrix()?.to_rows();
    for j in 0..6{let mass:Rat=h.iter().map(|r|r[j].abs()).sum();let p=if shares[j]>=0{Rat::from_integer(BigInt::one()<<shares[j] as usize)}else{Rat::new(1.into(),BigInt::one()<<(-shares[j]) as usize)};assert!(mass<=p&&mass>&p/Rat::from_integer(2.into()));for i in 0..4{assert_eq!(actual[i][j],&n[i][j]/&p);}}
    let mut bad=law.clone();bad.gram.values[0]=-bad.gram.values[0].abs();bad.gram.numerator_l1_bound=bad.gram.values.iter().map(Signed::abs).sum();assert!(EpochLaw::decode_checkpoint(&bad.encode_checkpoint(),&law,1<<24).is_err());
    let compact=EpochArray::from_native_parts(6,6,vec![BigInt::one();36],(BigInt::one()<<25000usize)+BigInt::one(),vec![1;6],b)?;
    assert!(compact.to_matrix().is_err()); // grouped payload fits, expanded Rat copies do not
    let sum=compact.add(&compact)?;assert_eq!(sum.denominator,compact.denominator);assert!(sum.values.iter().all(|n|n==&BigInt::from(2)));
    assert!(sum.subtract(&sum)?.is_zero());
    let huge=EpochArray::from_native_parts(1,1,vec![BigInt::one()],(BigInt::one()<<40000usize)+BigInt::one(),vec![1],b)?;
    assert!(huge.multiply(&huge).is_err()); // genuine product extent still refuses
    println!("RATIONAL_RESOURCE_WIDTH6_PASS gram_integer_bits={gram_limb} old_false_aggregate={old} in_place_minor_bits={minor} scalar_product_bits={temp} live_working_bits={live} caps=65536/1048576 cached_l1_counted=true expanded_view_refused=true actual_lcm_add_pass=true positive_definite_check_preserved=true shares={shares:?}");Ok(())
 }
}
