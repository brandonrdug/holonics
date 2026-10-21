//! Known input-channel framing, not a distribution over possible source branches.
use super::*;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ContextChart { ScalarV1, SourceFramingRouteV1, LaggedReceiverBoundaryV1 }
impl ContextChart {
    pub(super) fn framed(self)->bool{self!=Self::ScalarV1}
    pub(super) fn formation_work(self)->u64{
        if self==Self::LaggedReceiverBoundaryV1{let d=2*self.features() as u64;d*d*d+10*d*d+10*d}else{1_000_000}
    }
    pub(super) fn features(self)->usize{if self==Self::LaggedReceiverBoundaryV1{90}else{25}}
}
/// Reached computational state, not a new exterior observation or predicted target.
/// Only the producing native Word can issue one. Cold restoration is bound by its parent Field.
#[derive(Clone,Debug,PartialEq,Eq)]
pub struct LaggedReceiverBoundary {
    pub(super) field:Field,
    pub(super) receiver:usize,
    pub(super) source_cells:u64,
    pub(super) commit:u64,
    pub(super) tick:usize,
    pub(super) lift:Vec<num_bigint::BigInt>,
    pub(super) contrast:Vec<Rat>,
    pub(super) role:PrefixRole,
}
impl LaggedReceiverBoundary {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn issued(field:&Field,receiver:usize,source_cells:u64,commit:u64,tick:usize,lift:&[num_bigint::BigInt],feature:&[Rat],role:PrefixRole)->Result<Self,HnnError>{
        if field.ring(receiver).width()!=6 || feature.len()!=12 || lift.len()!=field.rings().len(){return Err(refuse("lagged native context is the complete six-coordinate original receiver boundary"));}
        Ok(Self{field:field.clone(),receiver,source_cells,commit,tick,lift:lift.to_vec(),contrast:feature[6..].to_vec(),role})
    }
    pub fn role(&self)->PrefixRole{self.role}
    pub fn reached_tick(&self)->usize{self.tick}
    pub fn contrast(&self)->&[Rat]{&self.contrast}
    pub fn produced_source_cells(&self)->u64{self.source_cells}
}
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SourceFraming { source_cells: u64 }
impl SourceFraming {
    pub(crate) fn at(source: &SourceMoment) -> Self { Self { source_cells: source.cells() } }
    pub(super) fn restored(source_cells:u64, part:usize)->Result<Self,HnnError>{
        let f=Self{source_cells};if f.part()!=part{return Err(refuse("source framing matches its original absolute frontier"));}Ok(f)
    }
    pub fn source_cells(self)->u64{self.source_cells}
    pub fn part(self)->usize{(self.source_cells%4) as usize}
    pub fn bits(self)->Vec<bool>{vec![self.part()&2!=0,self.part()&1!=0]}
    pub fn schema(self)->&'static str{SOURCE_FRAMING_LAW}
}
#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn source_framing_original_part_restore_rejects_mismatch() {
        assert!(SourceFraming::restored(10,3).is_err());
        assert_eq!(SourceFraming::restored(10,2).unwrap().bits(),vec![true,false]);
    }
}
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PreparedMaterial {
    ScalarV1(EmpiricalMaterial),
    SourceFramingRouteV1(Box<[EmpiricalMaterial;4]>),
    LaggedReceiverBoundaryV1(Box<[EmpiricalMaterial;4]>),
}
impl PreparedMaterial {
    pub fn chart(&self)->ContextChart {match self {Self::ScalarV1(_)=>ContextChart::ScalarV1,Self::SourceFramingRouteV1(_)=>ContextChart::SourceFramingRouteV1,Self::LaggedReceiverBoundaryV1(_)=>ContextChart::LaggedReceiverBoundaryV1}}
    pub fn parts(&self)->&[EmpiricalMaterial]{match self {Self::ScalarV1(m)=>std::slice::from_ref(m),Self::SourceFramingRouteV1(m)|Self::LaggedReceiverBoundaryV1(m)=>m.as_ref()}}
    pub fn observations(&self)->u64{self.parts().iter().map(EmpiricalMaterial::observations).sum()}
    pub(super) fn fresh(chart:ContextChart)->Self{match chart {ContextChart::ScalarV1=>Self::ScalarV1(EmpiricalMaterial::found(25,4)),ContextChart::SourceFramingRouteV1=>Self::SourceFramingRouteV1(Box::new(std::array::from_fn(|_|EmpiricalMaterial::found(25,4)))),ContextChart::LaggedReceiverBoundaryV1=>Self::LaggedReceiverBoundaryV1(Box::new(std::array::from_fn(|_|EmpiricalMaterial::found(90,4))))}}
    pub(super) fn part(&self,frame:Option<SourceFraming>)->Result<&EmpiricalMaterial,HnnError>{match(self,frame){(Self::ScalarV1(m),None)=>Ok(m),(Self::SourceFramingRouteV1(m)|Self::LaggedReceiverBoundaryV1(m),Some(f))=>Ok(&m[f.part()]),_=>Err(refuse("material part belongs to its declared original context schema"))}}
    pub(super) fn replace(&mut self,frame:Option<SourceFraming>,next:EmpiricalMaterial)->Result<(),HnnError>{match(self,frame){(Self::ScalarV1(m),None)=>*m=next,(Self::SourceFramingRouteV1(m)|Self::LaggedReceiverBoundaryV1(m),Some(f))=>m[f.part()]=next,_=>return Err(refuse("material publication keeps its original context part"))};Ok(())}
    pub(super) fn text(&self)->String{match self{Self::ScalarV1(m)=>m.checkpoint_text(),Self::SourceFramingRouteV1(m)=>format!("source-framing-material-v1 {}",m.iter().map(|p|codec::hex(&p.checkpoint_text())).collect::<Vec<_>>().join(" ")),Self::LaggedReceiverBoundaryV1(m)=>format!("lagged-receiver-material-v1 {}",m.iter().map(|p|codec::hex(&p.checkpoint_text())).collect::<Vec<_>>().join(" "))}}
    pub(super) fn restored(chart:ContextChart,text:&str,b:&ContextualBounds)->Result<Self,HnnError>{
        let value=if chart==ContextChart::ScalarV1{Self::ScalarV1(EmpiricalMaterial::restored_text(text,25,4,b)?)}else{
            let mut t=text.split_whitespace();let tag=if chart==ContextChart::LaggedReceiverBoundaryV1{"lagged-receiver-material-v1"}else{"source-framing-material-v1"};
            if t.next()!=Some(tag){return Err(refuse("new context has four fresh separately retained material parts"));}
            let mut parts=Vec::new();for _ in 0..4{parts.push(EmpiricalMaterial::restored_text(&codec::unhex(t.next().ok_or(refuse("four context parts"))?)?,chart.features(),4,b)?);}
            if t.next().is_some(){return Err(refuse("exactly four context parts"));}let parts=Box::new(parts.try_into().map_err(|_|refuse("four parts"))?);
            if chart==ContextChart::LaggedReceiverBoundaryV1{Self::LaggedReceiverBoundaryV1(parts)}else{Self::SourceFramingRouteV1(parts)}
        };
        value.parts().iter().try_fold(0u64,|n,p|n.checked_add(p.observations()).ok_or(HnnError::CountOverflow))?;
        Ok(value)
    }
}

#[cfg(test)]
mod native_context_pure_controls {
    use super::*;
    #[test]
    fn native_context_pure_four_parts_have_fresh_ninety_feature_codec(){
        let b=ContextualBounds{branches:1,pending:64,precision_bits:20,rational_bits:1024,max_features:90,max_scalar_work:ContextChart::LaggedReceiverBoundaryV1.formation_work()};
        b.admit().unwrap();let m=PreparedMaterial::fresh(ContextChart::LaggedReceiverBoundaryV1);
        assert_eq!(m.parts().len(),4);assert!(m.parts().iter().all(|p|p.normal().len()==90&&p.observations()==0));
        assert_eq!(PreparedMaterial::restored(ContextChart::LaggedReceiverBoundaryV1,&m.text(),&b).unwrap(),m);
        assert!(PreparedMaterial::restored(ContextChart::SourceFramingRouteV1,&m.text(),&b).is_err());
        println!("NATIVE_CONTEXT_PURE90 four_fresh_parts=true versioned_codec=true no_old_moment_padding=true");
    }
}
