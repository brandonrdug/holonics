//! Known input-channel framing, not a distribution over possible source branches.
use super::*;
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ContextChart { ScalarV1, SourceFramingRouteV1 }
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
}
impl PreparedMaterial {
    pub fn chart(&self)->ContextChart {match self {Self::ScalarV1(_)=>ContextChart::ScalarV1,Self::SourceFramingRouteV1(_)=>ContextChart::SourceFramingRouteV1}}
    pub fn parts(&self)->&[EmpiricalMaterial]{match self {Self::ScalarV1(m)=>std::slice::from_ref(m),Self::SourceFramingRouteV1(m)=>m.as_ref()}}
    pub fn observations(&self)->u64{self.parts().iter().map(EmpiricalMaterial::observations).sum()}
    pub(super) fn fresh(chart:ContextChart)->Self{match chart {ContextChart::ScalarV1=>Self::ScalarV1(EmpiricalMaterial::found(25,4)),ContextChart::SourceFramingRouteV1=>Self::SourceFramingRouteV1(Box::new(std::array::from_fn(|_|EmpiricalMaterial::found(25,4))))}}
    pub(super) fn part(&self,frame:Option<SourceFraming>)->Result<&EmpiricalMaterial,HnnError>{match(self,frame){(Self::ScalarV1(m),None)=>Ok(m),(Self::SourceFramingRouteV1(m),Some(f))=>Ok(&m[f.part()]),_=>Err(refuse("material part belongs to its declared original context schema"))}}
    pub(super) fn replace(&mut self,frame:Option<SourceFraming>,next:EmpiricalMaterial)->Result<(),HnnError>{match(self,frame){(Self::ScalarV1(m),None)=>*m=next,(Self::SourceFramingRouteV1(m),Some(f))=>m[f.part()]=next,_=>return Err(refuse("material publication keeps its original context part"))};Ok(())}
    pub(super) fn text(&self)->String{match self{Self::ScalarV1(m)=>m.checkpoint_text(),Self::SourceFramingRouteV1(m)=>format!("source-framing-material-v1 {}",m.iter().map(|p|codec::hex(&p.checkpoint_text())).collect::<Vec<_>>().join(" "))}}
    pub(super) fn restored(chart:ContextChart,text:&str,b:&ContextualBounds)->Result<Self,HnnError>{
        let value=match chart {ContextChart::ScalarV1=>Self::ScalarV1(EmpiricalMaterial::restored_text(text,25,4,b)?),ContextChart::SourceFramingRouteV1=>{
            let mut t=text.split_whitespace();if t.next()!=Some("source-framing-material-v1"){return Err(refuse("new context has four fresh separately retained material parts"));}
            let mut parts=Vec::new();for _ in 0..4{parts.push(EmpiricalMaterial::restored_text(&codec::unhex(t.next().ok_or(refuse("four source framing parts"))?)?,25,4,b)?);}
            if t.next().is_some(){return Err(refuse("exactly four source framing parts"));}Self::SourceFramingRouteV1(Box::new(parts.try_into().map_err(|_|refuse("four parts"))?))}};
        value.parts().iter().try_fold(0u64,|n,p|n.checked_add(p.observations()).ok_or(HnnError::CountOverflow))?;
        Ok(value)
    }
}
