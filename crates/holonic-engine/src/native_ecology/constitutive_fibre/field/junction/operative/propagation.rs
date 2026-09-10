//! Causal propagation and source-qualified history under the existing field owner.
//! Standalone staging, live passages and historical decoding share the same native word.
use super::*;
use crate::resident_section::CausalPropagationLayout as Layout;
use num_bigint::BigInt;
use num_traits::One;
pub(super) mod return_path;

impl NativeConstitutiveField<'_> {
    pub fn causal_contact_propagation_from(&self) -> Option<usize> {
        self.junction.as_ref().and_then(|j|j.operative.as_ref()).and_then(|o|o.propagate_from)
    }
    /// Admit causal contact propagation from the next occurrence. The existing interior
    /// propagates before a new zero-input contact is born; the same field owns the successor.
    pub fn enable_causal_contact_propagation(&mut self) -> Result<(),Error> {
        if !self.relation.usable || self.pending.is_some(){return Err(Error::Uncertain);}
        if self.transport.as_ref().is_some_and(|t|!t.source.is_operative()){
            return Err(invalid("causal propagation requires an operative material-source chart"));
        }
        self.enable_operative_contacts()?;self.retain_operative_map_program()?;
        let cut=self.history.len();let op=self.junction.as_mut().unwrap().operative.as_mut().unwrap();
        op.propagate_from.get_or_insert(cut);Ok(())
    }
}

impl<'c> NativeConstitutiveField<'c> {
    pub(super) fn operative_before_current(&self,source:usize) -> Result<(Rc<ResidentSection<'c>>,usize),Error> {
        let op=self.junction.as_ref().and_then(|j|j.operative.as_ref()).ok_or(Error::Shape)?;
        if source<op.activated_at || source>=self.history.len(){return Err(Error::ForeignOccurrence);}
        let count=op.births.partition_point(|b|b.receiving<source);let surface=self.relation.surface;
        let mut before=if source==op.activated_at {Rc::clone(&op.initial.b)} else {
            self.history[source-1].with_resident(surface,|r| {
                let state=r.operative.as_ref().ok_or(Error::Uncertain)?;
                if state.count!=count{return Err(Error::Shape);}Ok(Rc::clone(&state.b))
            })?
        };
        for r in op.returns.iter().filter(|r|r.at_cut==source) {
            if let Some(delta)=&r.b {
                if r.contact_count!=count{return Err(Error::Shape);}
                let out=Rc::new(surface.fresh_section(count.max(1),4,ResidentGrain(0))?);
                let mut passage=surface.begin_passage(&[vec![]])?;
                {let lane=passage.open(0,&[])?;surface.record_operative_input_current_add(&lane,&before,delta,count,&out)?;}
                passage.close(0,&out,64)?;
                let receipt=passage.finish()?.launch()?;
                if !receipt.obstruction.is_empty(){return Err(Error::Arithmetic(format!("source input current: {:?}",receipt.obstruction)));}
                before=out;
            }
        }
        Ok((before,count))
    }

    pub(super) fn operative_source_propagation(&self,source:usize,source_map:Option<&Rc<ResidentSection<'c>>>)
        -> Result<Option<NativeCausalContactPropagation<'_,'c>>,Error> {
        let op=self.junction.as_ref().and_then(|j|j.operative.as_ref()).ok_or(Error::Shape)?;
        if source>=self.history.len(){return Err(Error::ForeignOccurrence);}
        if op.propagate_from.is_none_or(|from|source<from){return Ok(None);}
        let surface=self.relation.surface;
        let count=op.births.partition_point(|b|b.receiving<source);
        let bounds=self.history[source].with_resident(surface,|r|r.operative.as_ref()
            .and_then(|o|o.propagation_input_bounds.clone()).ok_or(Error::Uncertain))?;
        let map=match source_map {Some(map)=>Rc::clone(map),None=>self.operative_producing_map(source)?};
        let word=if let Some((_,word))=op.recent_propagations.iter().find(|(at,_)|*at==source) {
            if word.count!=count{return Err(Error::Shape);}Rc::clone(word)
        }else{
            let (before,before_count)=self.operative_before_current(source)?;
            if before_count!=count{return Err(Error::Shape);}
            let word=CausalPropagationSections::prepare(surface,&op.births[..count])?;
            let mut passage=surface.begin_passage(&[vec![]])?;
            {let lane=passage.open(0,&[])?;word.record(surface,&lane,[&map,&before,&bounds],self.nodes(),op.grain)?;}
            passage.close(0,&word.bounds,64)?;
            let receipt=passage.finish()?.launch()?;
            if !receipt.obstruction.is_empty(){return Err(Error::Arithmetic(format!("source propagation: {:?}",receipt.obstruction)));}
            word
        };
        Ok(Some(NativeCausalContactPropagation{field:self,at_cut:source,_origin:Rc::new(()),source_map:map,source_bounds:bounds,
            births:op.births[..count].to_vec(),grain:op.grain,word}))
    }
}

pub(in super::super::super) struct CausalPropagationSections<'c> {
    births:Rc<ResidentSection<'c>>,
    pub(in super::super::super) current:Rc<ResidentSection<'c>>,
    pub(in super::super::super) bounds:Rc<ResidentSection<'c>>,
    pub(super) trace:Rc<ResidentSection<'c>>,
    summary:Rc<ResidentSection<'c>>,
    pub(super) count:usize,
}

impl<'c> CausalPropagationSections<'c> {
    pub(in super::super::super) fn prepare(surface:&'c ResidentSurface<'c>,births:&[NativeOperativeContactBirth]) -> Result<Rc<Self>,Error> {
        let count=births.len();let mut addresses=Vec::with_capacity(2*count.max(1));
        for birth in births {for at in [birth.source,birth.receiving] {
            let at=i64::try_from(at).map_err(invalid)?;addresses.push((at,at));
        }}
        if addresses.is_empty(){addresses.resize(2,(0,0));}
        Ok(Rc::new(Self {
            births:Rc::new(surface.mount_section_rest(&ResidentSectionRest::found(count.max(1),2,ResidentGrain(0),64,addresses).map_err(invalid)?)?),
            current:Rc::new(surface.fresh_section(count.max(1),4,ResidentGrain(0))?),
            bounds:Rc::new(surface.fresh_section(1,4,ResidentGrain(0))?),
            trace:Rc::new(surface.fresh_section(count.max(1),Layout::WORDS,ResidentGrain(0))?),
            summary:Rc::new(surface.fresh_section(1,4,ResidentGrain(0))?),count,
        }))
    }
    pub(in super::super::super) fn record(&self,surface:&'c ResidentSurface<'c>,lane:&crate::resident_section::Lane<'_,'c>,
        input:[&ResidentSection<'c>;3],nodes:usize,grain:u32) -> Result<(),Error> {
        Ok(surface.record_causal_contact_propagation(lane,&self.births,input,6*nodes,self.count,grain,
            &self.current,&self.bounds,&self.trace,&self.summary)?)
    }
}

pub struct NativeCausalContactPropagation<'f, 'c> {
    field: &'f NativeConstitutiveField<'c>,
    at_cut:usize,
    _origin: Rc<()>,
    source_map:Rc<ResidentSection<'c>>,
    source_bounds:Rc<ResidentSection<'c>>,
    births: Vec<NativeOperativeContactBirth>,
    grain: u32,
    pub(super) word:Rc<CausalPropagationSections<'c>>,
}

#[derive(Debug, Serialize)]
pub struct NativeCausalContactJoinReading {
    pub before: usize,
    pub after: usize,
    pub joining_occurrence: usize,
    pub incoming_pair: Vec<ExactComplexWaveCurrent>,
    pub incoming_radius: Rat,
    pub overlap: ExactComplexWaveCurrent,
    pub overlap_error: Rat,
    pub omitted_components: usize,
}

#[derive(Debug, Serialize)]
pub struct NativeCausalContactPropagationReading {
    pub field_cut: usize,
    pub fractional_bits: u32,
    pub internal: NativeFieldCurrentBall,
    pub contact_radius: Rat,
    pub rounding_radius: Rat,
    pub joins: Vec<NativeCausalContactJoinReading>,
}

impl<'f, 'c> NativeOperativeContactStaging<'f, 'c> {
    /// The device finds joins from this field's chronology and evaluates the complete word.
    /// This returns fresh current/trace carriers without changing the borrowed continuing field.
    pub fn propagate_causal_contacts(
        &self,
    ) -> Result<NativeCausalContactPropagation<'f, 'c>, Error> {
        let surface = self.field.relation.surface;
        let word=CausalPropagationSections::prepare(surface,&self.births)?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            word.record(surface,&lane,self.sections.current(),self.field.nodes(),self.grain)?;
        }
        passage.close(0, &word.bounds, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "causal contact propagation: {:?}",
                receipt.obstruction
            )));
        }
        Ok(NativeCausalContactPropagation {
            field: self.field,
            at_cut:self.field_cut(),
            _origin: Rc::clone(&self.origin),
            source_map:Rc::clone(&self.sections.map),source_bounds:Rc::clone(&self.sections.bounds),
            births: self.births.clone(),
            grain: self.grain,
            word,
        })
    }
}

impl NativeCausalContactPropagation<'_, '_> {
    /// Cold numerical observation. Staging itself performs no section readout.
    pub fn inspect(&self) -> Result<NativeCausalContactPropagationReading, Error> {
        let surface = self.field.relation.surface;
        let read = |s: &ResidentSection<'_>| surface.detach_section(s, 64).map_err(Error::from);
        let current = wides(&read(&self.word.current)?.intervals)?;
        let bounds = wides(&read(&self.word.bounds)?.intervals)?;
        let summary = wides(&read(&self.word.summary)?.intervals)?;
        let trace = read(&self.word.trace)?;
        let scale = BigInt::one() << self.grain;
        let rat = |v: i128| Rat::new(v.into(), scale.clone());
        let waves = |values: &[i128]| {
            values
                .chunks_exact(2)
                .map(|v| ExactComplexWaveCurrent::new(rat(v[0]), rat(v[1])))
                .collect::<Vec<_>>()
        };
        let history = |wire: &[(i64, i64)]| -> Result<Rat, Error> {
            if wire.len() != Layout::HISTORY_WORDS
                || wire.iter().any(|(a, b)| a != b)
                || !matches!(wire[Layout::HISTORY_WORDS - 1].0, 0 | 1)
            {
                return Err(Error::Shape);
            }
            let mut value = BigInt::from(0);
            for (at, part) in wire[..Layout::HISTORY_WORDS - 1].iter().enumerate() {
                value += BigInt::from(part.0 as u64) << (at * u64::BITS as usize);
            }
            if wire[Layout::HISTORY_WORDS - 1].0 != 0 {
                value = -value;
            }
            Ok(Rat::new(value, &scale * &scale))
        };
        let mut joins = Vec::new();
        for (after, row) in trace
            .intervals
            .chunks_exact(Layout::WORDS)
            .take(self.births.len())
            .enumerate()
        {
            if row.iter().any(|(a, b)| a != b)
                || row[1].0 != i64::try_from(self.births[after].receiving).map_err(invalid)?
            {
                return Err(Error::Shape);
            }
            if row[0].0 == -1 {
                continue;
            }
            let before = usize::try_from(row[0].0).map_err(invalid)?;
            if before >= after || self.births[before].receiving != self.births[after].source {
                return Err(Error::Shape);
            }
            let incoming = waves(&wides(&row[Layout::BEFORE..Layout::OVERLAP])?);
            let radius = wides(&row[Layout::RADIUS..Layout::OVERLAP_ERROR])?[0];
            let omitted = wides(&row[Layout::ROUNDS..Layout::WORDS])?[0];
            joins.push(NativeCausalContactJoinReading {
                before,
                after,
                joining_occurrence: self.births[after].source,
                incoming_pair: incoming,
                incoming_radius: rat(radius),
                overlap: ExactComplexWaveCurrent::new(
                    history(&row[Layout::OVERLAP..Layout::OVERLAP + Layout::HISTORY_WORDS])?,
                    history(&row[Layout::OVERLAP + Layout::HISTORY_WORDS..Layout::RADIUS])?,
                ),
                overlap_error: history(
                    &row[Layout::OVERLAP_ERROR..Layout::OVERLAP_ERROR + Layout::HISTORY_WORDS],
                )?,
                omitted_components: usize::try_from(omitted).map_err(invalid)?,
            });
        }
        if usize::try_from(summary[0]).map_err(invalid)? != joins.len()
            || summary[1]
                != joins
                    .iter()
                    .map(|j| j.omitted_components as i128)
                    .sum::<i128>()
            || bounds.iter().any(|v| *v < 0)
        {
            return Err(Error::Shape);
        }
        Ok(NativeCausalContactPropagationReading {
            field_cut: self.at_cut,
            fractional_bits: self.grain,
            internal: NativeFieldCurrentBall {
                center: waves(&current[..2 * self.births.len()]),
                radius: rat(bounds[1]),
            },
            contact_radius: rat(bounds[0]),
            rounding_radius: rat(summary[1]),
            joins,
        })
    }
}

#[cfg(test)]
mod tests;
#[cfg(test)]
mod live_tests;
