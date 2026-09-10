//! Native operative-map/current staging under the existing field owner.
//! The source field remains borrowed: staging cannot become a second continuing ecology or
//! outlive its original decoder. Publication and the joint constitutive-return producer remain
//! separate obligations; these carriers never mutate the borrowed field.
use super::super::material_transport::wides;
use super::*;
mod response;
mod deposit;
pub use deposit::NativeContactDepositReading;
pub use response::{NativeMaterialResponseChart, NativeMaterialContactResponse, NativeMaterialContactResponseReading, NativeRetainedMaterialRelation, NativeMaterialContactStepComparison, NativeFiniteMaterialResponse};

/// The numerical realization of a NEW contact deposit, not an identification of its source.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(rename_all="kebab-case")]
pub enum NativeContactRealization {
    /// Continue the enclosed unrounded response; its comparison error enters map uncertainty.
    #[default]
    EnclosedFlow,
    /// Install the exact dyadic deposit defined by the retained finite product/projection.
    /// The unrounded-response defect stays in the journal; it is not uncertainty in this new
    /// coefficient. Existing map and internal-current uncertainty is preserved.
    DyadicDeposit,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
pub struct NativeOperativeContactBirth {
    pub source: usize,
    pub receiving: usize,
}
pub(in super::super) mod rest;
mod current_factor;
mod propagation;
mod map_source;
use map_source::{OperativeMapProgram,OperativeSourceOverlap};
use propagation::CausalPropagationSections;
pub use propagation::{NativeCausalContactPropagation,NativeCausalContactPropagationReading,NativeCausalContactJoinReading};
pub use current_factor::NativeOperativeCurrentFactorCondensation;

pub(in super::super) struct OperativeSections<'c> {
    pub(in super::super) map: Rc<ResidentSection<'c>>,
    pub(in super::super) b: Rc<ResidentSection<'c>>,
    pub(in super::super) bounds: Rc<ResidentSection<'c>>,
    pub(in super::super) covariance: ResidentSection<'c>,
    pub(in super::super) aggregate: ResidentSection<'c>,
    pub(in super::super) moment_bounds: ResidentSection<'c>,
}
// Only the native joint-return producer may supply these packed carriers and their complete
// delta radii. There is intentionally no public constructor taking an authored learning delta.
pub(super) struct OperativeReturn<'c> {
    at_cut:usize,contact_count:usize,
    // Zero extension beyond the actual producing contact population.
    factor_count:usize,
    realization: NativeContactRealization,
    origin: Rc<()>,
    ports: Rc<ResidentSection<'c>>,
    currents: Rc<ResidentSection<'c>>,
    // When present, currents stores only ell; k is the addressed source interior difference.
    current_difference_source: Option<usize>,
    source_overlap: Option<OperativeSourceOverlap<'c>>,
    // None is the exact zero generator on contact_count entries, not missing current.
    b: Option<Rc<ResidentSection<'c>>>,
    bounds: Rc<ResidentSection<'c>>,
}
pub struct NativeOperativeContactStaging<'f, 'c> {
    field: &'f NativeConstitutiveField<'c>,
    origin: Rc<()>,
    grain: u32,
    births: Vec<NativeOperativeContactBirth>,
    sections: Rc<OperativeSections<'c>>,
    // Retained return carriers are chronological generators of the new map/current, not
    // rewritten source descriptions. A failed attempt is never appended here.
    returns: Vec<Rc<OperativeReturn<'c>>>,
    program:Option<OperativeMapProgram<'c>>,
}

pub(in super::super) struct OperativeState<'c> {
    // Immutable producing carriers at the two most recent emission cuts. This is a
    // performance cache, not a context window: older producers retain their decoder.
    recent_producers:std::collections::VecDeque<(usize,usize,Rc<OperativeSections<'c>>)>,
    recent_propagations:std::collections::VecDeque<(usize,Rc<CausalPropagationSections<'c>>)>,
    pub(in super::super) propagate_from:Option<usize>,
    pub(in super::super) sections: Rc<OperativeSections<'c>>,
    pub(in super::super) initial: Rc<OperativeSections<'c>>,
    pub(in super::super) activated_at: usize,
    pub(in super::super) grain: u32,
    pub(in super::super) births: Vec<NativeOperativeContactBirth>,
    origin: Rc<()>,
    returns: Vec<Rc<OperativeReturn<'c>>>,
    program:Option<OperativeMapProgram<'c>>,
}
pub(in super::super) struct PendingOperative<'c> {
    origin: Rc<()>,
    pub(in super::super) sections: Rc<OperativeSections<'c>>,
    pub(in super::super) trace: Rc<ResidentSection<'c>>,
    pub(in super::super) table: ResidentSection<'c>,
    pub(in super::super) _scratch: ResidentSection<'c>,
    pub(in super::super) count: usize,
    birth:Option<Rc<ResidentSection<'c>>>,
    pub(in super::super) propagation:Option<Rc<CausalPropagationSections<'c>>>,
    propagation_input_bounds:Option<Rc<ResidentSection<'c>>>,
}
pub(in super::super) struct HeldOperative<'c> {
    pub(in super::super) b: Rc<ResidentSection<'c>>,
    pub(in super::super) bounds: Rc<ResidentSection<'c>>,
    pub(in super::super) trace: Rc<ResidentSection<'c>>,
    pub(in super::super) count: usize,
    pub(in super::super) propagation_input_bounds:Option<Rc<ResidentSection<'c>>>,
}
/// Storage retained by the operative return journal, separate from historical field reports.
/// These carriers are distinct per committed return; temporary handles share the same buffers.
#[derive(Debug,Serialize)]
pub struct NativeOperativeReturnStorage {
    pub returns:usize,
    pub port_octets:u64,
    pub current_factor_octets:u64,
    pub internal_delta_octets:u64,
    pub bound_octets:u64,
    pub implicit_zero_delta_returns:usize,
    pub current_difference_returns:usize,
    pub logical_internal_delta_octets:u64,
    pub logical_current_factor_octets:u64,
    pub total_octets:u64,
    pub source_overlap_octets:u64,
    /// Referenced anchor/birth storage; the anchor can share the current map before its change.
    pub map_source_octets:u64,
}
impl NativeConstitutiveField<'_>{
    pub fn operative_return_storage(&self)->Option<NativeOperativeReturnStorage>{
        let op=self.junction.as_ref()?.operative.as_ref()?;
        let mut out=NativeOperativeReturnStorage{returns:op.returns.len(),port_octets:0,current_factor_octets:0,internal_delta_octets:0,bound_octets:0,implicit_zero_delta_returns:0,current_difference_returns:0,logical_internal_delta_octets:0,logical_current_factor_octets:0,total_octets:0,source_overlap_octets:0,map_source_octets:0};
        for r in &op.returns {out.port_octets+=r.ports.resident_octets();out.current_factor_octets+=r.currents.resident_octets();out.internal_delta_octets+=r.b.as_ref().map_or(0,|b|b.resident_octets());out.bound_octets+=r.bounds.resident_octets();out.implicit_zero_delta_returns+=usize::from(r.b.is_none());out.current_difference_returns+=usize::from(r.current_difference_source.is_some());out.logical_internal_delta_octets+=64*r.contact_count.max(1) as u64;out.logical_current_factor_octets+=128*r.contact_count.max(1) as u64;}
        out.source_overlap_octets=op.returns.iter().filter_map(|r|r.source_overlap.as_ref()).map(|h|h.coefficients.resident_octets()+h.errors.resident_octets()).sum();
        out.map_source_octets=op.program.as_ref().map_or(0,|p|p.map.resident_octets()+p.births.iter().map(|b|b.resident_octets()).sum::<u64>());
        out.total_octets=out.port_octets+out.current_factor_octets+out.internal_delta_octets+out.bound_octets+out.source_overlap_octets;Some(out)
    }
}

impl<'c> OperativeState<'c> {
    pub(in super::super) fn reserve_birth(&mut self) -> Result<(),Error> {
        self.births.try_reserve(1).map_err(|_|Error::Shape)?;
        if let Some(program)=&mut self.program {program.births.try_reserve(1).map_err(|_|Error::Shape)?;}
        Ok(())
    }
    /// The older alternating-prefix current decoder needs unchanged contacts and no separate
    /// propagation. This is not a claim that propagation alone changes the contact matrix.
    pub(in super::super) fn has_legacy_current_decoder(&self) -> bool {
        self.returns.is_empty() && self.propagate_from.is_none()
    }
    pub(in super::super) fn prepare(
        &self,
        surface: &'c ResidentSurface<'c>,
        nodes: usize,
        linked: bool,
    ) -> Result<PendingOperative<'c>, Error> {
        let d = 6 * nodes;
        let m = d / 2;
        // This realization allocates one coordinate per observed source contact. Birth count
        // is not effective rank or evidence of a newly learned reusable generator class.
        let count = self
            .births
            .len()
            .checked_add(usize::from(linked))
            .ok_or(Error::Shape)?;
        if count > u32::MAX as usize {
            return Err(Error::Shape);
        }
        let sections = sections(surface, d, count)?;
        let scratch =
            surface.fresh_section(1, 2 * (m * m + m) + 12 * count.max(1), ResidentGrain(0))?;
        let trace = Rc::new(surface.fresh_section(1, 18 * d + 12, ResidentGrain(0))?);
        let birth=(linked && self.program.is_some()).then(||surface.fresh_section(1,2*d,ResidentGrain(0)).map(Rc::new)).transpose()?;
        let propagation=self.propagate_from.map(|_|CausalPropagationSections::prepare(surface,&self.births)).transpose()?;
        let propagation_input_bounds=propagation.as_ref().map(|_|Rc::clone(&self.sections.bounds));
        let mut words = vec![];
        for ptr in [
            self.sections.map.lo_device_ptr(),
            propagation.as_ref().map_or_else(||self.sections.b.lo_device_ptr(),|p|p.current.lo_device_ptr()),
            propagation.as_ref().map_or_else(||self.sections.bounds.lo_device_ptr(),|p|p.bounds.lo_device_ptr()),
            sections.map.lo_device_ptr(),
            sections.map.hi_device_ptr(),
            sections.b.lo_device_ptr(),
            sections.b.hi_device_ptr(),
            sections.bounds.lo_device_ptr(),
            sections.bounds.hi_device_ptr(),
            sections.covariance.lo_device_ptr(),
            sections.covariance.hi_device_ptr(),
            sections.aggregate.lo_device_ptr(),
            sections.aggregate.hi_device_ptr(),
            sections.moment_bounds.lo_device_ptr(),
            sections.moment_bounds.hi_device_ptr(),
            scratch.lo_device_ptr(),
            trace.lo_device_ptr(),
            trace.hi_device_ptr(),
            self.births.len() as u64,
            count as u64,
            birth.as_ref().map_or(0,|b|b.lo_device_ptr()),
            birth.as_ref().map_or(0,|b|b.hi_device_ptr()),
        ] {
            words.push((ptr as i64, ptr as i64));
        }
        let table = surface.mount_section_rest(
            &ResidentSectionRest::found(1, 22, ResidentGrain(0), 64, words).map_err(invalid)?,
        )?;
        Ok(PendingOperative {
            origin: Rc::new(()),
            sections,
            trace,
            table,
            _scratch: scratch,
            count,
            birth,
            propagation,propagation_input_bounds,
        })
    }
    pub(in super::super) fn receive(
        &mut self,
        next: PendingOperative<'c>,
        source: Option<usize>,
        at: usize,
    ) {
        if let Some(source) = source {
            if let Some(program)=&mut self.program {program.births.push(next.birth.as_ref().expect("prepared birth column").clone());}
            self.births.push(NativeOperativeContactBirth {
                source,
                receiving: at,
            });
        }
        self.recent_producers.push_back((at,next.count,Rc::clone(&next.sections)));
        while self.recent_producers.len()>2 {self.recent_producers.pop_front();}
        if let Some(word)=next.propagation {self.recent_propagations.push_back((at,word));}
        while self.recent_propagations.len()>2 {self.recent_propagations.pop_front();}
        self.sections = next.sections;
        self.origin = next.origin;
    }
}
impl<'c> PendingOperative<'c> {
    pub(in super::super) fn history(&self) -> HeldOperative<'c> {
        HeldOperative {
            b: Rc::clone(&self.sections.b),
            bounds: Rc::clone(&self.sections.bounds),
            trace: Rc::clone(&self.trace),
            count: self.count,
            propagation_input_bounds:self.propagation_input_bounds.clone(),
        }
    }
}
#[derive(Debug, Serialize)]
pub struct NativeOperativeContactReading {
    pub field_cut: usize,
    pub fractional_bits: u32,
    pub births: Vec<NativeOperativeContactBirth>,
    pub contacts: Vec<Vec<ExactComplexWaveCurrent>>,
    pub contacts_radius: Rat,
    pub internal: NativeFieldCurrentBall,
    pub covariance: Vec<Vec<ExactComplexWaveCurrent>>,
    pub covariance_radius: Rat,
    pub aggregate: NativeFieldCurrentBall,
    pub numerical_contact_norm_upper: Rat,
    pub numerical_internal_norm_upper: Rat,
    pub staged_returns: usize,
}
type Error = ConstitutiveFibreError;
fn invalid(s: impl std::fmt::Display) -> Error {
    Error::Rest(format!("operative contacts: {s}"))
}
pub(in super::super) fn sections<'c>(
    surface: &'c ResidentSurface<'c>,
    d: usize,
    k: usize,
) -> Result<Rc<OperativeSections<'c>>, Error> {
    let m = d / 2;
    let sq = m.checked_mul(m).ok_or(Error::Shape)?;
    Ok(Rc::new(OperativeSections {
        map: Rc::new(surface.fresh_section(k.max(1), 2 * d, ResidentGrain(0))?),
        b: Rc::new(surface.fresh_section(k.max(1), 4, ResidentGrain(0))?),
        bounds: Rc::new(surface.fresh_section(1, 4, ResidentGrain(0))?),
        covariance: surface.fresh_section(1, 4 * sq, ResidentGrain(0))?,
        aggregate: surface.fresh_section(1, 2 * d, ResidentGrain(0))?,
        moment_bounds: surface.fresh_section(1, 8, ResidentGrain(0))?,
    }))
}
impl<'c> OperativeSections<'c> {
    pub(in super::super) fn current(&self) -> [&ResidentSection<'c>; 3] {
        [&self.map, &self.b, &self.bounds]
    }
    pub(in super::super) fn moments(&self) -> [&ResidentSection<'c>; 3] {
        [&self.covariance, &self.aggregate, &self.moment_bounds]
    }
}
impl<'c> NativeConstitutiveField<'c> {
    /// Transfer the prepared map/current representation into this same continuing owner.
    /// Existing sources and past reports retain their producing cut.
    pub fn enable_operative_contacts(&mut self) -> Result<(), Error> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(Error::Uncertain);
        }
        if self
            .junction
            .as_ref()
            .is_some_and(|j| j.operative.is_some())
        {
            return Ok(());
        }
        let owned = self.stage_operative_contacts()?.into_owned();
        self.junction.as_mut().ok_or(Error::Shape)?.operative = Some(owned);
        self.junction.as_mut().unwrap().solver = NativeFieldJunctionSolver::Full;
        Ok(())
    }
    pub fn has_operative_contacts(&self) -> bool {
        self.junction
            .as_ref()
            .is_some_and(|j| j.operative.is_some())
    }
    /// Number of committed operative return generators; this is chronology, not a quality score.
    pub fn operative_return_count(&self) -> Option<usize> {
        self.junction.as_ref().and_then(|j|j.operative.as_ref()).map(|o|o.returns.len())
    }
    /// Prepare the existing contact map and full internal-current carrier on the device.
    /// This borrows the one source ecology and issues no source handle or state publication.
    pub fn stage_operative_contacts(
        &mut self,
    ) -> Result<NativeOperativeContactStaging<'_, 'c>, Error> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(Error::Uncertain);
        }
        if let Some(owned) = self.junction.as_ref().and_then(|j| j.operative.as_ref()) {
            return Ok(NativeOperativeContactStaging {
                field: self,
                origin: Rc::clone(&owned.origin),
                grain: owned.grain,
                births: owned.births.clone(),
                sections: Rc::clone(&owned.sections),
                returns: owned.returns.clone(),
                program:owned.program.clone(),
            });
        }
        let grain = match self.junction_representation() {
            Some(NativeFieldJunctionRepresentation::EnclosedDyadic { fractional_bits }) => {
                fractional_bits
            }
            _ => return Err(Error::Shape),
        };
        let n = self.nodes();
        let d = 6 * n;
        let births = self
            .history
            .iter()
            .enumerate()
            .filter_map(|(receiving, h)| {
                h.lineage
                    .observed_source()
                    .map(|source| NativeOperativeContactBirth { source, receiving })
            })
            .collect::<Vec<_>>();
        let k = births.len();
        let mut inputs = Vec::new();
        for birth in &births {
            for at in [birth.source, birth.receiving, birth.receiving - 1] {
                self.mount_history_source(at)?;
            }
        }
        let surface = self.relation.surface;
        let mut pointers = Vec::with_capacity(7 * k.max(1));
        for birth in &births {
            let event = &self.history[birth.receiving];
            inputs.push(if let Some(s) = &event.resident()?.incoming {
                Rc::clone(s)
            } else {
                Rc::new(
                    surface.mount_section_rest(
                        &ResidentSectionRest::found(
                            n,
                            3,
                            ResidentGrain(0),
                            64,
                            event
                                .lineage
                                .incoming
                                .exterior()
                                .ok_or(Error::Uncertain)?
                                .iter()
                                .flat_map(|p| p.words())
                                .map(|v| (v, v))
                                .collect(),
                        )
                        .map_err(invalid)?,
                    )?,
                )
            });
            let old = &self.history[birth.source];
            for value in [
                event.resident()?.section.lo_device_ptr(),
                old.resident()?.section.lo_device_ptr(),
                inputs.last().unwrap().lo_device_ptr(),
                event.frame.native.lo_device_ptr(),
                old.frame.native.lo_device_ptr(),
                self.history[birth.receiving - 1]
                    .resident()?
                    .junction
                    .as_ref()
                    .ok_or(Error::Uncertain)?
                    .lo_device_ptr(),
                birth.receiving as u64,
            ] {
                pointers.push((value as i64, value as i64));
            }
        }
        if pointers.is_empty() {
            pointers.resize(7, (0, 0));
        }
        let table = surface.mount_section_rest(
            &ResidentSectionRest::found(k.max(1), 7, ResidentGrain(0), 64, pointers)
                .map_err(invalid)?,
        )?;
        let staged = sections(surface, d, k)?;
        let scratch = surface.fresh_section(k.max(1), 4 * d + 8, ResidentGrain(0))?;
        let rounds = surface.fresh_section(1, 2 * ((d / 2) * (d / 2) + d / 2), ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![], vec![0]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_operative_mount(
                &lane,
                &table,
                self.junction.as_ref().unwrap().current.as_ref(),
                n,
                k,
                grain,
                self.history.len().saturating_sub(1),
                &staged.map,
                &staged.b,
                &staged.bounds,
                &scratch,
            )?;
        }
        passage.close(0, &staged.bounds, 64)?;
        {
            let lane = passage.open(1, &[0])?;
            surface.record_operative_moments(
                &lane,
                d,
                k,
                grain,
                staged.current(),
                staged.moments(),
                &rounds,
            )?;
        }
        passage.close(1, &staged.moment_bounds, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!("{:?}", receipt.obstruction)));
        }
        Ok(NativeOperativeContactStaging {
            field: self,
            origin: Rc::new(()),
            grain,
            births,
            sections: staged,
            returns: vec![],
            program:None,
        })
    }
}
impl<'f, 'c> NativeOperativeContactStaging<'f, 'c> {
    // Owner-only adoption after a complete native constitutive return. Birth identity and
    // activation standing remain in the existing ecology; only its staged differences move.
    #[cfg(test)]
    fn into_update(self)->(Rc<OperativeSections<'c>>,Rc<()>,Vec<Rc<OperativeReturn<'c>>>,Option<OperativeMapProgram<'c>>) {(self.sections,self.origin,self.returns,self.program)}
    pub(in super::super) fn into_owned(self) -> OperativeState<'c> {
        let activated_at = self.field_cut();
        OperativeState {
            recent_producers:Default::default(),
            recent_propagations:Default::default(),propagate_from:None,
            initial: Rc::clone(&self.sections),
            sections: self.sections,
            activated_at,
            grain: self.grain,
            births: self.births,
            origin: self.origin,
            returns: self.returns,
            program:self.program,
        }
    }
    pub fn field_cut(&self) -> usize {
        self.field.occurrence_count()
    }
    pub fn census(&self) -> TransferCensus {
        self.field.census()
    }
    pub fn births(&self) -> &[NativeOperativeContactBirth] {
        &self.births
    }
    // The field's material-contact producer stages every component;
    // the borrowed source, its old returns and its exact decoder survive refusal unchanged.
    pub(super) fn stage_return(&self, returned: Rc<OperativeReturn<'c>>) -> Result<Self, Error> {
        let currents=self.field.resolve_operative_current_factors(&returned)?;
        self.stage_return_using(returned,&currents)
    }
    pub(super) fn stage_return_using(&self, returned: Rc<OperativeReturn<'c>>,
        currents: &Rc<ResidentSection<'c>>) -> Result<Self, Error> {
        if returned.source_overlap.is_some(){return self.stage_source_return(returned,currents);}
        if !Rc::ptr_eq(&self.origin, &returned.origin) || returned.at_cut!=self.field_cut() || returned.contact_count!=self.births.len() {
            return Err(Error::ForeignOccurrence);
        }
        let surface = self.field.relation.surface;
        let d = 6 * self.field.nodes();
        let k = self.births.len();
        let staged = sections(surface, d, k)?;
        let update_rounds = surface.fresh_section(k.max(1), 2, ResidentGrain(0))?;
        let moments_rounds =
            surface.fresh_section(1, 2 * ((d / 2) * (d / 2) + d / 2), ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![], vec![0]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_operative_update(
                &lane,
                d,
                k,
                self.grain,
                returned.realization == NativeContactRealization::DyadicDeposit,
                self.sections.current(),
                [
                    &returned.ports,
                    currents,
                    &returned.bounds,
                ],
                returned.b.as_deref(),
                returned.factor_count,
                staged.current(),
                &update_rounds,
            )?;
        }
        passage.close(0, &staged.bounds, 64)?;
        {
            let lane = passage.open(1, &[0])?;
            surface.record_operative_moments(
                &lane,
                d,
                k,
                self.grain,
                staged.current(),
                staged.moments(),
                &moments_rounds,
            )?;
        }
        passage.close(1, &staged.moment_bounds, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!("{:?}", receipt.obstruction)));
        }
        let mut returns = self.returns.clone();
        returns.push(returned);
        Ok(Self {
            field: self.field,
            origin: Rc::new(()),
            grain: self.grain,
            births: self.births.clone(),
            sections: staged,
            returns,
            program:self.program.clone(),
        })
    }
    pub fn inspect(&self) -> Result<NativeOperativeContactReading, Error> {
        inspect_sections(
            self.field,
            self.grain,
            &self.births,
            &self.sections,
            self.returns.len(),
        )
    }
}

pub(in super::super) fn inspect_sections(
    field: &NativeConstitutiveField<'_>,
    grain: u32,
    births: &[NativeOperativeContactBirth],
    sections: &OperativeSections<'_>,
    staged_returns: usize,
) -> Result<NativeOperativeContactReading, Error> {
    let surface = field.relation.surface;
    let d = 6 * field.nodes();
    let m = d / 2;
    let k = births.len();
    let read = |s: &ResidentSection<'_>| -> Result<Vec<i128>, Error> {
        wides(&surface.detach_section(s, 64)?.intervals)
    };
    let map = read(&sections.map)?;
    let b = read(&sections.b)?;
    let e = read(&sections.bounds)?;
    let cov = read(&sections.covariance)?;
    let h = read(&sections.aggregate)?;
    let bounds = read(&sections.moment_bounds)?;
    if e.iter().chain(&bounds).any(|v| *v < 0) {
        return Err(invalid("negative enclosure or norm"));
    }
    let scale = num_bigint::BigInt::from(1) << grain;
    let q = |v: i128| Rat::new(v.into(), scale.clone());
    let waves = |v: &[i128]| {
        v.chunks_exact(2)
            .map(|v| ExactComplexWaveCurrent::new(q(v[0]), q(v[1])))
            .collect::<Vec<_>>()
    };
    Ok(NativeOperativeContactReading {
        field_cut: field.occurrence_count(),
        fractional_bits: grain,
        births: births.to_vec(),
        contacts: map[..k * d].chunks_exact(d).map(waves).collect(),
        contacts_radius: q(e[0]),
        internal: NativeFieldCurrentBall {
            center: waves(&b[..2 * k]),
            radius: q(e[1]),
        },
        covariance: cov.chunks_exact(2 * m).map(waves).collect(),
        covariance_radius: q(bounds[0]),
        aggregate: NativeFieldCurrentBall {
            center: waves(&h),
            radius: q(bounds[1]),
        },
        numerical_contact_norm_upper: q(bounds[2]),
        numerical_internal_norm_upper: q(bounds[3]),
        staged_returns: staged_returns,
    })
}

#[cfg(test)]
mod tests;

#[derive(Debug, PartialEq, Eq, Serialize)]
pub struct NativeOperativeReflectionReading {
    pub potential: NativeFieldCurrentBall,
    pub outgoing: NativeFieldCurrentBall,
    pub aggregate: NativeFieldCurrentBall,
    pub internal: NativeFieldCurrentBall,
    /// An auxiliary potential sum, not the decoder for changing contact maps.
    pub potential_prefix: NativeFieldCurrentBall,
    pub source: NativeFieldCurrentBall,
    pub numerical_residual: Vec<ExactComplexWaveCurrent>,
    pub contact_radius: Rat,
    pub joint_current_radius: Rat,
    pub input_norm_upper: Rat,
    pub internal_rounding_upper: Rat,
    pub residual_rounding_upper: Rat,
    pub residual_norm_upper: Rat,
}
pub(in super::super) fn decode_reflection(
    surface: &ResidentSurface<'_>,
    report: &ResidentSection<'_>,
    op: &HeldOperative<'_>,
    nodes: usize,
    grain: u32,
) -> Result<NativeOperativeReflectionReading, Error> {
    let d = 6 * nodes;
    let base =
        super::enclosure::decode_report(&surface.detach_section(report, 64)?.intervals, d, grain)?;
    let b = wides(&surface.detach_section(&op.b, 64)?.intervals)?;
    let bounds = wides(&surface.detach_section(&op.bounds, 64)?.intervals)?;
    let trace = surface.detach_section(&op.trace, 64)?;
    if trace.width != 18 * d + 12 || trace.intervals.iter().any(|(a, b)| a != b) {
        return Err(invalid("reflection trace shape"));
    }
    let scalar = wides(&trace.intervals[18 * d..])?;
    if scalar.iter().chain(&bounds).any(|v| *v < 0) {
        return Err(invalid("reflection radius or norm"));
    }
    let scale = num_bigint::BigInt::from(1) << grain;
    let cube = num_bigint::BigInt::from(1) << (3 * grain);
    let q = |x: i128| Rat::new(x.into(), scale.clone());
    let integer = |row: usize| -> Result<num_bigint::BigInt, Error> {
        let w = &trace.intervals[18 * row..18 * (row + 1)];
        if ![0, 1].contains(&w[17].0) || w[..17].iter().any(|(a, _)| *a < 0 || *a > u32::MAX as i64)
        {
            return Err(invalid("reflection residual codeword"));
        }
        let mut v = num_bigint::BigInt::from(0);
        for (i, (word, _)) in w[..17].iter().enumerate() {
            v += num_bigint::BigInt::from(*word) << (32 * i);
        }
        if w[17].0 == 1 {
            v = -v;
        }
        Ok(v)
    };
    let numerical_residual = (0..d / 2)
        .map(|j| {
            Ok(ExactComplexWaveCurrent::new(
                Rat::new(integer(2 * j)?, cube.clone()),
                Rat::new(integer(2 * j + 1)?, cube.clone()),
            ))
        })
        .collect::<Result<Vec<_>, Error>>()?;
    Ok(NativeOperativeReflectionReading {
        potential: base.potential,
        outgoing: base.outgoing,
        aggregate: base.held_current,
        internal: NativeFieldCurrentBall {
            center: b[..2 * op.count]
                .chunks_exact(2)
                .map(|v| ExactComplexWaveCurrent::new(q(v[0]), q(v[1])))
                .collect(),
            radius: q(bounds[1]),
        },
        potential_prefix: base.potential_prefix,
        source: NativeFieldCurrentBall {
            center: base.source_center,
            radius: q(scalar[0]),
        },
        numerical_residual,
        contact_radius: q(bounds[0]),
        joint_current_radius: q(scalar[5]),
        input_norm_upper: q(scalar[1]),
        internal_rounding_upper: q(scalar[2]),
        residual_rounding_upper: q(scalar[3]),
        residual_norm_upper: q(scalar[4]),
    })
}
impl NativeConstitutiveField<'_> {
    pub fn inspect_operative_contacts(
        &self,
    ) -> Result<Option<NativeOperativeContactReading>, Error> {
        self.junction
            .as_ref()
            .and_then(|j| j.operative.as_ref())
            .map(|o| inspect_sections(self, o.grain, &o.births, &o.sections, o.returns.len()))
            .transpose()
    }
    pub fn inspect_operative_reflection(
        &self,
        at: usize,
    ) -> Result<Option<NativeOperativeReflectionReading>, Error> {
        self.history
            .get(at)
            .ok_or(Error::ForeignOccurrence)?
            .with_resident(self.relation.surface, |event| {
                event
                    .operative
                    .as_ref()
                    .map(|o| {
                        decode_reflection(
                            self.relation.surface,
                            event.junction.as_ref().ok_or(Error::Uncertain)?,
                            o,
                            self.nodes(),
                            self.transport_grain()?,
                        )
                    })
                    .transpose()
            })
    }
}
