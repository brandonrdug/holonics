//! Native operative-map/current staging under the existing field owner.
//! The source field remains borrowed: staging cannot become a second continuing ecology or
//! outlive its original decoder. Publication and the joint constitutive-return producer remain
//! separate obligations; these carriers never mutate the borrowed field.
use super::super::material_transport::wides;
use super::*;

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NativeOperativeContactBirth {
    pub source: usize,
    pub receiving: usize,
}

pub(super) struct OperativeSections<'c> {
    map: ResidentSection<'c>,
    b: ResidentSection<'c>,
    bounds: ResidentSection<'c>,
    covariance: ResidentSection<'c>,
    aggregate: ResidentSection<'c>,
    moment_bounds: ResidentSection<'c>,
}
// Only the native joint-return producer may supply these packed carriers and their complete
// delta radii. There is intentionally no public constructor taking an authored learning delta.
pub(super) struct OperativeReturn<'c> {
    origin: Rc<()>,
    ports: ResidentSection<'c>,
    currents: ResidentSection<'c>,
    b: ResidentSection<'c>,
    bounds: ResidentSection<'c>,
}
pub struct NativeOperativeContactStaging<'f, 'c> {
    field: &'f NativeConstitutiveField<'c>,
    origin: Rc<()>,
    grain: u32,
    births: Vec<NativeOperativeContactBirth>,
    sections: OperativeSections<'c>,
    // Retained return carriers are chronological generators of the new map/current, not
    // rewritten source descriptions. A failed attempt is never appended here.
    returns: Vec<Rc<OperativeReturn<'c>>>,
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
fn sections<'c>(
    surface: &'c ResidentSurface<'c>,
    d: usize,
    k: usize,
) -> Result<OperativeSections<'c>, Error> {
    let m = d / 2;
    let sq = m.checked_mul(m).ok_or(Error::Shape)?;
    Ok(OperativeSections {
        map: surface.fresh_section(k.max(1), 2 * d, ResidentGrain(0))?,
        b: surface.fresh_section(k.max(1), 4, ResidentGrain(0))?,
        bounds: surface.fresh_section(1, 4, ResidentGrain(0))?,
        covariance: surface.fresh_section(1, 4 * sq, ResidentGrain(0))?,
        aggregate: surface.fresh_section(1, 2 * d, ResidentGrain(0))?,
        moment_bounds: surface.fresh_section(1, 8, ResidentGrain(0))?,
    })
}
impl<'c> OperativeSections<'c> {
    fn current(&self) -> [&ResidentSection<'c>; 3] {
        [&self.map, &self.b, &self.bounds]
    }
    fn moments(&self) -> [&ResidentSection<'c>; 3] {
        [&self.covariance, &self.aggregate, &self.moment_bounds]
    }
}
impl<'c> NativeConstitutiveField<'c> {
    /// Prepare the existing contact map and full internal-current carrier on the device.
    /// This borrows the one source ecology and issues no source handle or state publication.
    pub fn stage_operative_contacts(
        &mut self,
    ) -> Result<NativeOperativeContactStaging<'_, 'c>, Error> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(Error::Uncertain);
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
                    .received_from
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
        })
    }
}
impl<'f, 'c> NativeOperativeContactStaging<'f, 'c> {
    pub fn field_cut(&self) -> usize {
        self.field.occurrence_count()
    }
    pub fn census(&self) -> TransferCensus { self.field.census() }
    pub fn births(&self) -> &[NativeOperativeContactBirth] {
        &self.births
    }
    // Not yet called by the field's joint constitutive producer. It stages every component;
    // the borrowed source, its old returns and its exact decoder survive refusal unchanged.
    #[allow(dead_code)]
    pub(super) fn stage_return(&self, returned: Rc<OperativeReturn<'c>>) -> Result<Self, Error> {
        if !Rc::ptr_eq(&self.origin, &returned.origin) {
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
                self.sections.current(),
                [
                    &returned.ports,
                    &returned.currents,
                    &returned.b,
                    &returned.bounds,
                ],
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
        })
    }
    pub fn inspect(&self) -> Result<NativeOperativeContactReading, Error> {
        let surface = self.field.relation.surface;
        let d = 6 * self.field.nodes();
        let m = d / 2;
        let k = self.births.len();
        let read = |s: &ResidentSection<'c>| -> Result<Vec<i128>, Error> {
            wides(&surface.detach_section(s, 64)?.intervals)
        };
        let map = read(&self.sections.map)?;
        let b = read(&self.sections.b)?;
        let e = read(&self.sections.bounds)?;
        let cov = read(&self.sections.covariance)?;
        let h = read(&self.sections.aggregate)?;
        let bounds = read(&self.sections.moment_bounds)?;
        if e.iter().chain(&bounds).any(|v| *v < 0) {
            return Err(invalid("negative enclosure or norm"));
        }
        let scale = num_bigint::BigInt::from(1) << self.grain;
        let q = |v: i128| Rat::new(v.into(), scale.clone());
        let waves = |v: &[i128]| {
            v.chunks_exact(2)
                .map(|v| ExactComplexWaveCurrent::new(q(v[0]), q(v[1])))
                .collect::<Vec<_>>()
        };
        Ok(NativeOperativeContactReading {
            field_cut: self.field_cut(),
            fractional_bits: self.grain,
            births: self.births.clone(),
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
            staged_returns: self.returns.len(),
        })
    }
}

#[cfg(test)]
mod tests;
