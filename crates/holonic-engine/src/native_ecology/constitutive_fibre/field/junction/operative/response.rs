//! The material covector returns through its actual paired producer. Contact response has
//! the declared unit Frobenius metric; source/internal input reactions remain explicit.
use super::*;
use num_bigint::BigInt;
use num_traits::One;

pub struct NativeMaterialContactResponse<'c> {
    surface: &'c ResidentSurface<'c>,
    query: NativeMaterialSourcePullback<'c>,
    origin: Rc<()>,
    at_cut: usize,
    _producing: Rc<OperativeSections<'c>>,
    _forward: Rc<ResidentSection<'c>>,
    ports: Rc<ResidentSection<'c>>,
    currents: Rc<ResidentSection<'c>>,
    delta_b: Rc<ResidentSection<'c>>,
    delta_bounds: Rc<ResidentSection<'c>>,
    diagnostics: ResidentSection<'c>,
}

#[derive(Debug, Serialize)]
pub struct NativeMaterialContactResponseReading {
    pub query: NativeMaterialSourcePullbackReading,
    pub application_cut: usize,
    pub contact_covector: PairedContactCotangent,
    pub contact_covector_radius: Rat,
    pub incoming_source: NativeFieldCurrentBall,
    /// The reaction includes a newborn's zero-input constraint; it is not a free birth value.
    pub incoming_internal: NativeFieldCurrentBall,
    pub potential_covector_radius: Rat,
    pub contact_factor_radii: [Rat; 2],
    pub solve_residual: NativeFieldCurrentBall,
}
impl NativeMaterialContactResponse<'_> {
    pub fn inspect(&self) -> Result<NativeMaterialContactResponseReading, Error> {
        let read = |s: &ResidentSection<'_>| wides(&self.surface.detach_section(s, 64)?.intervals);
        let ports = read(&self.ports)?;
        let currents = read(&self.currents)?;
        let out = read(&self.diagnostics)?;
        let query = self.query.inspect()?;
        let k = self.query.contacts;
        let d = query.outgoing_current.len();
        let scale = BigInt::one() << self.query.grain;
        let rat = |v: i128| Rat::new(v.into(), scale.clone());
        let vector = |v: &[i128]| {
            v.chunks_exact(2)
                .map(|a| ExactComplexWaveCurrent::new(rat(a[0]), rat(a[1])))
                .collect::<Vec<_>>()
        };
        let e = &out[2 * d + 4 * k..];
        Ok(NativeMaterialContactResponseReading {
            query,
            application_cut: self.at_cut,
            contact_covector: PairedContactCotangent {
                port_factors: [vector(&ports[..d]), vector(&ports[d..])],
                contact_factors: [vector(&currents[..2 * k]), vector(&currents[2 * k..4 * k])],
            },
            contact_covector_radius: rat(e[5]),
            incoming_source: NativeFieldCurrentBall {
                center: vector(&out[..d]),
                radius: rat(e[1]),
            },
            incoming_internal: NativeFieldCurrentBall {
                center: vector(&out[d..d + 2 * k]),
                radius: rat(e[2]),
            },
            potential_covector_radius: rat(e[0]),
            contact_factor_radii: [rat(e[3]), rat(e[4])],
            // The full norm bound also bounds conversion error conservatively. Preserve the
            // oriented representative separately; a scalar norm does not replace it.
            solve_residual: NativeFieldCurrentBall {
                center: vector(&out[d + 2 * k..2 * d + 4 * k]),
                radius: rat(e[6]),
            },
        })
    }
}

impl<'c> NativeConstitutiveField<'c> {
    /// Publish the constrained unit-Frobenius contact response atomically. Its constitutive
    /// functional is 1/2 ||delta D||² - Re<G_D,delta D>, with input currents fixed. Thus
    /// delta D=G_D; this is not a claim of global descent of the nonlinear material loss.
    /// Recompute D'D'* and D'b, including every finite mixed term, before publication.
    pub fn apply_material_contact_response(
        &mut self,
        response: &NativeMaterialContactResponse<'c>,
    ) -> Result<(), Error> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(Error::Uncertain);
        }
        if !Rc::ptr_eq(&response.query._owner, &self.owner)
            || response.at_cut != self.history.len()
            || response.query.receiving.occurrence.checked_add(1) != Some(self.history.len())
        {
            return Err(Error::ForeignOccurrence);
        }
        let op = self
            .junction
            .as_ref()
            .and_then(|j| j.operative.as_ref())
            .ok_or(Error::Shape)?;
        if !Rc::ptr_eq(&response.origin, &op.origin)
            || op
                .returns
                .last()
                .is_some_and(|r| r.at_cut == self.history.len())
        {
            return Err(Error::ForeignOccurrence);
        }
        let k = op.births.len();
        let surface = self.relation.surface;
        let (currents, db) = if k == response.query.contacts {
            (response.currents.clone(), response.delta_b.clone())
        } else {
            let currents = Rc::new(surface.fresh_section(2, 4 * k.max(1), ResidentGrain(0))?);
            let db = Rc::new(surface.fresh_section(k.max(1), 4, ResidentGrain(0))?);
            let mut passage = surface.begin_passage(&[vec![]])?;
            {
                let lane = passage.open(0, &[])?;
                surface.record_operative_extend_response(
                    &lane,
                    &response.currents,
                    response.query.contacts,
                    k,
                    &currents,
                    &db,
                )?;
            }
            passage.close(0, &currents, 64)?;
            let r = passage.finish()?.launch()?;
            if !r.obstruction.is_empty() {
                return Err(Error::Arithmetic(format!(
                    "contact response extension: {:?}",
                    r.obstruction
                )));
            }
            (currents, db)
        };
        let returned = Rc::new(OperativeReturn {
            at_cut: self.history.len(),
            contact_count: k,
            origin: op.origin.clone(),
            ports: response.ports.clone(),
            currents,
            b: db,
            bounds: response.delta_bounds.clone(),
        });
        let (sections, origin, returns) = {
            let view = self.stage_operative_contacts()?;
            let staged = view.stage_return(returned)?;
            (staged.sections, staged.origin, staged.returns)
        };
        let op = self.junction.as_mut().unwrap().operative.as_mut().unwrap();
        op.sections = sections;
        op.origin = origin;
        op.returns = returns;
        Ok(())
    }

    pub fn material_contact_response(
        &self,
        query: NativeMaterialSourcePullback<'c>,
    ) -> Result<NativeMaterialContactResponse<'c>, Error> {
        if !Rc::ptr_eq(&query._owner, &self.owner) {
            return Err(Error::ForeignOccurrence);
        }
        let op = self
            .junction
            .as_ref()
            .and_then(|j| j.operative.as_ref())
            .ok_or(Error::Shape)?;
        let source = query.source.occurrence;
        let k = query.contacts;
        let n = self.nodes();
        let d = 6 * n;
        let surface = self.relation.surface;
        let (forward, b, bounds, count) = self
            .history
            .get(source)
            .ok_or(Error::ForeignOccurrence)?
            .with_resident(surface, |r| {
                let p = r.operative.as_ref().ok_or(Error::Uncertain)?;
                Ok((
                    r.junction.as_ref().ok_or(Error::Uncertain)?.clone(),
                    p.b.clone(),
                    p.bounds.clone(),
                    p.count,
                ))
            })?;
        if count != k || k > op.births.len() || query.grain != op.grain {
            return Err(Error::Shape);
        }
        let later = op
            .returns
            .iter()
            .filter(|r| r.at_cut >= source + 1)
            .collect::<Vec<_>>();
        let mut pointers = Vec::with_capacity(3 * later.len().max(1));
        for r in &later {
            for v in [
                r.ports.lo_device_ptr(),
                r.currents.lo_device_ptr(),
                r.contact_count as u64,
            ] {
                pointers.push((v as i64, v as i64));
            }
        }
        if pointers.is_empty() {
            pointers.resize(3, (0, 0));
        }
        let journal = surface.mount_section_rest(
            &ResidentSectionRest::found(later.len().max(1), 3, ResidentGrain(0), 64, pointers)
                .map_err(invalid)?,
        )?;
        let mut producing = sections(surface, d, k)?;
        let p = Rc::get_mut(&mut producing).unwrap();
        p.b = b;
        p.bounds = bounds;
        let moment_rounds =
            surface.fresh_section(1, 2 * ((d / 2) * (d / 2) + d / 2), ResidentGrain(0))?;
        let ports = Rc::new(surface.fresh_section(2, 2 * d, ResidentGrain(0))?);
        let currents = Rc::new(surface.fresh_section(2, 4 * k.max(1), ResidentGrain(0))?);
        let delta_b = Rc::new(surface.fresh_section(k.max(1), 4, ResidentGrain(0))?);
        let delta_bounds = Rc::new(surface.fresh_section(1, 4, ResidentGrain(0))?);
        let diagnostics = surface.fresh_section(1, 2 * (2 * d + 4 * k + 8), ResidentGrain(0))?;
        let workspace =
            surface.fresh_section(1, 2 * (d * d + 3 * d + 4 * k + 2), ResidentGrain(0))?;
        let dots = surface.fresh_section(k.max(1), 10, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![], vec![0], vec![1]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_operative_producing_map(
                &lane,
                &op.sections.map,
                &journal,
                later.len(),
                d,
                k,
                query.grain,
                &producing.map,
            )?;
        }
        passage.close(0, &producing.map, 64)?;
        {
            let lane = passage.open(1, &[0])?;
            surface.record_operative_moments(
                &lane,
                d,
                k,
                query.grain,
                producing.current(),
                producing.moments(),
                &moment_rounds,
            )?;
        }
        passage.close(1, &producing.moment_bounds, 64)?;
        {
            let lane = passage.open(2, &[1])?;
            surface.record_operative_material_adjoint(
                &lane,
                [
                    &producing.map,
                    &producing.b,
                    &producing.bounds,
                    &producing.covariance,
                    &producing.moment_bounds,
                    &forward,
                    &query.output,
                ],
                n,
                k,
                query.grain,
                [&ports, &currents, &delta_b, &delta_bounds, &diagnostics],
                &workspace,
                &dots,
            )?;
        }
        passage.close(2, &diagnostics, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "paired material adjoint: {:?}",
                receipt.obstruction
            )));
        }
        Ok(NativeMaterialContactResponse {
            surface,
            query,
            origin: op.origin.clone(),
            at_cut: self.history.len(),
            _producing: producing,
            _forward: forward,
            ports,
            currents,
            delta_b,
            delta_bounds,
            diagnostics,
        })
    }
}

#[cfg(test)]
mod tests;
