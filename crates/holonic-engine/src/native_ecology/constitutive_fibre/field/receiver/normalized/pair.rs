//! A geometric pair receiver on resident chart coordinates, with a separately typed value
//! current. s=-beta*Q/2, y=sum softmax(s)_i v_i. The geometric charts' producing operands
//! survive the complete reverse return. The caller composes their chart and pair-jet adjoints;
//! no spatial/current or inverse/adjoint identification is implicit here.
use super::*;
use crate::resident_section::{Dyadic, SLOT_WORDS};

pub struct NativePairParticipation<'c> {
    query: Rc<ResidentNormalEnclosureSection<'c>>,
    neighbors: Rc<ResidentNormalEnclosureSection<'c>>,
    values: Rc<ResidentNormalEnclosureSection<'c>>,
    logits: ResidentNormalEnclosureSection<'c>,
    normalized: NativeNormalizedSection<'c>,
    output: ResidentNormalEnclosureSection<'c>,
    count: usize,
    beta: Dyadic,
}

/// Covectors in each producing chart. A shared query/value source joins these after its own
/// chart transpose, not by equating their coordinates or discarding one variation term.
pub struct NativePairParticipationAdjoint<'c> {
    query: ResidentNormalEnclosureSection<'c>,
    neighbors: ResidentNormalEnclosureSection<'c>,
    values: ResidentNormalEnclosureSection<'c>,
}

impl<'c> ResidentNormalEnclosureSection<'c> {
    pub fn pair_quadrance_participation(
        self: Rc<Self>,
        neighbors: Rc<Self>,
        values: Rc<Self>,
        neighbors_per_row: usize,
        beta: Dyadic,
        terms: SeriesAperture,
    ) -> Result<NativePairParticipation<'c>, ConstitutiveFibreError> {
        let rows = self.rows();
        let n = neighbors_per_row;
        let surface = self.resident_section().surface();
        let grain = self.grain();
        let population = rows.checked_mul(n).ok_or(ConstitutiveFibreError::Shape)?;
        let potentials = n.checked_mul(2).ok_or(ConstitutiveFibreError::Shape)?;
        let dimensions = self.components();
        let components = values.components();
        if rows == 0
            || rows > u32::MAX as usize
            || n == 0
            || n > u32::MAX as usize / 4
            || population > u32::MAX as usize
            || dimensions == 0
            || dimensions % 2 != 0
            || dimensions > u32::MAX as usize / 4
            || components == 0
            || components % 2 != 0
            || components > u32::MAX as usize / 4
            || !(1..=120).contains(&grain.0)
            || terms.0 == 0
            || terms.0 == u32::MAX
            || beta.significand < 0
            || beta.exponent == i32::MIN
            || neighbors.rows() != population
            || neighbors.components() != dimensions
            || values.rows() != population
            || [&*neighbors, &*values].iter().any(|v| {
                v.grain() != grain || !std::ptr::eq(v.resident_section().surface(), surface)
            })
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let logits = surface.fresh_section(rows, (potentials + 1) * 2, ResidentGrain(0))?;
        let flags = surface.fresh_section(rows, SLOT_WORDS / 2, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_pair_logits(
                &lane,
                self.resident_section(),
                neighbors.resident_section(),
                rows,
                n,
                dimensions,
                grain.0,
                beta,
                &logits,
                &flags,
            )?;
            surface.collect_phase_status(&lane, &flags, rows)?;
        }
        passage.close(0, &logits, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "pair logits: {:?}",
                receipt.obstruction
            )));
        }
        let logits = Self::from_resident(surface, logits, rows, potentials, grain)?;
        let normalized = logits.normalized_participation(
            n,
            terms,
            NativeNormalizedFaceMeasure::ExponentialPotential,
        )?;
        let output = surface.fresh_section(rows, (components + 1) * 2, ResidentGrain(0))?;
        let flags = surface.fresh_section(rows, SLOT_WORDS / 2, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_phase_weighted(
                &lane,
                values.resident_section(),
                normalized.participation().resident_section(),
                rows,
                n,
                components,
                grain.0,
                &output,
                &flags,
            )?;
            surface.collect_phase_status(&lane, &flags, rows)?;
        }
        passage.close(0, &output, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "pair current: {:?}",
                receipt.obstruction
            )));
        }
        Ok(NativePairParticipation {
            query: self,
            neighbors,
            values,
            logits,
            normalized,
            output: Self::from_resident(surface, output, rows, components, grain)?,
            count: n,
            beta,
        })
    }
}

impl<'c> NativePairParticipation<'c> {
    pub fn values(&self) -> &ResidentNormalEnclosureSection<'c> {
        &self.values
    }
    pub fn output(&self) -> &ResidentNormalEnclosureSection<'c> {
        &self.output
    }
    pub fn logits(&self) -> &ResidentNormalEnclosureSection<'c> {
        &self.logits
    }
    pub fn participation(&self) -> &ResidentNormalEnclosureSection<'c> {
        self.normalized.participation()
    }
    pub fn pull_back(
        &self,
        gy: &ResidentNormalEnclosureSection<'c>,
        gp: Option<&ResidentNormalEnclosureSection<'c>>,
    ) -> Result<NativePairParticipationAdjoint<'c>, ConstitutiveFibreError> {
        let surface = self.query.resident_section().surface();
        let rows = self.query.rows();
        let n = self.count;
        let dimensions = self.query.components();
        let components = self.values.components();
        let grain = self.query.grain();
        let correct = |v: &ResidentNormalEnclosureSection<'c>, d| {
            v.rows() == rows
                && v.components() == d
                && v.grain() == grain
                && std::ptr::eq(v.resident_section().surface(), surface)
        };
        if !correct(gy, components) || gp.is_some_and(|v| !correct(v, 2 * n)) {
            return Err(ConstitutiveFibreError::Shape);
        }
        let terms = surface.fresh_section(rows, (2 * n + 1) * 2, ResidentGrain(0))?;
        let flags = surface.fresh_section(rows, SLOT_WORDS / 2, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_phase_terms(
                &lane,
                self.values.resident_section(),
                gy.resident_section(),
                gp.map(|v| v.resident_section()),
                rows,
                n,
                components,
                grain.0,
                &terms,
                &flags,
            )?;
            surface.collect_phase_status(&lane, &flags, rows)?;
        }
        passage.close(0, &terms, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "pair terms: {:?}",
                receipt.obstruction
            )));
        }
        let terms =
            ResidentNormalEnclosureSection::from_resident(surface, terms, rows, 2 * n, grain)?;
        let normalized_return = self.normalized.pull_back(&terms)?;
        let dq = surface.fresh_section(rows, (dimensions + 1) * 2, ResidentGrain(0))?;
        let du = surface.fresh_section(rows * n, (dimensions + 1) * 2, ResidentGrain(0))?;
        let dv = surface.fresh_section(rows * n, (components + 1) * 2, ResidentGrain(0))?;
        let flags = surface.fresh_section(rows, SLOT_WORDS / 2, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_pair_adjoint(
                &lane,
                self.query.resident_section(),
                self.neighbors.resident_section(),
                self.normalized.participation().resident_section(),
                normalized_return.potentials().resident_section(),
                gy.resident_section(),
                rows,
                n,
                dimensions,
                components,
                grain.0,
                self.beta,
                &dq,
                &du,
                &dv,
                &flags,
            )?;
            surface.collect_phase_status(&lane, &flags, rows)?;
        }
        passage.close(0, &dq, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "pair adjoint: {:?}",
                receipt.obstruction
            )));
        }
        Ok(NativePairParticipationAdjoint {
            query: ResidentNormalEnclosureSection::from_resident(
                surface, dq, rows, dimensions, grain,
            )?,
            neighbors: ResidentNormalEnclosureSection::from_resident(
                surface,
                du,
                rows * n,
                dimensions,
                grain,
            )?,
            values: ResidentNormalEnclosureSection::from_resident(
                surface,
                dv,
                rows * n,
                components,
                grain,
            )?,
        })
    }
}
impl<'c> NativePairParticipationAdjoint<'c> {
    pub fn into_parts(
        self,
    ) -> (
        ResidentNormalEnclosureSection<'c>,
        ResidentNormalEnclosureSection<'c>,
        ResidentNormalEnclosureSection<'c>,
    ) {
        (self.query, self.neighbors, self.values)
    }
    pub fn query(&self) -> &ResidentNormalEnclosureSection<'c> {
        &self.query
    }
    pub fn neighbors(&self) -> &ResidentNormalEnclosureSection<'c> {
        &self.neighbors
    }
    pub fn values(&self) -> &ResidentNormalEnclosureSection<'c> {
        &self.values
    }
}

#[cfg(test)]
mod tests;
