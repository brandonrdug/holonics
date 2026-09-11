//! The existing accumulated normal response with direct resident-current operands.
//! The current three-port source chart is explicit. No occurrence archive or field handle is
//! needed to develop or query this local material; exact moments own its continuing geometry.
use super::*;
use std::rc::Rc;
mod rest;
pub use rest::NormalMaterialRest;
mod refine;
pub use refine::NormalRealizationRefinement;

mod enclosure;
pub use enclosure::{ResidentNormalEnclosure, ResidentNormalEnclosureView, ResidentNormalInput};
mod section;
pub use section::ResidentNormalSectionReturn;
mod wave;
pub use wave::{ResidentNormalWave, NormalWaveCurrent, NormalWaveFibre, NormalWaveStep, NormalWaveReading, NormalWaveRest, NormalWaveSeedRefusal, NormalWaveSeedKind, NormalWaveReception, NormalWaveReceptionReading, NormalWaveDevelopment, NormalSourceActuation, NormalProducingHandle, NormalWavePrediction, NormalWaveComparison, NormalWaveComparisonReading, NormalWaveTransport, NormalWaveTransportChange, NormalWaveReference, NormalWaveReferenceReading, NormalWaveBasisChart, NormalWaveBasisFace, NormalWaveBasisReading, NormalBasisSelection, NormalBasisScore, NormalWaveSource, NormalWaveJointSource, NormalWaveFamily, NormalWaveFamilyRest, NormalFamilySupport, NormalFamilyReceiverReading, NormalWaveFamilyReceiver};

pub struct ResidentNormalMaterial<'c> {
    surface: &'c ResidentSurface<'c>,
    state: Rc<ResidentSection<'c>>,
    roots: usize,
    targets: usize,
    grain: ResidentGrain,
    observations: u64,
}

/// A receiver result with its actual borrowed operands. Forward/return currents are complete
/// balls; there is no method that turns their numerical centres into point-current inputs.
pub struct ResidentNormalReturn<'a, 'c> {
    surface: &'c ResidentSurface<'c>,
    before: ResidentSection<'c>,
    after: Option<ResidentSection<'c>>,
    source: ResidentNormalInput<'a, 'c>,
    observed: Option<ResidentConstitutiveCurrent<'a, 'c>>,
    roots: usize,
    targets: usize,
    grain: ResidentGrain,
    pub predecessor_observations: u64,
    pub successor_observations: u64,
}
impl<'a, 'c> ResidentNormalReturn<'a, 'c> {
    pub fn source(&self) -> ResidentNormalInput<'_, 'c> {
        self.source
    }
    pub fn observed(&self) -> Option<ResidentConstitutiveCurrent<'_, 'c>> {
        self.observed
    }
    pub fn inspect_before(&self) -> Result<NativeNormalMaterialReading, ConstitutiveFibreError> {
        let rest = self.surface.detach_section(&self.before, i64::BITS)?;
        decode_report(&rest, self.roots, self.targets, self.grain.0, false)
    }
    pub fn inspect_after(
        &self,
    ) -> Result<Option<NativeNormalMaterialReading>, ConstitutiveFibreError> {
        self.after
            .as_ref()
            .map(|section| {
                let rest = self.surface.detach_section(section, i64::BITS)?;
                decode_report(&rest, self.roots, self.targets, self.grain.0, true)
            })
            .transpose()
    }
}
impl<'c> ResidentNormalMaterial<'c> {
    /// Found the existing unit-prior normal law. `roots` declares three equal complex port
    /// blocks (outgoing, held, target/reference), and targets declares the output chart.
    /// Grain is the caller's numerical realization; it is not a semantic capacity.
    pub fn found(
        surface: &'c ResidentSurface<'c>,
        roots: usize,
        targets: usize,
        grain: ResidentGrain,
    ) -> Result<Self, ConstitutiveFibreError> {
        if roots == 0 || targets == 0 || !(1..=120).contains(&grain.0) {
            return Err(ConstitutiveFibreError::Shape);
        }
        let values = initial_words(roots, targets, grain.0)?;
        let state = surface.mount_section_rest(
            &ResidentSectionRest::found(1, values.len(), ResidentGrain(0), i64::BITS, values)
                .map_err(invalid)?,
        )?;
        Ok(Self {
            surface,
            state: Rc::new(state),
            roots,
            targets,
            grain,
            observations: 0,
        })
    }
    pub fn observations(&self) -> u64 {
        self.observations
    }
    pub fn inspect(&self) -> Result<NativeNormalMaterialState, ConstitutiveFibreError> {
        decode_state(
            &self.surface.detach_section(&self.state, i64::BITS)?,
            self.roots,
            self.targets,
            self.grain.0,
        )
    }
    /// Durable boundary data for this owner, containing accumulated geometry and numerical
    /// witness only. Source observations are not present. A rest decoder is a separate port.
    pub fn state_wire(&self) -> Result<ResidentSectionRest, ConstitutiveFibreError> {
        Ok(self.surface.detach_section(&self.state, i64::BITS)?)
    }
    pub fn read<'a>(
        &self,
        source: impl Into<ResidentNormalInput<'a, 'c>>,
    ) -> Result<ResidentNormalReturn<'a, 'c>, ConstitutiveFibreError> {
        Ok(self.prepare(source.into(), None)?.0)
    }
    pub fn receive<'a>(
        &mut self,
        source: impl Into<ResidentNormalInput<'a, 'c>>,
        observed: ResidentConstitutiveCurrent<'a, 'c>,
    ) -> Result<ResidentNormalReturn<'a, 'c>, ConstitutiveFibreError> {
        let (returned, next) = self.prepare(source.into(), Some(observed))?;
        self.state = Rc::new(next.ok_or(ConstitutiveFibreError::Shape)?);
        self.observations = returned.successor_observations;
        Ok(returned)
    }
    fn prepare<'a>(
        &self,
        source: ResidentNormalInput<'a, 'c>,
        observed: Option<ResidentConstitutiveCurrent<'a, 'c>>,
    ) -> Result<(ResidentNormalReturn<'a, 'c>, Option<ResidentSection<'c>>), ConstitutiveFibreError>
    {
        let layout =
            NormalLayout::new(self.roots, self.targets).ok_or(ConstitutiveFibreError::Shape)?;
        if source.width() != layout.source_components
            || observed.is_some_and(|y| y.width != layout.target_components)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let next_count = self
            .observations
            .checked_add(u64::from(observed.is_some()))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let fresh = |width| self.surface.fresh_section(1, width, ResidentGrain(0));
        let before = fresh(layout.report_words)?;
        let after = observed.map(|_| fresh(layout.report_words)).transpose()?;
        let next = observed.map(|_| fresh(layout.state_words)).transpose()?;
        let work = fresh(layout.workspace_words)?;
        // Two complex-source ball slots in the old junction chart, followed by rational pairs.
        let input_words = layout
            .source_components
            .checked_add(1)
            .and_then(|n| n.checked_mul(4))
            .and_then(|n| self.targets.checked_mul(3).and_then(|t| n.checked_add(t)))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let input = fresh(input_words)?;
        let mut passage = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.surface.record_direct_normal_material(
                &lane,
                &self.state,
                source,
                observed,
                self.roots,
                self.targets,
                self.grain.0,
                next.as_ref(),
                &before,
                after.as_ref(),
                &work,
                &input,
            )?;
        }
        passage.close(0, after.as_ref().unwrap_or(&before), i64::BITS)?;
        let result = passage.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "direct normal material: {:?}",
                result.obstruction
            )));
        }
        Ok((
            ResidentNormalReturn {
                surface: self.surface,
                before,
                after,
                source,
                observed,
                roots: self.roots,
                targets: self.targets,
                grain: self.grain,
                predecessor_observations: self.observations,
                successor_observations: next_count,
            },
            next,
        ))
    }
}

#[cfg(test)]
mod tests;
