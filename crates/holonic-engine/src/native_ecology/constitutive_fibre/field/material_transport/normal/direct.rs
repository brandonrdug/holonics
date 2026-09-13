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

/// Declared domain of the same normal-statistic operator. A feature chart is not silently
/// padded or identified with the wave's three equally sized physical/current ports.
#[derive(Clone, Copy, Debug, PartialEq, Eq, serde::Serialize, serde::Deserialize)]
#[serde(tag = "kind", rename_all = "kebab-case")]
pub enum NormalSourceChart {
    Wave { roots: usize },
    Features { source_complex: usize },
}
impl NormalSourceChart {
    pub fn wave_roots(self) -> Option<usize> {
        match self {
            Self::Wave { roots } => Some(roots),
            Self::Features { .. } => None,
        }
    }
    pub fn complex_sources(self) -> Option<usize> {
        match self {
            Self::Wave { roots } => roots.checked_mul(3),
            Self::Features { source_complex } => Some(source_complex),
        }
    }
    pub(super) fn layout(self, targets: usize) -> Result<NormalLayout, ConstitutiveFibreError> {
        NormalLayout::for_sources(
            self.complex_sources()
                .ok_or(ConstitutiveFibreError::Shape)?,
            targets,
        )
        .ok_or(ConstitutiveFibreError::Shape)
    }
}
mod wave;
pub use wave::{
    CompiledCoupledJoint, ConstitutiveComparisonSection, ConstitutiveSourceFrame,
    ConstitutiveSourceRefusal, CoupledConstitutiveAlternative, CoupledConstitutiveFamily,
    CoupledConstitutiveRefusal, CoupledConstitutiveRest, CoupledJointEvaluation,
    CoupledJointReading, FamilyBasisReading, FamilyBasisSelection, NormalBasisScore,
    NormalBasisSelection, NormalContinuationJoin, NormalContinuationPullback,
    NormalCoupledAttachRefusal, NormalCoupledComparison, NormalCoupledContact,
    NormalCoupledContinuation, NormalCoupledPrediction, NormalCoupledProducingHandle,
    NormalCoupledReception, NormalCoupledSourceActuation, NormalCoupledStep, NormalFamilyBasisFace,
    NormalFamilyComparisonRow, NormalFamilyPullback, NormalFamilyReceiverReading,
    NormalFamilySupport, NormalProducingHandle, NormalReceiverCoordinates, NormalSourceActuation,
    NormalWaveBasisChart, NormalWaveBasisFace, NormalWaveBasisReading, NormalWaveComparison,
    NormalWaveComparisonReading, NormalWaveCoupled, NormalWaveCurrent, NormalWaveDevelopment,
    NormalWaveFacePacket, NormalWaveFamily, NormalWaveFamilyReceiver, NormalWaveFamilyRest,
    NormalWaveFibre, NormalWaveJointSource, NormalWavePrediction, NormalWaveReading,
    NormalWaveReception, NormalWaveReceptionReading, NormalWaveReference,
    NormalWaveReferenceReading, NormalWaveRest, NormalWaveSeedKind, NormalWaveSeedRefusal,
    NormalWaveSource, NormalWaveStep, NormalWaveTransport, NormalWaveTransportChange,
    NormalWaveWord, ResidentCoupledConstitutive, ResidentNormalWave,
};

pub struct ResidentNormalMaterial<'c> {
    surface: &'c ResidentSurface<'c>,
    state: Rc<ResidentSection<'c>>,
    source_chart: NormalSourceChart,
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
    source_chart: NormalSourceChart,
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
        decode_report_layout(
            &rest,
            self.source_chart.layout(self.targets)?,
            self.grain.0,
            false,
        )
    }
    pub fn inspect_after(
        &self,
    ) -> Result<Option<NativeNormalMaterialReading>, ConstitutiveFibreError> {
        self.after
            .as_ref()
            .map(|section| {
                let rest = self.surface.detach_section(section, i64::BITS)?;
                decode_report_layout(
                    &rest,
                    self.source_chart.layout(self.targets)?,
                    self.grain.0,
                    true,
                )
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
        Self::found_in_chart(surface, NormalSourceChart::Wave { roots }, targets, grain)
    }
    /// Fit arbitrary declared complex features through the same resident unit-prior normal
    /// geometry. Features can be native restrictions or joined bilinear products.
    pub fn found_features(
        surface: &'c ResidentSurface<'c>,
        source_complex: usize,
        targets: usize,
        grain: ResidentGrain,
    ) -> Result<Self, ConstitutiveFibreError> {
        Self::found_in_chart(
            surface,
            NormalSourceChart::Features { source_complex },
            targets,
            grain,
        )
    }
    fn found_in_chart(
        surface: &'c ResidentSurface<'c>,
        source_chart: NormalSourceChart,
        targets: usize,
        grain: ResidentGrain,
    ) -> Result<Self, ConstitutiveFibreError> {
        if !(1..=120).contains(&grain.0) {
            return Err(ConstitutiveFibreError::Shape);
        }
        let layout = source_chart.layout(targets)?;
        let values = initial_words_for_sources(layout.sources, targets, grain.0)?;
        let state = surface.mount_section_rest(
            &ResidentSectionRest::found(1, values.len(), ResidentGrain(0), i64::BITS, values)
                .map_err(invalid)?,
        )?;
        Ok(Self {
            surface,
            state: Rc::new(state),
            source_chart,
            targets,
            grain,
            observations: 0,
        })
    }
    pub fn observations(&self) -> u64 {
        self.observations
    }
    /// Number of wave roots; a Features chart has no wave roots. Use `source_chart` for
    /// the domain and `source_complex` for its feature width.
    pub fn roots(&self) -> usize {
        self.source_chart.wave_roots().unwrap_or(0)
    }
    pub fn source_chart(&self) -> NormalSourceChart {
        self.source_chart
    }
    pub fn source_complex(&self) -> usize {
        self.source_chart
            .complex_sources()
            .expect("admitted normal chart")
    }
    pub fn targets(&self) -> usize {
        self.targets
    }
    pub fn inspect(&self) -> Result<NativeNormalMaterialState, ConstitutiveFibreError> {
        decode_state_layout(
            &self.surface.detach_section(&self.state, i64::BITS)?,
            self.source_chart.layout(self.targets)?,
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
        let layout = self.source_chart.layout(self.targets)?;
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
                self.source_complex(),
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
                source_chart: self.source_chart,
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
