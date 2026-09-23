//! The existing accumulated normal response with direct resident-current operands.
//! The current three-port source chart is explicit. No occurrence archive or field handle is
//! needed to develop or query this local material; exact moments own its continuing geometry.
use super::*;
use std::rc::Rc;
mod rest;
pub use rest::NormalMaterialRest;
mod boundary;
pub use boundary::{BoundaryMaterialMaps, BoundaryMaterialSeed};
mod refine;


#[cfg(test)]
mod conditional_tests;
mod enclosure;
mod enclosure_ports;
mod held_section;
pub use enclosure::{ResidentNormalEnclosure, ResidentNormalEnclosureView, ResidentNormalInput};
pub use held_section::{ResidentHeldSection, ResidentHeldSectionRest};
mod applied_relation;
mod joined_source;
pub use section::{
    NativeAffineGeometry, NativeAffineGeometryAdjoint, NativeEnclosurePropagation,
    NativeRealification, NativeRealificationAdjoint,
};
mod section;
pub use section::{ResidentNormalEnclosureSection, ResidentNormalSectionReturn};
mod section_basis;
pub use section_basis::NormalSectionBasisFace;
mod reaction_law;
pub use reaction_law::{NormalReactionProjection, PowerNeutralCertificate};

/// [definition] **The one refusal of the normal Holon** (plan phase 9). A move-owned operation
/// that fails returns every owner it took (`returned`) with the reason; nothing is lost and no
/// partial state is published. The former per-operation refusals are this type at their
/// owners: `NormalWaveSeedRefusal` (the constitution), `NormalCoupledAttachRefusal` (the wave and
/// neighborhood), `CoupledConstitutiveRefusal` (wave, comparison, receiver) and
/// `ConstitutiveSourceRefusal` (the source packet).
pub struct NormalRefusal<T> {
    pub returned: T,
    pub reason: ConstitutiveFibreError,
}
impl<T> NormalRefusal<T> {
    pub fn new(returned: T, reason: ConstitutiveFibreError) -> Self {
        Self { returned, reason }
    }
}
impl<T> std::fmt::Debug for NormalRefusal<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.reason.fmt(f)
    }
}
impl<T> From<NormalRefusal<T>> for ConstitutiveFibreError {
    fn from(refusal: NormalRefusal<T>) -> Self {
        refusal.reason
    }
}

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
pub use wave::*;

/// [definition] **The normal constitution on its resident chart** (plan phase 9): the element
/// relation `W H = B` of the normal law — accumulated source Gram `H` (storage), cross moment `B`,
/// target energy `C`, optional immutable prior `(B₀, C₀)` and the applied dyadic coefficients `W`
/// with their certified normal-reference defect — mounted as one device section. Its exact host
/// reading is [`NormalConstitution`]. A clone shares the immutable device section: it is the
/// retained cut ("view") of a forecast or delayed receiver, and a mutation (`receive`, a
/// refinement) replaces the owner's section without touching any other clone. There is no
/// separate view type (`ResidentNormalMaterialView` is this type).
#[derive(Clone)]
pub struct ResidentNormalMaterial<'c> {
    pub(crate) surface: &'c ResidentSurface<'c>,
    pub(crate) state: Rc<ResidentSection<'c>>,
    pub(crate) source_chart: NormalSourceChart,
    pub(crate) targets: usize,
    pub(crate) grain: ResidentGrain,
    pub(crate) observations: u64,
    pub(crate) prior: Option<NativeNormalPrior>,
}

/// Compatibility name: the retained immutable cut is the constitution itself (a shared clone).
pub type ResidentNormalMaterialView<'c> = ResidentNormalMaterial<'c>;

impl<'c> ResidentNormalMaterial<'c> {
    /// Execute M[s,h,h⊗s] at fixed exact h, retaining the actual affine source restriction.
    /// Only A(h), not the independent condition coefficients, transports source uncertainty.
    pub fn read_applied_bilinear(
        &self,
        source: ResidentNormalEnclosureView<'_, 'c>,
        condition: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<ResidentNormalEnclosure<'c>, ConstitutiveFibreError> {
        let d = source.components();
        let k = condition.components();
        let features = d
            .checked_mul(k / 2)
            .and_then(|v| v.checked_add(d)?.checked_add(k))
            .ok_or(ConstitutiveFibreError::Shape)?;
        if self.source_chart
            != (NormalSourceChart::Features {
                source_complex: features / 2,
            })
            || source.grain() != self.grain
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let width = self
            .targets
            .checked_mul(2)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let section = self
            .surface
            .fresh_section(1, 2 * (width + 1), ResidentGrain(0))?;
        let mut pass = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = pass.open(0, &[])?;
            self.surface.record_normal_applied_condition(
                &lane,
                &self.state,
                source,
                condition,
                self.targets,
                None,
                false,
                &section,
            )?;
        }
        pass.close(0, &section, 64)?;
        let result = pass.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "applied conditional reaction: {:?}",
                result.obstruction
            )));
        }
        Ok(ResidentNormalEnclosure {
            surface: self.surface,
            section,
            width,
            grain: self.grain,
        })
    }
    /// Execute x+M[x,h,h⊗x] as one affine action of the incoming source. The
    /// identity path and reaction share x; its uncertainty is transported by I+A(h).
    pub fn read_applied_bilinear_identity(
        &self,
        source: ResidentNormalEnclosureView<'_, 'c>,
        condition: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<ResidentNormalEnclosure<'c>, ConstitutiveFibreError> {
        let d = source.components();
        let k = condition.components();
        let features = d
            .checked_mul(k / 2)
            .and_then(|v| v.checked_add(d)?.checked_add(k))
            .ok_or(ConstitutiveFibreError::Shape)?;
        if self.source_chart
            != (NormalSourceChart::Features {
                source_complex: features / 2,
            })
            || source.grain() != self.grain
            || d != 2 * self.targets
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let section = self
            .surface
            .fresh_section(1, 2 * (d + 1), ResidentGrain(0))?;
        let mut pass = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = pass.open(0, &[])?;
            self.surface.record_normal_applied_condition(
                &lane,
                &self.state,
                source,
                condition,
                self.targets,
                None,
                true,
                &section,
            )?;
        }
        pass.close(0, &section, 64)?;
        let result = pass.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "incoming conditional reaction: {:?}",
                result.obstruction
            )));
        }
        Ok(ResidentNormalEnclosure {
            surface: self.surface,
            section,
            width: d,
            grain: self.grain,
        })
    }
    /// At fixed h apply (s,b) -> (x+A(h)s+c(h),b) to one joint ball. The
    /// unchanged tail is part of that same source, not an independently joined enclosure.
    pub fn read_applied_bilinear_joint(
        &self,
        source: ResidentNormalEnclosureView<'_, 'c>,
        boundary_components: usize,
        condition: ResidentConstitutiveCurrent<'_, 'c>,
        external: ResidentNormalEnclosureView<'_, 'c>,
    ) -> Result<ResidentNormalEnclosure<'c>, ConstitutiveFibreError> {
        let d = boundary_components;
        let k = condition.components();
        let features = d
            .checked_mul(k / 2)
            .and_then(|v| v.checked_add(d)?.checked_add(k))
            .ok_or(ConstitutiveFibreError::Shape)?;
        if self.source_chart
            != (NormalSourceChart::Features {
                source_complex: features / 2,
            })
            || source.grain() != self.grain
            || external.grain() != self.grain
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let tail = source
            .components()
            .checked_sub(d)
            .ok_or(ConstitutiveFibreError::Shape)?;
        let width = self
            .targets
            .checked_mul(2)
            .and_then(|v| v.checked_add(tail))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let words = width
            .checked_add(1)
            .and_then(|v| v.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let section = self.surface.fresh_section(1, words, ResidentGrain(0))?;
        let mut pass = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = pass.open(0, &[])?;
            self.surface.record_normal_applied_condition(
                &lane,
                &self.state,
                source,
                condition,
                self.targets,
                Some((d, external)),
                false,
                &section,
            )?;
        }
        pass.close(0, &section, 64)?;
        let result = pass.finish()?.launch()?;
        if !result.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "applied conditional joint current: {:?}",
                result.obstruction
            )));
        }
        Ok(ResidentNormalEnclosure {
            surface: self.surface,
            section,
            width,
            grain: self.grain,
        })
    }
}

/// A receiver result with its actual borrowed operands. Forward/return currents are complete
/// balls; there is no method that turns their numerical centres into point-current inputs.
pub struct ResidentNormalReturn<'a, 'c> {
    surface: &'c ResidentSurface<'c>,
    before: ResidentSection<'c>,
    after: Option<ResidentSection<'c>>,
    source: ResidentNormalInput<'a, 'c>,
    observed: Option<ResidentNormalInput<'a, 'c>>,
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
    pub fn observed(&self) -> Option<ResidentNormalInput<'_, 'c>> {
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
    /// Retain an immutable resident producing cut for a forecast or delayed
    /// receiver.  The view keeps the device section and does not detach its
    /// numerical state to the host.
    pub fn retained_view(&self) -> ResidentNormalMaterialView<'c> {
        self.clone()
    }
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

    /// Found a feature chart with the explicit nonzero normal prior H₀=I,
    /// B₀=W₀.  Legacy constructors retain their zero B₀ behavior.
    pub fn found_features_with_prior(
        surface: &'c ResidentSurface<'c>,
        source_complex: usize,
        targets: usize,
        grain: ResidentGrain,
        prior: NativeNormalPrior,
    ) -> Result<Self, ConstitutiveFibreError> {
        if !(1..=120).contains(&grain.0) {
            return Err(ConstitutiveFibreError::Shape);
        }
        let source_chart = NormalSourceChart::Features { source_complex };
        let layout = source_chart.layout(targets)?;
        let values =
            initial_words_for_sources_with_prior(layout.sources, targets, grain.0, &prior)?;
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
            prior: Some(prior),
        })
    }

    pub fn prior(&self) -> Option<&NativeNormalPrior> {
        self.prior.as_ref()
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
            prior: None,
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
    pub fn grain(&self) -> ResidentGrain {
        self.grain
    }
    pub fn inspect(&self) -> Result<NormalConstitution, ConstitutiveFibreError> {
        expose_data_energy(
            decode_state_layout(
                &self.surface.detach_section(&self.state, i64::BITS)?,
                self.source_chart.layout(self.targets)?,
                self.targets,
                self.grain.0,
            )?,
            self.prior.as_ref(),
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
    /// Apply the stored dyadic coefficient map. Input-family and arithmetic errors remain in
    /// the output; the separate normal-equation comparison remains in the returned metadata
    /// and material. This is the same applied/reference distinction used by native wave transport.
    pub fn read_applied<'a>(
        &self,
        source: impl Into<ResidentNormalInput<'a, 'c>>,
    ) -> Result<ResidentNormalReturn<'a, 'c>, ConstitutiveFibreError> {
        Ok(self.prepare_mode(source.into(), None, false)?.0)
    }
    pub fn receive<'a>(
        &mut self,
        source: impl Into<ResidentNormalInput<'a, 'c>>,
        observed: impl Into<ResidentNormalInput<'a, 'c>>,
    ) -> Result<ResidentNormalReturn<'a, 'c>, ConstitutiveFibreError> {
        let (returned, next) = self.prepare(source.into(), Some(observed.into()))?;
        self.state = Rc::new(next.ok_or(ConstitutiveFibreError::Shape)?);
        self.observations = returned.successor_observations;
        Ok(returned)
    }
    fn prepare<'a>(
        &self,
        source: ResidentNormalInput<'a, 'c>,
        observed: Option<ResidentNormalInput<'a, 'c>>,
    ) -> Result<(ResidentNormalReturn<'a, 'c>, Option<ResidentSection<'c>>), ConstitutiveFibreError>
    {
        self.prepare_mode(source, observed, true)
    }
    fn prepare_mode<'a>(
        &self,
        source: ResidentNormalInput<'a, 'c>,
        observed: Option<ResidentNormalInput<'a, 'c>>,
        reference: bool,
    ) -> Result<(ResidentNormalReturn<'a, 'c>, Option<ResidentSection<'c>>), ConstitutiveFibreError>
    {
        let layout = self.source_chart.layout(self.targets)?;
        if source.width() != layout.source_components
            || observed.is_some_and(|y| y.width() != layout.target_components)
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
                reference,
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
mod enclosed_target_tests;
#[cfg(test)]
mod tests;
