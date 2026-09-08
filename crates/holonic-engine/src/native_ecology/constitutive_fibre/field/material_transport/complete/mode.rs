//! The existing complete material operator received on an actual shared-drive source mode.
//! All coefficients come from retained native update factors. No coefficient is fitted here.
use super::*;
use crate::phase_current::{
    PhaseCurrentLineageId, PhaseCurrentReceiverId,
    resident::{ResidentPhaseCurrentError, ResidentPhaseEnclosureView},
};
use num_rational::BigRational as Rat;
use std::rc::Rc;

#[derive(Clone, Copy, Debug, Serialize)]
pub enum NativeMaterialModeComponent {
    ProducingMode,
    CurrentMode,
    ModeChange,
    ProducingRemainder,
    CurrentRemainder,
    ProducingFull,
    CurrentFull,
    FullChange,
}
impl NativeMaterialModeComponent {
    fn block(self) -> usize {
        match self {
            Self::ProducingMode => 3,
            Self::CurrentMode => 4,
            Self::ModeChange => 5,
            Self::ProducingRemainder => 6,
            Self::CurrentRemainder => 7,
            Self::ProducingFull => 8,
            Self::CurrentFull => 9,
            Self::FullChange => 10,
        }
    }
}
#[derive(Debug, Serialize)]
pub struct NativeMaterialModeDifferential {
    pub source_occurrence: usize,
    pub producing_operator_at: usize,
    pub current_operator_at: usize,
    pub component: NativeMaterialModeComponent,
    pub future_steps: u64,
    pub positive: u64,
    pub negative: u64,
    pub unresolved: u64,
    pub exact_zero: u64,
}

#[derive(Debug, Serialize)]
pub struct NativeMaterialModeReading {
    pub source_occurrence: usize,
    pub producing_operator_at: usize,
    pub current_operator_at: usize,
    pub receiving_occurrences: [usize; 2],
    pub direct_receiving_occurrence: Option<usize>,
    pub source_mode: NativeFieldCurrentBall,
    pub producing_coefficient: NativeFieldCurrentBall,
    pub current_coefficient: NativeFieldCurrentBall,
    pub coefficient_change: NativeFieldCurrentBall,
    pub producing_mode: NativeFieldCurrentBall,
    pub current_mode: NativeFieldCurrentBall,
    pub mode_change: NativeFieldCurrentBall,
    pub producing_remainder: NativeFieldCurrentBall,
    pub current_remainder: NativeFieldCurrentBall,
    pub producing_full: NativeFieldCurrentBall,
    pub current_full: NativeFieldCurrentBall,
    pub full_change: NativeFieldCurrentBall,
    pub actual_received: Option<NativeFieldCurrentBall>,
    pub whole_returned_difference: Option<NativeFieldCurrentBall>,
    pub numerical_coefficients: [Vec<ExactComplexWaveCurrent>; 2],
    pub numerical_modes: [Vec<ExactComplexWaveCurrent>; 2],
    pub numerical_full: [Vec<ExactComplexWaveCurrent>; 2],
    pub coefficient_rounding_residuals: [Vec<ExactComplexWaveCurrent>; 2],
    pub mode_rounding_residuals: [Vec<ExactComplexWaveCurrent>; 2],
    pub remainder_rounding_residuals: [Vec<ExactComplexWaveCurrent>; 2],
}
struct MaterialModeData<'c> {
    surface: &'c ResidentSurface<'c>,
    report: ResidentSection<'c>,
    _mode: NativeSharedDriveMode<'c>,
    nodes: usize,
    grain: u32,
    source: usize,
    cut: usize,
    births: [usize; 2],
    direct: bool,
}
pub struct NativeMaterialModeReturn<'c> {
    inner: Rc<MaterialModeData<'c>>,
}
pub struct NativeMaterialModeUnfolding<'c> {
    origin: Rc<MaterialModeData<'c>>,
    report: ResidentSection<'c>,
    steps: u64,
}

/// A borrowed temporal view of one complete all-node mode component.  The component and field
/// cuts remain attached to the view; the view itself does not select a numerical centre.
pub struct NativeMaterialModeComponentTemporalView<'view, 'c> {
    view: ResidentPhaseEnclosureView<'view, 'c>,
    component: NativeMaterialModeComponent,
    source_occurrence: usize,
    producing_operator_at: usize,
    current_operator_at: usize,
    receiving_occurrences: [usize; 2],
}

impl<'view, 'c> NativeMaterialModeComponentTemporalView<'view, 'c> {
    pub fn view(&self) -> ResidentPhaseEnclosureView<'_, 'c> {
        ResidentPhaseEnclosureView::new(
            self.view.section(),
            self.view.wide_offset(),
            self.view.grain(),
            self.view.receiver(),
            self.view.lineage(),
            self.view.origin().clone(),
            self.view.sample_step().clone(),
            self.view.phase_extent(),
            self.view.raw_extent(),
        )
        .expect("mode temporal view retains a validated resident carrier")
    }
    pub fn component(&self) -> NativeMaterialModeComponent {
        self.component
    }
    pub fn source_occurrence(&self) -> usize {
        self.source_occurrence
    }
    pub fn producing_operator_at(&self) -> usize {
        self.producing_operator_at
    }
    pub fn current_operator_at(&self) -> usize {
        self.current_operator_at
    }
    pub fn receiving_occurrences(&self) -> [usize; 2] {
        self.receiving_occurrences
    }
}

/// A borrowed temporal view of a frozen mode unfolding report.
pub struct NativeMaterialModeUnfoldingTemporalView<'view, 'c> {
    view: ResidentPhaseEnclosureView<'view, 'c>,
    source_occurrence: usize,
    producing_operator_at: usize,
    current_operator_at: usize,
    receiving_occurrences: [usize; 2],
    steps: u64,
}

impl<'view, 'c> NativeMaterialModeUnfoldingTemporalView<'view, 'c> {
    pub fn view(&self) -> ResidentPhaseEnclosureView<'_, 'c> {
        ResidentPhaseEnclosureView::new(
            self.view.section(),
            self.view.wide_offset(),
            self.view.grain(),
            self.view.receiver(),
            self.view.lineage(),
            self.view.origin().clone(),
            self.view.sample_step().clone(),
            self.view.phase_extent(),
            self.view.raw_extent(),
        )
        .expect("unfolded temporal view retains a validated resident carrier")
    }
    pub fn source_occurrence(&self) -> usize {
        self.source_occurrence
    }
    pub fn producing_operator_at(&self) -> usize {
        self.producing_operator_at
    }
    pub fn current_operator_at(&self) -> usize {
        self.current_operator_at
    }
    pub fn receiving_occurrences(&self) -> [usize; 2] {
        self.receiving_occurrences
    }
    pub fn steps(&self) -> u64 {
        self.steps
    }
}

fn ball(v: &[i128], n: usize, scale: &BigInt) -> NativeFieldCurrentBall {
    NativeFieldCurrentBall {
        center: v[..2 * n]
            .chunks_exact(2)
            .map(|p| {
                ExactComplexWaveCurrent::new(
                    Rat::new(p[0].into(), scale.clone()),
                    Rat::new(p[1].into(), scale.clone()),
                )
            })
            .collect(),
        radius: Rat::new(v[2 * n].into(), scale.clone()),
    }
}
impl<'c> NativeMaterialModeReturn<'c> {
    /// Borrow one complete temporal component without reading the native report.  The component
    /// blocks retain every field node; this is not a centre or a host reconstruction.
    pub fn temporal_view(
        &self,
        component: NativeMaterialModeComponent,
        receiver: PhaseCurrentReceiverId,
        lineage: PhaseCurrentLineageId,
        origin: Rat,
        sample_step: Rat,
        phase_extent: u32,
    ) -> Result<NativeMaterialModeComponentTemporalView<'_, 'c>, ResidentPhaseCurrentError> {
        let d = &self.inner;
        let stride = 2 * d.nodes + 1;
        let wide_offset = 3 + component.block() * stride;
        let view = ResidentPhaseEnclosureView::new(
            &d.report,
            wide_offset,
            d.grain,
            receiver,
            lineage,
            origin,
            sample_step,
            phase_extent,
            d.nodes,
        )?;
        Ok(NativeMaterialModeComponentTemporalView {
            view,
            component,
            source_occurrence: d.source,
            producing_operator_at: d.source,
            current_operator_at: d.cut,
            receiving_occurrences: d.births,
        })
    }

    pub fn read_pairs(
        &self,
        component: NativeMaterialModeComponent,
        pairs: usize,
    ) -> Result<NativeMaterialModeDifferential, ConstitutiveFibreError> {
        differential(
            &self.inner,
            &self.inner.report,
            2 * (3 + component.block() * (2 * self.inner.nodes + 1)),
            component,
            0,
            pairs,
        )
    }
    /// Unfold only this mode through the frozen current material map. Later changes to the
    /// field's operator require another read; they cannot rewrite this producing return.
    pub fn unfold_current(
        &self,
        steps: u64,
    ) -> Result<NativeMaterialModeUnfolding<'c>, ConstitutiveFibreError> {
        let d = &self.inner;
        let report = d
            .surface
            .fresh_section(1, 4 * d.nodes + 2, ResidentGrain(0))?;
        let mut passage = d.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            d.surface
                .record_material_mode_unfold(&lane, &d.report, d.nodes, steps, &report)?;
        }
        passage.close(0, &report, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "material mode unfolding: {:?}",
                receipt.obstruction
            )));
        }
        Ok(NativeMaterialModeUnfolding {
            origin: Rc::clone(&self.inner),
            report,
            steps,
        })
    }
    pub fn inspect(&self) -> Result<NativeMaterialModeReading, ConstitutiveFibreError> {
        let d = &self.inner;
        let n = d.nodes;
        let r = 2 * n;
        let stride = r + 1;
        let words = d.surface.read_out(&d.report)?;
        let raw_at = 2 * (3 + 13 * stride);
        let v = wides(&words[..raw_at])?;
        let scale = BigInt::one() << d.grain;
        if v[2] < 0 || (0..13).any(|i| v[3 + i * stride + r] < 0) {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let part = |i: usize| ball(&v[3 + i * stride..3 + (i + 1) * stride], n, &scale);
        let q = ball(&v[..3], 1, &scale);
        let read_raw = |which: usize,
                        den: &BigInt|
         -> Result<Vec<ExactComplexWaveCurrent>, ConstitutiveFibreError> {
            (0..n)
                .map(|row| {
                    let at = raw_at + 5 * (which * r + 2 * row);
                    complex256(&words[at..at + 10], den)
                })
                .collect()
        };
        let coeff_den = (&scale * &scale) * 2;
        let full_den = &scale * &scale * &scale;
        let coefficients = [read_raw(0, &coeff_den)?, read_raw(1, &coeff_den)?];
        let full = [read_raw(2, &full_den)?, read_raw(3, &full_den)?];
        let modes = coefficients.each_ref().map(|k| {
            k.iter()
                .map(|v| v.multiply(&q.center[0]))
                .collect::<Vec<_>>()
        });
        let coefficients_error =
            std::array::from_fn(|i| subtract(&part(i).center, &coefficients[i]));
        let modes_error = std::array::from_fn(|i| subtract(&part(3 + i).center, &modes[i]));
        let remainders_error =
            std::array::from_fn(|i| subtract(&part(6 + i).center, &subtract(&full[i], &modes[i])));
        Ok(NativeMaterialModeReading {
            source_occurrence: d.source,
            producing_operator_at: d.source,
            current_operator_at: d.cut,
            receiving_occurrences: d.births,
            direct_receiving_occurrence: d.direct.then_some(d.cut),
            source_mode: q,
            producing_coefficient: part(0),
            current_coefficient: part(1),
            coefficient_change: part(2),
            producing_mode: part(3),
            current_mode: part(4),
            mode_change: part(5),
            producing_remainder: part(6),
            current_remainder: part(7),
            producing_full: part(8),
            current_full: part(9),
            full_change: part(10),
            actual_received: d.direct.then(|| part(11)),
            whole_returned_difference: d.direct.then(|| part(12)),
            numerical_coefficients: coefficients,
            numerical_modes: modes,
            numerical_full: full,
            coefficient_rounding_residuals: coefficients_error,
            mode_rounding_residuals: modes_error,
            remainder_rounding_residuals: remainders_error,
        })
    }
}
impl NativeMaterialModeUnfolding<'_> {
    /// Borrow the complete unfolded all-node carrier without reading its native report.
    pub fn temporal_view(
        &self,
        receiver: PhaseCurrentReceiverId,
        lineage: PhaseCurrentLineageId,
        origin: Rat,
        sample_step: Rat,
        phase_extent: u32,
    ) -> Result<NativeMaterialModeUnfoldingTemporalView<'_, '_>, ResidentPhaseCurrentError> {
        let d = &self.origin;
        let view = ResidentPhaseEnclosureView::new(
            &self.report,
            0,
            d.grain,
            receiver,
            lineage,
            origin,
            sample_step,
            phase_extent,
            d.nodes,
        )?;
        Ok(NativeMaterialModeUnfoldingTemporalView {
            view,
            source_occurrence: d.source,
            producing_operator_at: d.source,
            current_operator_at: d.cut,
            receiving_occurrences: d.births,
            steps: self.steps,
        })
    }

    pub fn read_pairs(
        &self,
        pairs: usize,
    ) -> Result<NativeMaterialModeDifferential, ConstitutiveFibreError> {
        differential(
            &self.origin,
            &self.report,
            0,
            NativeMaterialModeComponent::CurrentMode,
            self.steps,
            pairs,
        )
    }
    pub fn steps(&self) -> u64 {
        self.steps
    }
    pub fn inspect(&self) -> Result<NativeFieldCurrentBall, ConstitutiveFibreError> {
        let v = wides(&self.origin.surface.read_out(&self.report)?)?;
        if v[2 * self.origin.nodes] < 0 {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        Ok(ball(
            &v,
            self.origin.nodes,
            &(BigInt::one() << self.origin.grain),
        ))
    }
}

fn differential<'c>(
    data: &MaterialModeData<'c>,
    report: &ResidentSection<'c>,
    offset: usize,
    component: NativeMaterialModeComponent,
    steps: u64,
    pairs: usize,
) -> Result<NativeMaterialModeDifferential, ConstitutiveFibreError> {
    let s = data.surface;
    let output = s.fresh_section(1, 4, ResidentGrain(0))?;
    let mut passage = s.begin_passage(&[vec![]])?;
    {
        let lane = passage.open(0, &[])?;
        s.record_ball_differential(&lane, report, offset, 2 * data.nodes, pairs, &output)?;
    }
    passage.close(0, &output, 64)?;
    let receipt = passage.finish()?.launch()?;
    if !receipt.obstruction.is_empty() {
        return Err(ConstitutiveFibreError::Arithmetic(format!(
            "material mode differential: {:?}",
            receipt.obstruction
        )));
    }
    let words = s.read_out(&output)?;
    if words.iter().any(|(a, b)| a != b || *a < 0) {
        return Err(ConstitutiveFibreError::Uncertain);
    }
    Ok(NativeMaterialModeDifferential {
        source_occurrence: data.source,
        producing_operator_at: data.source,
        current_operator_at: data.cut,
        component,
        future_steps: steps,
        positive: words[0].0 as u64,
        negative: words[1].0 as u64,
        unresolved: words[2].0 as u64,
        exact_zero: words[3].0 as u64,
    })
}

impl<'c> NativeConstitutiveField<'c> {
    pub fn read_material_mode(
        &mut self,
        source: &NativeFieldSourceAnchor,
        left: usize,
        right: usize,
    ) -> Result<NativeMaterialModeReturn<'c>, ConstitutiveFibreError> {
        if !Rc::ptr_eq(&source.owner, &self.owner) {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        self.read_material_mode_at(source.occurrence, left, right)
    }
    /// Read-only decomposition of M x at an actual historical source. Both mode contacts must
    /// already exist there. The current map is the committed successor at the reported cut.
    pub fn read_material_mode_at(
        &mut self,
        source: usize,
        left: usize,
        right: usize,
    ) -> Result<NativeMaterialModeReturn<'c>, ConstitutiveFibreError> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        if self.material_transport_source() != Some(NativeMaterialTransportSource::CompleteCurrent)
        {
            return Err(invalid("complete source transport required for mode"));
        }
        if source >= self.history.len() || source < left.max(right) {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        let mode = self.condense_shared_drive_mode(left, right)?;
        self.read_material_mode_using(source, &mode)
    }

    /// Reuse the same immutable mode origin as the field continues. Standalone/imported mode
    /// files carry no right to index another body's internal columns; their unfolding remains
    /// available, while an in-body material read requires this actual origin ownership.
    pub fn read_material_mode_using(
        &mut self,
        source: usize,
        mode: &NativeSharedDriveMode<'c>,
    ) -> Result<NativeMaterialModeReturn<'c>, ConstitutiveFibreError> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        if self.material_transport_source() != Some(NativeMaterialTransportSource::CompleteCurrent)
        {
            return Err(invalid("complete source transport required for mode"));
        }
        let ([left, right], mode_cut) = mode
            .material_origin(&self.owner)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        if source >= self.history.len() || source < left.max(right) {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        let cut = self.history.len() - 1;
        let minimum = left.min(right);
        let maximum = left.max(right);
        let factors = (0..=cut)
            .filter_map(|at| {
                self.history[at]
                    .lineage
                    .received_from
                    .filter(|s| *s >= minimum)
                    .map(|s| (at, s))
            })
            .collect::<Vec<_>>();
        for &(at, s) in &factors {
            self.mount_history_source(at)?;
            if s < maximum {
                self.mount_history_source(s)?;
            }
        }
        self.mount_history_source(source)?;
        let refreshed = self.prepare_current_source_refresh(source)?;
        let surface = self.relation.surface;
        let n = self.nodes();
        let grain = self.transport_grain()?;
        let mut pointers = Vec::with_capacity(4 * factors.len().max(1));
        for &(at, s) in &factors {
            let increment = self.history[at]
                .resident()?
                .transport
                .as_ref()
                .ok_or_else(|| invalid("missing native coefficient factor"))?;
            let prefix = if s < maximum {
                self.history[s]
                    .resident()?
                    .junction
                    .as_ref()
                    .ok_or(ConstitutiveFibreError::Uncertain)?
                    .lo_device_ptr()
            } else {
                0
            };
            for p in [
                increment.lo_device_ptr() as i64,
                prefix as i64,
                s as i64,
                at as i64,
            ] {
                pointers.push((p, p));
            }
        }
        if pointers.is_empty() {
            pointers.resize(4, (0, 0));
        }
        let chart = surface.mount_section_rest(
            &ResidentSectionRest::found(factors.len().max(1), 4, ResidentGrain(0), 64, pointers)
                .map_err(invalid)?,
        )?;
        let output = surface.fresh_section(1, 92 * n + 32, ResidentGrain(0))?;
        let direct = self.history[cut].lineage.received_from == Some(source);
        let src = self.history[source]
            .resident()?
            .transport
            .as_deref()
            .ok_or_else(|| invalid("missing source transport"))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            if let Some(refresh) = &refreshed {
                surface.record_complete_material_source_current(
                    &lane,
                    src,
                    &refresh.tail,
                    refresh.count,
                    n,
                    &refresh.output,
                )?;
            }
            let (contact, amplitude) = mode.native_parts();
            surface.record_complete_material_mode(
                &lane,
                &self.transport.as_ref().unwrap().state,
                src,
                refreshed.as_ref().map(|r| &r.output),
                if direct {
                    self.history[cut].resident()?.transport.as_deref()
                } else {
                    None
                },
                contact,
                amplitude,
                self.history[left - 1]
                    .resident()?
                    .junction
                    .as_deref()
                    .ok_or(ConstitutiveFibreError::Uncertain)?,
                self.history[right - 1]
                    .resident()?
                    .junction
                    .as_deref()
                    .ok_or(ConstitutiveFibreError::Uncertain)?,
                &chart,
                factors.len(),
                n,
                grain,
                left,
                right,
                source,
                cut,
                mode_cut,
                &output,
            )?;
        }
        passage.close(0, &output, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "material mode: {:?}",
                receipt.obstruction
            )));
        }
        Ok(NativeMaterialModeReturn {
            inner: Rc::new(MaterialModeData {
                surface,
                report: output,
                _mode: mode.share_origin(),
                nodes: n,
                grain,
                source,
                cut,
                births: [left, right],
                direct,
            }),
        })
    }
}

#[cfg(test)]
mod tests;
