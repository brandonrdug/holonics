//! Resident dyadic balls for temporal phase currents.
//!
//! The centre and one global Euclidean radius remain on the resident surface.  This owner
//! provides no point-current view of a centre: its cold inspection is the only operation which
//! turns a completed report into a `NativeFieldCurrentBall`.

use super::*;
use crate::dimensional_wave::ExactComplexWaveCurrent;
use crate::native_ecology::constitutive_fibre::NativeFieldCurrentBall;
use num_bigint::BigInt;
use num_traits::One;

fn malformed() -> ResidentPhaseCurrentError {
    PhaseCurrentError::MalformedSection.into()
}

fn wire_words(raw_extent: usize) -> Result<usize, ResidentPhaseCurrentError> {
    raw_extent
        .checked_mul(2)
        .and_then(|n| n.checked_add(1))
        .and_then(|n| n.checked_mul(2))
        .ok_or_else(|| PhaseCurrentError::CarrierOverflow.into())
}

fn output_width(raw_extent: usize) -> Result<usize, ResidentPhaseCurrentError> {
    wire_words(raw_extent)
}

fn validate_enclosure_shape(
    section: &ResidentSection<'_>,
    wide_offset: usize,
    grain: u32,
    raw_extent: usize,
    phase_extent: u32,
    sample_step: &Rat,
) -> Result<(), ResidentPhaseCurrentError> {
    let wide_count = wire_words(raw_extent)? / 2;
    if !(1..=120).contains(&grain)
        || raw_extent == 0
        || phase_extent == 0
        || !sample_step.is_positive()
        || section.rows() != 1
        || section.width() % 2 != 0
        || section.grain().0 != 0
        || wide_offset
            .checked_add(wide_count)
            .is_none_or(|end| end > section.width() / 2)
    {
        return Err(malformed());
    }
    Ok(())
}

fn signed_wide(words: &[(i64, i64)]) -> Result<i128, ResidentPhaseCurrentError> {
    if words.len() != 2 || words.iter().any(|(lo, hi)| lo != hi) {
        return Err(ConstitutiveFibreError::Uncertain.into());
    }
    Ok((((words[1].0 as u64 as u128) << 64) | words[0].0 as u64 as u128) as i128)
}

/// A borrowed receiver-relative view into a resident temporal enclosure report.
pub struct ResidentPhaseEnclosureView<'section, 'chart> {
    pub(crate) section: &'section ResidentSection<'chart>,
    pub(crate) wide_offset: usize,
    pub(crate) grain: u32,
    pub(crate) receiver: PhaseCurrentReceiverId,
    pub(crate) lineage: PhaseCurrentLineageId,
    pub(crate) origin: Rat,
    pub(crate) sample_step: Rat,
    pub(crate) phase_extent: u32,
    pub(crate) raw_extent: usize,
}

impl<'section, 'chart> ResidentPhaseEnclosureView<'section, 'chart> {
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn new(
        section: &'section ResidentSection<'chart>,
        wide_offset: usize,
        grain: u32,
        receiver: PhaseCurrentReceiverId,
        lineage: PhaseCurrentLineageId,
        origin: Rat,
        sample_step: Rat,
        phase_extent: u32,
        raw_extent: usize,
    ) -> Result<Self, ResidentPhaseCurrentError> {
        validate_enclosure_shape(
            section,
            wide_offset,
            grain,
            raw_extent,
            phase_extent,
            &sample_step,
        )?;
        Ok(Self {
            section,
            wide_offset,
            grain,
            receiver,
            lineage,
            origin,
            sample_step,
            phase_extent,
            raw_extent,
        })
    }

    /// The whole serialized carrier; a view may occupy a nonzero wide offset within it.
    pub fn section(&self) -> &ResidentSection<'chart> {
        self.section
    }
    pub fn wide_offset(&self) -> usize {
        self.wide_offset
    }
    pub fn grain(&self) -> u32 {
        self.grain
    }
    pub fn raw_extent(&self) -> usize {
        self.raw_extent
    }
    pub fn receiver(&self) -> PhaseCurrentReceiverId {
        self.receiver
    }
    pub fn lineage(&self) -> PhaseCurrentLineageId {
        self.lineage
    }
    pub fn origin(&self) -> &Rat {
        &self.origin
    }
    pub fn sample_step(&self) -> &Rat {
        &self.sample_step
    }
    pub fn phase_extent(&self) -> u32 {
        self.phase_extent
    }

    /// Cold observation of the complete centre and global Euclidean radius.
    pub fn inspect(
        &self,
        surface: &ResidentSurface<'chart>,
    ) -> Result<NativeFieldCurrentBall, ResidentPhaseCurrentError> {
        if !self.section.belongs_to(surface) {
            return Err(ConstitutiveFibreError::Shape.into());
        }
        validate_enclosure_shape(
            self.section,
            self.wide_offset,
            self.grain,
            self.raw_extent,
            self.phase_extent,
            &self.sample_step,
        )?;
        let words = surface.read_out(self.section)?;
        let end = self
            .wide_offset
            .checked_add(wire_words(self.raw_extent)? / 2)
            .ok_or(PhaseCurrentError::CarrierOverflow)?;
        if end > words.len() / 2 {
            return Err(malformed());
        }
        let numerator = |index: usize| {
            let wide_at = self
                .wide_offset
                .checked_add(index)
                .and_then(|at| at.checked_mul(2))
                .ok_or(PhaseCurrentError::CarrierOverflow)?;
            signed_wide(&words[wide_at..wide_at + 2])
        };
        let scale = BigInt::one() << self.grain;
        let mut center = Vec::with_capacity(self.raw_extent);
        for index in 0..self.raw_extent {
            center.push(ExactComplexWaveCurrent::new(
                Rat::new(numerator(2 * index)?.into(), scale.clone()),
                Rat::new(numerator(2 * index + 1)?.into(), scale.clone()),
            ));
        }
        let radius_numerator = numerator(2 * self.raw_extent)?;
        if radius_numerator < 0 {
            return Err(ConstitutiveFibreError::Uncertain.into());
        }
        Ok(NativeFieldCurrentBall {
            center,
            radius: Rat::new(radius_numerator.into(), scale),
        })
    }
}

/// An owned lift of an exact temporal point into a resident dyadic enclosure.
pub struct ResidentPhaseEnclosure<'point, 'chart> {
    point: ResidentPhaseCurrentView<'point, 'chart>,
    output: ResidentSection<'chart>,
    grain: u32,
}

impl<'point, 'chart> ResidentPhaseEnclosure<'point, 'chart> {
    pub fn point(&self) -> &ResidentPhaseCurrentView<'point, 'chart> {
        &self.point
    }
    pub fn section(&self) -> &ResidentSection<'chart> {
        &self.output
    }
    pub fn view(&self) -> ResidentPhaseEnclosureView<'_, 'chart> {
        ResidentPhaseEnclosureView::new(
            &self.output,
            0,
            self.grain,
            self.point.receiver(),
            self.point.lineage(),
            self.point.origin().clone(),
            self.point.sample_step().clone(),
            self.point.phase_extent(),
            self.point.raw_extent(),
        )
        .expect("resident enclosure owns a validated report")
    }
    pub(crate) fn into_section(self) -> ResidentSection<'chart> {
        self.output
    }
}

/// A causal convolution whose response operand is an enclosed resident carrier.
pub struct ResidentEnclosedPhaseConvolution<'source, 'response, 'chart> {
    source: ResidentPhaseCurrentView<'source, 'chart>,
    response: ResidentPhaseEnclosureView<'response, 'chart>,
    output: ResidentSection<'chart>,
    target_receiver: PhaseCurrentReceiverId,
    target_lineage: PhaseCurrentLineageId,
}

impl<'source, 'response, 'chart> ResidentEnclosedPhaseConvolution<'source, 'response, 'chart> {
    pub fn source(&self) -> &ResidentPhaseCurrentView<'source, 'chart> {
        &self.source
    }
    pub fn response(&self) -> &ResidentPhaseEnclosureView<'response, 'chart> {
        &self.response
    }
    pub fn section(&self) -> &ResidentSection<'chart> {
        &self.output
    }
    pub fn view(&self) -> ResidentPhaseEnclosureView<'_, 'chart> {
        ResidentPhaseEnclosureView::new(
            &self.output,
            0,
            self.response.grain,
            self.target_receiver,
            self.target_lineage,
            self.source.origin() + self.response.origin(),
            self.source.sample_step().clone(),
            self.source.phase_extent(),
            self.source.raw_extent() + self.response.raw_extent() - 1,
        )
        .expect("resident enclosed convolution owns a validated report")
    }
    pub(crate) fn into_section(self) -> ResidentSection<'chart> {
        self.output
    }
}

/// An exact observation minus an enclosed prediction, with the complete support receipt kept.
pub struct ResidentEnclosedPhaseDifference<'predicted, 'observed, 'chart> {
    predicted: ResidentPhaseEnclosureView<'predicted, 'chart>,
    observed: ResidentPhaseCurrentView<'observed, 'chart>,
    support: PhaseComparisonSupport,
    output: ResidentSection<'chart>,
    lineage: PhaseCurrentLineageId,
}

impl<'predicted, 'observed, 'chart> ResidentEnclosedPhaseDifference<'predicted, 'observed, 'chart> {
    pub fn predicted(&self) -> &ResidentPhaseEnclosureView<'predicted, 'chart> {
        &self.predicted
    }
    pub fn observed(&self) -> &ResidentPhaseCurrentView<'observed, 'chart> {
        &self.observed
    }
    pub fn support(&self) -> &PhaseComparisonSupport {
        &self.support
    }
    pub fn section(&self) -> &ResidentSection<'chart> {
        &self.output
    }
    pub fn view(&self) -> ResidentPhaseEnclosureView<'_, 'chart> {
        ResidentPhaseEnclosureView::new(
            &self.output,
            0,
            self.predicted.grain,
            self.observed.receiver(),
            self.lineage,
            self.support.begin.clone(),
            self.observed.sample_step().clone(),
            self.observed.phase_extent(),
            self.support.predicted.len(),
        )
        .expect("resident enclosed difference owns a validated report")
    }
    pub(crate) fn into_section(self) -> ResidentSection<'chart> {
        self.output
    }
}

pub fn enclose_resident<'source, 'chart>(
    surface: &'chart ResidentSurface<'chart>,
    point: ResidentPhaseCurrentView<'source, 'chart>,
    grain: u32,
) -> Result<ResidentPhaseEnclosure<'source, 'chart>, ResidentPhaseCurrentError> {
    if !(1..=120).contains(&grain) {
        return Err(malformed());
    }
    surface.validate_constitutive_current_view(point.current)?;
    let width = output_width(point.raw_extent())?;
    let output = surface.fresh_section(1, width, ResidentGrain(0))?;
    let mut passage = surface.begin_passage(&[vec![]])?;
    {
        let lane = passage.open(0, &[])?;
        surface.record_phase_enclosure_lift(
            &lane,
            point.current,
            point.raw_extent(),
            grain,
            &output,
        )?;
    }
    passage.close(0, &output, 64)?;
    let receipt = passage.finish()?.launch()?;
    if !receipt.obstruction.is_empty() {
        return Err(ConstitutiveFibreError::Arithmetic(format!(
            "phase enclosure lift: {:?}",
            receipt.obstruction
        ))
        .into());
    }
    Ok(ResidentPhaseEnclosure {
        point,
        output,
        grain,
    })
}

pub fn convolve_enclosed_resident<'source, 'response, 'chart>(
    surface: &'chart ResidentSurface<'chart>,
    source: ResidentPhaseCurrentView<'source, 'chart>,
    response: ResidentPhaseEnclosureView<'response, 'chart>,
    target_receiver: PhaseCurrentReceiverId,
    target_lineage: PhaseCurrentLineageId,
) -> Result<ResidentEnclosedPhaseConvolution<'source, 'response, 'chart>, ResidentPhaseCurrentError>
{
    if source.sample_step() != response.sample_step()
        || source.phase_extent() != response.phase_extent()
    {
        return Err(PhaseCurrentError::ChartMismatch.into());
    }
    surface.validate_constitutive_current_view(source.current)?;
    let output_extent = source
        .raw_extent()
        .checked_add(response.raw_extent())
        .and_then(|n| n.checked_sub(1))
        .ok_or(PhaseCurrentError::CarrierOverflow)?;
    let output = surface.fresh_section(1, output_width(output_extent)?, ResidentGrain(0))?;
    let workspace_words = 4usize
        .checked_mul(source.raw_extent())
        .and_then(|n| n.checked_add(output_extent))
        .and_then(|n| n.checked_add(4))
        .and_then(ResidentSurface::constitutive_wide_workspace_words)
        .ok_or(PhaseCurrentError::CarrierOverflow)?;
    let workspace = surface.fresh_section(1, workspace_words, ResidentGrain(0))?;
    let mut passage = surface.begin_passage(&[vec![]])?;
    {
        let lane = passage.open(0, &[])?;
        surface.record_phase_enclosed_convolution(
            &lane,
            source.current,
            source.raw_extent(),
            response.section,
            response.wide_offset,
            response.raw_extent,
            response.grain,
            &workspace,
            &output,
        )?;
    }
    passage.close(0, &output, 64)?;
    let receipt = passage.finish()?.launch()?;
    if !receipt.obstruction.is_empty() {
        return Err(ConstitutiveFibreError::Arithmetic(format!(
            "enclosed phase convolution: {:?}",
            receipt.obstruction
        ))
        .into());
    }
    Ok(ResidentEnclosedPhaseConvolution {
        source,
        response,
        output,
        target_receiver,
        target_lineage,
    })
}

pub fn compare_enclosed_resident<'predicted, 'observed, 'chart>(
    surface: &'chart ResidentSurface<'chart>,
    predicted: ResidentPhaseEnclosureView<'predicted, 'chart>,
    observed: ResidentPhaseCurrentView<'observed, 'chart>,
    lineage: PhaseCurrentLineageId,
) -> Result<ResidentEnclosedPhaseDifference<'predicted, 'observed, 'chart>, ResidentPhaseCurrentError>
{
    let support = super::difference::comparison_support(
        predicted.receiver,
        &predicted.origin,
        &predicted.sample_step,
        predicted.phase_extent,
        predicted.raw_extent,
        observed.receiver,
        observed.origin(),
        observed.sample_step(),
        observed.phase_extent(),
        observed.raw_extent(),
    )?;
    surface.validate_constitutive_current_view(observed.current)?;
    let length = support.predicted.len();
    let output = surface.fresh_section(1, output_width(length)?, ResidentGrain(0))?;
    let workspace_words = length
        .checked_mul(2)
        .and_then(|n| n.checked_add(2))
        .and_then(ResidentSurface::constitutive_wide_workspace_words)
        .ok_or(PhaseCurrentError::CarrierOverflow)?;
    let workspace = surface.fresh_section(1, workspace_words, ResidentGrain(0))?;
    let mut passage = surface.begin_passage(&[vec![]])?;
    {
        let lane = passage.open(0, &[])?;
        surface.record_phase_enclosed_difference(
            &lane,
            predicted.section,
            predicted.wide_offset,
            predicted.raw_extent,
            observed.current,
            observed.raw_extent(),
            support.predicted.start,
            support.observed.start,
            length,
            predicted.grain,
            &workspace,
            &output,
        )?;
    }
    passage.close(0, &output, 64)?;
    let receipt = passage.finish()?.launch()?;
    if !receipt.obstruction.is_empty() {
        return Err(ConstitutiveFibreError::Arithmetic(format!(
            "enclosed phase difference: {:?}",
            receipt.obstruction
        ))
        .into());
    }
    Ok(ResidentEnclosedPhaseDifference {
        predicted,
        observed,
        support,
        output,
        lineage,
    })
}

#[cfg(test)]
mod tests;
