//! The oriented return at one temporal receiver. Comparing a prediction with an observation
//! supplies evidence; it neither installs a condition nor asserts an exact constitutive fit.
use super::*;
use num_traits::ToPrimitive;
use serde::{Deserialize, Serialize};
use std::ops::Range;

/// Exact overlap and the portions excluded from this comparison. Excluded coefficients are
/// retained in the operand carriers; lack of an observation never supplies a zero target.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct PhaseComparisonSupport {
    pub predicted: Range<usize>,
    pub observed: Range<usize>,
    pub unobserved_prediction: Vec<Range<usize>>,
    pub unpredicted_observation: Vec<Range<usize>>,
    pub begin: Rat,
    pub end: Rat,
}

/// Both complete operands remain borrowed alongside `observed - predicted`. Keeping this
/// difference before scalar measurement preserves its orientation and both quadratures.
pub struct ResidentPhaseDifference<'source, 'chart> {
    predicted: ResidentPhaseCurrentView<'source, 'chart>,
    observed: ResidentPhaseCurrentView<'source, 'chart>,
    support: PhaseComparisonSupport,
    output: ResidentSection<'chart>,
    lineage: PhaseCurrentLineageId,
}

fn outside(range: &Range<usize>, extent: usize) -> Vec<Range<usize>> {
    let mut result = Vec::with_capacity(2);
    if range.start > 0 {
        result.push(0..range.start);
    }
    if range.end < extent {
        result.push(range.end..extent);
    }
    result
}

fn support(
    predicted: &ResidentPhaseCurrentView<'_, '_>,
    observed: &ResidentPhaseCurrentView<'_, '_>,
) -> Result<PhaseComparisonSupport, ResidentPhaseCurrentError> {
    comparison_support(
        predicted.receiver,
        &predicted.origin,
        &predicted.sample_step,
        predicted.phase_extent,
        predicted.raw_extent,
        observed.receiver,
        &observed.origin,
        &observed.sample_step,
        observed.phase_extent,
        observed.raw_extent,
    )
}

/// One clock/support relation shared by point and enclosed temporal receivers.
#[allow(clippy::too_many_arguments)]
pub fn comparison_support(
    predicted_receiver: PhaseCurrentReceiverId,
    predicted_origin: &Rat,
    predicted_step: &Rat,
    predicted_phase: u32,
    predicted_raw: usize,
    observed_receiver: PhaseCurrentReceiverId,
    observed_origin: &Rat,
    observed_step: &Rat,
    observed_phase: u32,
    observed_raw: usize,
) -> Result<PhaseComparisonSupport, ResidentPhaseCurrentError> {
    if predicted_step <= &Rat::from_integer(0.into())
        || predicted_phase == 0
        || predicted_raw == 0
        || observed_raw == 0
        || predicted_step != observed_step
        || predicted_phase != observed_phase
        || predicted_receiver != observed_receiver
    {
        return Err(PhaseCurrentError::ChartMismatch.into());
    }
    let begin = predicted_origin.clone().max(observed_origin.clone());
    let offset = |origin: &Rat| -> Result<usize, ResidentPhaseCurrentError> {
        let cells = (&begin - origin) / predicted_step;
        if !cells.is_integer() {
            return Err(ResidentPhaseCurrentError::UnalignedSupport);
        }
        cells
            .to_integer()
            .to_usize()
            .ok_or(ResidentPhaseCurrentError::NonOverlappingSupport)
    };
    let p = offset(predicted_origin)?;
    let o = offset(observed_origin)?;
    let extent = predicted_raw
        .checked_sub(p)
        .zip(observed_raw.checked_sub(o))
        .map(|(a, b)| a.min(b))
        .filter(|extent| *extent > 0)
        .ok_or(ResidentPhaseCurrentError::NonOverlappingSupport)?;
    let predicted_range = p..p + extent;
    let observed_range = o..o + extent;
    Ok(PhaseComparisonSupport {
        unobserved_prediction: outside(&predicted_range, predicted_raw),
        unpredicted_observation: outside(&observed_range, observed_raw),
        predicted: predicted_range,
        observed: observed_range,
        end: &begin + predicted_step * Rat::from_integer(extent.into()),
        begin,
    })
}

/// Compare at an explicitly shared receiver and exact clock. Origins may differ by an integral
/// number of samples; no interpolation, delay estimation, resampling or exterior zero extension
/// is performed. All numerical subtraction and normalization run in one resident passage.
pub fn compare_resident<'source, 'chart>(
    surface: &'chart ResidentSurface<'chart>,
    predicted: ResidentPhaseCurrentView<'source, 'chart>,
    observed: ResidentPhaseCurrentView<'source, 'chart>,
    lineage: PhaseCurrentLineageId,
) -> Result<ResidentPhaseDifference<'source, 'chart>, ResidentPhaseCurrentError> {
    let support = support(&predicted, &observed)?;
    surface.validate_constitutive_current_view(predicted.current)?;
    surface.validate_constitutive_current_view(observed.current)?;
    let extent = support.predicted.len();
    let width = extent
        .checked_mul(2)
        .filter(|n| *n < u32::MAX as usize)
        .ok_or(PhaseCurrentError::CarrierOverflow)?;
    let workspace_words = width
        .checked_add(4)
        .and_then(ResidentSurface::constitutive_wide_workspace_words)
        .ok_or(PhaseCurrentError::CarrierOverflow)?;
    let workspace = surface.fresh_section(1, workspace_words, ResidentGrain(0))?;
    let output = surface.fresh_section(1, width + 1, ResidentGrain(0))?;
    let mut passage = surface.begin_passage(&[vec![]])?;
    {
        let lane = passage.open(0, &[])?;
        surface.record_phase_difference(
            &lane,
            predicted.current,
            observed.current,
            predicted.raw_extent,
            observed.raw_extent,
            support.predicted.start,
            support.observed.start,
            extent,
            &workspace,
            &output,
        )?;
    }
    passage.close(0, &output, 64)?;
    let receipt = passage.finish()?.launch()?;
    if !receipt.obstruction.is_empty() {
        return Err(ConstitutiveFibreError::Arithmetic(format!(
            "phase difference: {:?}",
            receipt.obstruction
        ))
        .into());
    }
    Ok(ResidentPhaseDifference {
        predicted,
        observed,
        support,
        output,
        lineage,
    })
}

impl<'source, 'chart> ResidentPhaseDifference<'source, 'chart> {
    pub fn predicted(&self) -> &ResidentPhaseCurrentView<'source, 'chart> {
        &self.predicted
    }
    pub fn observed(&self) -> &ResidentPhaseCurrentView<'source, 'chart> {
        &self.observed
    }
    pub fn support(&self) -> &PhaseComparisonSupport {
        &self.support
    }
    pub fn section(&self) -> &ResidentSection<'chart> {
        &self.output
    }
    pub fn current(
        &self,
    ) -> Result<ResidentConstitutiveCurrent<'_, 'chart>, ConstitutiveFibreError> {
        ResidentConstitutiveCurrent::rational(&self.output)
    }
    pub fn view(&self) -> Result<ResidentPhaseCurrentView<'_, 'chart>, ResidentPhaseCurrentError> {
        ResidentPhaseCurrentView::new(
            self.current()?,
            self.predicted.receiver,
            self.lineage,
            self.support.begin.clone(),
            self.predicted.sample_step.clone(),
            self.predicted.phase_extent,
            self.support.predicted.len(),
        )
    }
}

#[cfg(test)]
mod tests;
