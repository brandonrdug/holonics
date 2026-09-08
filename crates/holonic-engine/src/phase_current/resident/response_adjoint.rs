//! Return through the source carrier that produced a retained temporal prediction. The
//! receiver is restricted to observed support before taking its response adjoint.
use super::*;

/// The response leg of the actual forward operation's adjoint, with its complete prediction
/// and observed-minus-predicted return still borrowed. This does not develop a condition.
pub struct ResidentPhaseResponseAdjoint<'operation, 'source, 'observed, 'chart> {
    forward: &'operation ResidentPhaseConvolution<'source, 'chart>,
    difference: &'operation ResidentPhaseDifference<'observed, 'chart>,
    output: ResidentSection<'chart>,
    lineage: PhaseCurrentLineageId,
}

/// For the retained forward y=x*h and its comparison on S, return X_x* R_S* e in
/// h's original chart. R_S* is the dual of restriction: missing observations supply no
/// returned covector, rather than being asserted to have zero measured value.
/// All coefficients are computed on device, including zero response directions.
pub fn return_response_resident<'operation, 'source, 'observed, 'chart>(
    surface: &'chart ResidentSurface<'chart>,
    forward: &'operation ResidentPhaseConvolution<'source, 'chart>,
    difference: &'operation ResidentPhaseDifference<'observed, 'chart>,
    lineage: PhaseCurrentLineageId,
) -> Result<
    ResidentPhaseResponseAdjoint<'operation, 'source, 'observed, 'chart>,
    ResidentPhaseCurrentError,
> {
    let expected = forward.view()?;
    let actual = difference.predicted();
    let a = actual.current();
    let b = expected.current();
    // Equal values, labels, clocks or digests cannot stand in for the producing carrier.
    if !std::ptr::eq(a.section, b.section)
        || a.offset != b.offset
        || a.width != b.width
        || a.denominator != b.denominator
        || a.disposition != b.disposition
        || actual.receiver != expected.receiver
        || actual.lineage != expected.lineage
        || actual.origin != expected.origin
        || actual.sample_step != expected.sample_step
        || actual.phase_extent != expected.phase_extent
        || actual.raw_extent != expected.raw_extent
    {
        return Err(ResidentPhaseCurrentError::PredictionMismatch);
    }
    let source = forward.source();
    let residual = difference.current()?;
    surface.validate_constitutive_current_view(source.current())?;
    surface.validate_constitutive_current_view(residual)?;
    let response_extent = forward.response().raw_extent();
    let width = response_extent
        .checked_mul(2)
        .filter(|n| *n < u32::MAX as usize)
        .ok_or(PhaseCurrentError::CarrierOverflow)?;
    let workspace_words = width
        .checked_add(2)
        .and_then(ResidentSurface::constitutive_wide_workspace_words)
        .ok_or(PhaseCurrentError::CarrierOverflow)?;
    let workspace = surface.fresh_section(1, workspace_words, ResidentGrain(0))?;
    let output = surface.fresh_section(1, width + 1, ResidentGrain(0))?;
    let mut passage = surface.begin_passage(&[vec![]])?;
    {
        let lane = passage.open(0, &[])?;
        surface.record_phase_response_adjoint(
            &lane,
            source.current(),
            residual,
            source.raw_extent(),
            response_extent,
            difference.support().predicted.start,
            difference.support().predicted.len(),
            &workspace,
            &output,
        )?;
    }
    passage.close(0, &output, 64)?;
    let receipt = passage.finish()?.launch()?;
    if !receipt.obstruction.is_empty() {
        return Err(ConstitutiveFibreError::Arithmetic(format!(
            "phase response adjoint: {:?}",
            receipt.obstruction
        ))
        .into());
    }
    Ok(ResidentPhaseResponseAdjoint {
        forward,
        difference,
        output,
        lineage,
    })
}

impl<'operation, 'source, 'observed, 'chart>
    ResidentPhaseResponseAdjoint<'operation, 'source, 'observed, 'chart>
{
    pub fn forward(&self) -> &ResidentPhaseConvolution<'source, 'chart> {
        self.forward
    }
    pub fn difference(&self) -> &ResidentPhaseDifference<'observed, 'chart> {
        self.difference
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
        let response = self.forward.response();
        ResidentPhaseCurrentView::new(
            self.current()?,
            response.receiver(),
            self.lineage,
            response.origin().clone(),
            response.sample_step().clone(),
            response.phase_extent(),
            response.raw_extent(),
        )
    }
}

#[cfg(test)]
mod tests;
