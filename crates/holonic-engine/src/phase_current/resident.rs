//! Resident realization of the existing carried causal convolution. Temporal coordinates and
//! exact source carriers remain explicit; this operation supplies no acoustic classifier or
//! separate learning law.
use super::{PhaseCurrentError, PhaseCurrentLineageId, PhaseCurrentReceiverId};
use crate::{
    native_ecology::constitutive_fibre::{ConstitutiveFibreError, ResidentConstitutiveCurrent},
    resident_section::{ResidentGrain, ResidentRefusal, ResidentSection, ResidentSurface},
};
use num_rational::BigRational as Rat;
use num_traits::Signed;
use thiserror::Error;

#[derive(Debug, Error)]
pub enum ResidentPhaseCurrentError {
    #[error(transparent)]
    Chart(#[from] PhaseCurrentError),
    #[error(transparent)]
    Native(#[from] ConstitutiveFibreError),
    #[error("temporal observations have no common sampled support")]
    NonOverlappingSupport,
    #[error("temporal observation origins do not align on their shared sample clock")]
    UnalignedSupport,
    #[error("temporal return does not retain this operation's producing prediction")]
    PredictionMismatch,
}

mod difference;
pub use difference::{compare_resident, PhaseComparisonSupport, ResidentPhaseDifference};

mod response_adjoint;
pub use response_adjoint::{return_response_resident, ResidentPhaseResponseAdjoint};

impl From<ResidentRefusal> for ResidentPhaseCurrentError {
    fn from(value: ResidentRefusal) -> Self {
        Self::Native(value.into())
    }
}

/// Borrowed complex rational coefficients in an exact temporal chart. Extra coordinates are
/// declared structural padding and are checked to be zero on device before any product returns.
pub struct ResidentPhaseCurrentView<'source, 'chart> {
    current: ResidentConstitutiveCurrent<'source, 'chart>,
    receiver: PhaseCurrentReceiverId,
    lineage: PhaseCurrentLineageId,
    origin: Rat,
    sample_step: Rat,
    phase_extent: u32,
    raw_extent: usize,
}

impl<'source, 'chart> ResidentPhaseCurrentView<'source, 'chart> {
    #[allow(clippy::too_many_arguments)]
    pub fn new(
        current: ResidentConstitutiveCurrent<'source, 'chart>,
        receiver: PhaseCurrentReceiverId,
        lineage: PhaseCurrentLineageId,
        origin: Rat,
        sample_step: Rat,
        phase_extent: u32,
        raw_extent: usize,
    ) -> Result<Self, ResidentPhaseCurrentError> {
        if current.width % 2 != 0
            || raw_extent == 0
            || raw_extent > current.width / 2
            || phase_extent == 0
            || !sample_step.is_positive()
        {
            return Err(PhaseCurrentError::MalformedSection.into());
        }
        Ok(Self {
            current,
            receiver,
            lineage,
            origin,
            sample_step,
            phase_extent,
            raw_extent,
        })
    }

    pub fn current(&self) -> ResidentConstitutiveCurrent<'source, 'chart> {
        self.current
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
}

/// A returned temporal product with both complete operand carriers still borrowed. These
/// particular operands retain every mixed contribution; the summed output alone does not
/// identify its source or constitute the preimage of every possible operand pair.
pub struct ResidentPhaseConvolution<'source, 'chart> {
    source: ResidentPhaseCurrentView<'source, 'chart>,
    response: ResidentPhaseCurrentView<'source, 'chart>,
    output: ResidentSection<'chart>,
    target_receiver: PhaseCurrentReceiverId,
    target_lineage: PhaseCurrentLineageId,
}

impl<'source, 'chart> ResidentPhaseConvolution<'source, 'chart> {
    pub fn source(&self) -> &ResidentPhaseCurrentView<'source, 'chart> {
        &self.source
    }
    pub fn response(&self) -> &ResidentPhaseCurrentView<'source, 'chart> {
        &self.response
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
            self.target_receiver,
            self.target_lineage,
            &self.source.origin + &self.response.origin,
            self.source.sample_step.clone(),
            self.source.phase_extent,
            self.source.raw_extent + self.response.raw_extent - 1,
        )
    }
}

/// Apply the existing polynomial action with its complete causal carry. Both charts must share
/// the sample step and phase extent. The response origin is in its declared local chart; origins
/// add exactly as in the cold reference owner. This does not align arbitrary dialogue intervals.
pub fn convolve_resident<'source, 'chart>(
    surface: &'chart ResidentSurface<'chart>,
    source: ResidentPhaseCurrentView<'source, 'chart>,
    response: ResidentPhaseCurrentView<'source, 'chart>,
    target_receiver: PhaseCurrentReceiverId,
    target_lineage: PhaseCurrentLineageId,
) -> Result<ResidentPhaseConvolution<'source, 'chart>, ResidentPhaseCurrentError> {
    if source.sample_step != response.sample_step || source.phase_extent != response.phase_extent {
        return Err(PhaseCurrentError::ChartMismatch.into());
    }
    surface.validate_constitutive_current_view(source.current)?;
    surface.validate_constitutive_current_view(response.current)?;
    let width = source
        .raw_extent
        .checked_add(response.raw_extent)
        .and_then(|n| n.checked_sub(1))
        .and_then(|n| n.checked_mul(2))
        .filter(|n| *n < u32::MAX as usize)
        .ok_or(PhaseCurrentError::CarrierOverflow)?;
    let scratch = ResidentSurface::constitutive_wide_scratch(width)
        .ok_or(PhaseCurrentError::CarrierOverflow)?;
    let available = surface.declaration().max_sectiond_bytes;
    // Placement changes with the complete receiver extent, not with an authored semantic
    // grain. Large currents keep all coefficients in resident device workspace; dependent
    // commands normalize the same exact product before returning a public current.
    let workspace = if scratch > available as usize {
        let words = width
            .checked_add(2)
            .and_then(ResidentSurface::constitutive_wide_workspace_words)
            .ok_or(PhaseCurrentError::CarrierOverflow)?;
        Some(surface.fresh_section(1, words, ResidentGrain(0))?)
    } else {
        None
    };
    let output = surface.fresh_section(1, width + 1, ResidentGrain(0))?;
    let mut passage = surface.begin_passage(&[vec![]])?;
    {
        let lane = passage.open(0, &[])?;
        surface.record_phase_convolution(
            &lane,
            source.current,
            response.current,
            source.raw_extent,
            response.raw_extent,
            workspace.as_ref(),
            &output,
        )?;
    }
    passage.close(0, &output, 64)?;
    let receipt = passage.finish()?.launch()?;
    if !receipt.obstruction.is_empty() {
        return Err(ConstitutiveFibreError::Arithmetic(format!(
            "phase convolution: {:?}",
            receipt.obstruction
        ))
        .into());
    }
    Ok(ResidentPhaseConvolution {
        source,
        response,
        output,
        target_receiver,
        target_lineage,
    })
}

#[cfg(test)]
mod tests;
