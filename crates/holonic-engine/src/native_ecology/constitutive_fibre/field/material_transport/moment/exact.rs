//! Cold evaluation of the retained numerical generator; never called by native conduct.
use super::*;

pub(super) fn source_pair(
    a: &NativeCurrentHistorySourceReading,
    b: &NativeCurrentHistorySourceReading,
) -> Rat {
    let overlap = a.numerical_pairing(b);
    let homogeneous = overlap.add(&ExactComplexWaveCurrent::new(
        Rat::one(),
        Rat::from_integer(0.into()),
    ));
    homogeneous.norm_square()
        / ((Rat::one() + &a.numerical_norm_square) * (Rat::one() + &b.numerical_norm_square))
}
impl NativeConstitutiveField<'_> {
    /// Evaluate the exact rational numerical operator retained at `operator_at` on the
    /// numerical complete source at `source_at`. This is an exterior diagnostic, not a
    /// replacement for its resident evaluation or an assertion of an exact physical source.
    pub fn inspect_exact_numerical_moment_forward(
        &self,
        operator_at: usize,
        source_at: usize,
    ) -> Result<Option<Vec<ExactComplexWaveCurrent>>, ConstitutiveFibreError> {
        if self.material_transport_source()
            != Some(NativeMaterialTransportSource::HomogeneousMoment)
        {
            return Ok(None);
        }
        if operator_at >= self.history.len() || source_at >= self.history.len() {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        let source = self
            .inspect_moment_material_transport(source_at)?
            .ok_or_else(|| invalid("source absent"))?
            .source;
        let mut sum = vec![ExactComplexWaveCurrent::zero(); self.nodes()];
        for at in 0..=operator_at {
            if let Some(origin) = self.history[at].lineage.received_from {
                let factor = self
                    .inspect_moment_material_transport(at)?
                    .ok_or_else(|| invalid("factor absent"))?;
                let original = self
                    .inspect_moment_material_transport(origin)?
                    .ok_or_else(|| invalid("factor source absent"))?;
                let kernel = source_pair(&original.source, &source);
                for (sum, beta) in sum.iter_mut().zip(&factor.numerical_return_factor) {
                    *sum = sum.add(&beta.scaled(&kernel));
                }
            }
        }
        Ok(Some(sum))
    }
}
