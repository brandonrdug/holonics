//! The common normalized receiver applied to this already-owned producing comparison.
//! The source adapter adds c to the pre-fit increment; it defines no new return/report types.
use super::*;
use crate::{
    native_ecology::constitutive_fibre::NativeNormalizedMaterialReturn,
    resident_section::SeriesAperture,
};

impl<'c> NormalWaveReception<'c> {
    pub fn normalized_return(
        &self,
        group_width: usize,
        terms: SeriesAperture,
    ) -> Result<
        NativeNormalizedMaterialReturn<'c, u64, NormalWaveTransport, &Self>,
        ConstitutiveFibreError,
    > {
        let fibre = &self.predecessor_fibre;
        let n = fibre.roots;
        if group_width == 0 || n % group_width != 0 || terms.0 == 0 || terms.0 == u32::MAX {
            return Err(ConstitutiveFibreError::Shape);
        }
        let s = fibre.surface;
        let output = Rc::new(s.fresh_section(
            1,
            n.checked_mul(20).ok_or(ConstitutiveFibreError::Shape)?,
            ResidentGrain(0),
        )?);
        let scratch = s.fresh_section(
            1,
            n.checked_mul(4)
                .and_then(|n| n.checked_add(2))
                .ok_or(ConstitutiveFibreError::Shape)?,
            ResidentGrain(0),
        )?;
        let layout = NormalLayout::new(n, n).ok_or(ConstitutiveFibreError::Shape)?;
        let mut passage = s.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            s.record_normalized_sum_receiver(
                &lane,
                &self.source_joint,
                2 * n,
                &self.report,
                layout.ball_at(ReportBall::ContemporarySource),
                &self.current.inner.section,
                n,
                group_width,
                fibre.grain.0,
                terms,
                &scratch,
                &output,
            )?;
        }
        passage.close(0, &output, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "next-current probability receiver: {:?}",
                receipt.obstruction
            )));
        }
        Ok(NativeNormalizedMaterialReturn::from_resident(
            s,
            output,
            self,
            fibre.epoch,
            self.successor_fibre.epoch,
            group_width,
            fibre.grain.0,
            terms.0,
            n,
            fibre.transport,
        ))
    }
}
