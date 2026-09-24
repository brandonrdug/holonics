//! A projected unit-basis action from a complete anchored family. The original family is
//! retained; its receiver witness is not converted to a point-current learning operand.
use super::super::*;

pub struct NormalFamilyBasisFace<'c, Origin = (Rc<NormalWaveFamily<'c>>, ResidentSection<'c>)> {
    origin: Origin,
    surface: &'c ResidentSurface<'c>,
    epoch: u64,
    coordinates: Vec<usize>,
    _basis: Rc<ResidentSection<'c>>,
    scores: ResidentSection<'c>,
    selection: ResidentSection<'c>,
}
impl<'c> NormalFamilyBasisFace<'c> {
    pub fn source(&self) -> &NormalWaveFamily<'c> {
        &self.origin.0
    }
}
impl<'a, 'r, 'c> NormalFamilyBasisFace<'c, &'a NormalWaveFamilyReceiver<'r, 'c>> {
    pub fn source(&self) -> &NormalWaveFamilyReceiver<'r, 'c> {
        self.origin
    }
}
impl<'c, Origin> NormalFamilyBasisFace<'c, Origin> {
    pub fn epoch(&self) -> u64 {
        self.epoch
    }
    pub fn basis_coordinates(&self) -> &[usize] {
        &self.coordinates
    }
    pub fn selection(&self) -> Result<FamilyBasisSelection, ConstitutiveFibreError> {
        let s = self.surface;
        let v = wides(&s.read_out(&self.selection)?)?;
        if v.len() != 4
            || v[0] < 0
            || v[0] >= self.coordinates.len() as i128
            || v[2] <= 0
            || v[3] < 1
            || v[3] > self.coordinates.len() as i128
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let selected = usize::try_from(v[0]).map_err(invalid)?;
        Ok(FamilyBasisSelection {
            selected,
            selected_coordinate: self.coordinates[selected],
            projected_score: Rat::new(v[1].into(), v[2].into()),
            projected_ties: usize::try_from(v[3]).map_err(invalid)?,
        })
    }
    pub fn inspect(&self) -> Result<FamilyBasisReading, ConstitutiveFibreError> {
        let selection = self.selection()?;
        let v = wides(&self.surface.read_out(&self.scores)?)?;
        let n = self.coordinates.len();
        if v.len() != 2 * n + 1 || v[n] <= 0 || v[n + 1..].iter().any(|v| !matches!(*v, 0 | 1)) {
            return Err(ConstitutiveFibreError::Shape);
        }
        Ok(FamilyBasisReading {
            epoch: self.epoch,
            selection,
            coordinates: self.coordinates.clone(),
            projected_scores: v[..n]
                .iter()
                .map(|x| Rat::new((*x).into(), v[n].into()))
                .collect(),
            anchor_independent_free: v[n + 1..].iter().map(|v| *v != 0).collect(),
        })
    }
}

impl<'c> NormalWaveBasisChart<'c> {
    pub(in super::super) fn read_family(
        &self,
        family: Rc<NormalWaveFamily<'c>>,
        epoch: u64,
    ) -> Result<NormalFamilyBasisFace<'c>, ConstitutiveFibreError> {
        let s = family.origin().fibre().surface;
        let n = self.coordinates.len();
        if !std::ptr::eq(s, self.surface) || family.origin().fibre().roots != n {
            return Err(ConstitutiveFibreError::Shape);
        }
        let receiver = family.read_receiver()?.into_report();
        let (scores, selection) = self.project_family(&receiver, 4 * n, 2 * n)?;
        Ok(NormalFamilyBasisFace {
            origin: (family, receiver),
            surface: s,
            epoch,
            coordinates: self.coordinates.clone(),
            _basis: Rc::clone(&self.permutation),
            scores,
            selection,
        })
    }
    fn project_family(
        &self,
        receiver: &ResidentSection<'c>,
        outputs: usize,
        current_at: usize,
    ) -> Result<(ResidentSection<'c>, ResidentSection<'c>), ConstitutiveFibreError> {
        let s = self.surface;
        let n = self.coordinates.len();
        let scores = s.fresh_section(1, 2 * (2 * n + 1), ResidentGrain(0))?;
        let selection = s.fresh_section(1, 8, ResidentGrain(0))?;
        let mut p = s.begin_passage(&[vec![]])?;
        {
            let lane = p.open(0, &[])?;
            s.record_family_basis_face(
                &lane,
                receiver,
                &self.permutation,
                n,
                outputs,
                current_at,
                &scores,
                &selection,
            )?;
        }
        p.close(0, &selection, 64)?;
        let receipt = p.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "family basis receiver: {:?}",
                receipt.obstruction
            )));
        }
        Ok((scores, selection))
    }
}

impl<'r, 'c> NormalWaveFamilyReceiver<'r, 'c> {
    /// Every requested frame reads the SAME joint projection. This preserves its source
    /// across decoding; it does not select a new marginal/source independently per symbol.
    pub fn read_basis<'a>(
        &'a self,
        chart: &NormalWaveBasisChart<'c>,
        state: usize,
        epoch: u64,
    ) -> Result<NormalFamilyBasisFace<'c, &'a Self>, ConstitutiveFibreError> {
        let n = chart.coordinates.len();
        if !std::ptr::eq(chart.surface, self.source().origin().fibre().surface)
            || n != self.source().origin().fibre().roots
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let t = 2 + 8 * n;
        let width = self.target_width();
        if width % t != 0 || state >= width / t {
            return Err(ConstitutiveFibreError::Shape);
        }
        let current_at = state
            .checked_mul(t)
            .and_then(|v| v.checked_add(2 * n))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let (scores, selection) =
            chart.project_family(self.report(), width - 2 - 4 * n, current_at)?;
        Ok(NormalFamilyBasisFace {
            origin: self,
            surface: chart.surface,
            epoch,
            coordinates: chart.coordinates.clone(),
            _basis: Rc::clone(&chart.permutation),
            scores,
            selection,
        })
    }
}
