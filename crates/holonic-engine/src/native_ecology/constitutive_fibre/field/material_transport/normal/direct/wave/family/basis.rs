//! A projected unit-basis action from a complete anchored family. The original family is
//! retained; its receiver witness is not converted to a point-current learning operand.
use super::super::*;

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct FamilyBasisSelection {
    pub selected: usize,
    pub selected_coordinate: usize,
    pub projected_score: Rat,
    pub projected_ties: usize,
}
#[derive(Debug, Serialize)]
pub struct FamilyBasisReading {
    pub epoch: u64,
    pub selection: FamilyBasisSelection,
    pub coordinates: Vec<usize>,
    pub projected_scores: Vec<Rat>,
    /// These flags witness unbounded variation at fixed anchor. False does not establish
    /// constancy over the anchor ball, or a robust winning symbol for the whole family.
    pub anchor_independent_free: Vec<bool>,
}
pub struct NormalFamilyBasisFace<'c> {
    family: Rc<NormalWaveFamily<'c>>,
    epoch: u64,
    coordinates: Vec<usize>,
    _basis: Rc<ResidentSection<'c>>,
    _receiver: ResidentSection<'c>,
    scores: ResidentSection<'c>,
    selection: ResidentSection<'c>,
}
impl<'c> NormalFamilyBasisFace<'c> {
    pub fn source(&self) -> &NormalWaveFamily<'c> {
        &self.family
    }
    pub fn epoch(&self) -> u64 {
        self.epoch
    }
    pub fn basis_coordinates(&self) -> &[usize] {
        &self.coordinates
    }
    pub fn selection(&self) -> Result<FamilyBasisSelection, ConstitutiveFibreError> {
        let s = self.family.origin().fibre().surface;
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
        let v = wides(
            &self
                .family
                .origin()
                .fibre()
                .surface
                .read_out(&self.scores)?,
        )?;
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
        let scores = s.fresh_section(1, 2 * (2 * n + 1), ResidentGrain(0))?;
        let selection = s.fresh_section(1, 8, ResidentGrain(0))?;
        let mut p = s.begin_passage(&[vec![]])?;
        {
            let lane = p.open(0, &[])?;
            s.record_family_basis_face(
                &lane,
                &receiver,
                &self.permutation,
                n,
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
        Ok(NormalFamilyBasisFace {
            family,
            epoch,
            coordinates: self.coordinates.clone(),
            _basis: Rc::clone(&self.permutation),
            _receiver: receiver,
            scores,
            selection,
        })
    }
}
