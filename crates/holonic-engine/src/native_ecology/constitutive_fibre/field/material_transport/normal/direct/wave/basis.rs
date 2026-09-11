use super::*;

/// A declared ordering of the unit complex coordinate basis. Addresses belong to this receiver
/// chart, not to semantic classes or native incidence. The first chart supports permutations;
/// an arbitrary change of phase/basis requires its actual additional projection map.
pub struct NormalWaveBasisChart<'c> {
    pub(super) surface: &'c ResidentSurface<'c>,
    pub(super) permutation: Rc<ResidentSection<'c>>,
    pub(super) coordinates: Vec<usize>,
}
impl<'c> NormalWaveBasisChart<'c> {
    pub fn identity(
        surface: &'c ResidentSurface<'c>,
        count: usize,
    ) -> Result<Self, ConstitutiveFibreError> {
        if count == 0
            || count
                .checked_mul(4)
                .and_then(|v| v.checked_add(2))
                .is_none_or(|v| v > u32::MAX as usize)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let mut coordinates = Vec::new();
        coordinates.try_reserve_exact(count).map_err(invalid)?;
        coordinates.extend(0..count);
        Self::from_permutation(surface, &coordinates)
    }
    pub fn from_permutation(
        surface: &'c ResidentSurface<'c>,
        coordinates: &[usize],
    ) -> Result<Self, ConstitutiveFibreError> {
        if coordinates.is_empty()
            || coordinates
                .len()
                .checked_mul(4)
                .and_then(|v| v.checked_add(2))
                .is_none_or(|v| v > u32::MAX as usize)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let mut sorted = coordinates.to_vec();
        sorted.sort_unstable();
        if !sorted.iter().copied().eq(0..coordinates.len()) {
            return Err(ConstitutiveFibreError::Shape);
        }
        let words = coordinates.iter().map(|v| (*v as i64, *v as i64)).collect();
        let rest = ResidentSectionRest::found(1, coordinates.len(), ResidentGrain(0), 64, words)
            .map_err(invalid)?;
        Ok(Self {
            surface,
            permutation: Rc::new(surface.mount_section_rest(&rest)?),
            coordinates: coordinates.to_vec(),
        })
    }
    pub fn coordinates(&self) -> &[usize] {
        &self.coordinates
    }
}

/// The projected action and all coordinate bounds retain one shared source family. Bounds are
/// not independent coordinate choices, and selecting one action does not replace that family.
pub struct NormalWaveBasisFace<'c> {
    current: NormalWaveCurrent<'c>,
    fibre: NormalWaveFibre<'c>,
    _permutation: Rc<ResidentSection<'c>>,
    coordinates: Vec<usize>,
    scores: ResidentSection<'c>,
    report: ResidentSection<'c>,
}
#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct NormalBasisSelection {
    pub selected: usize,
    pub selected_coordinate: usize,
    pub centre_score: Rat,
    pub centre_ties: usize,
    pub score_radius: Rat,
    /// Strict interval separation for this finite receiver; never source uniqueness.
    pub robust: bool,
}
#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct NormalBasisScore {
    pub centre: Rat,
    pub lower: Rat,
    pub upper: Rat,
}
#[derive(Debug, Serialize)]
pub struct NormalWaveBasisReading {
    pub epoch: Option<u64>,
    pub transport: NormalWaveTransport,
    pub coordinates: Vec<usize>,
    pub selection: NormalBasisSelection,
    pub scores: Vec<NormalBasisScore>,
}
impl<'c> NormalWaveBasisFace<'c> {
    pub fn source(&self) -> &NormalWaveCurrent<'c> {
        &self.current
    }
    pub fn source_fibre(&self) -> &NormalWaveFibre<'c> {
        &self.fibre
    }
    pub fn basis_coordinates(&self) -> &[usize] {
        &self.coordinates
    }
    /// Only the already-selected native face crosses here. The host never ranks scores.
    pub fn selection(&self) -> Result<NormalBasisSelection, ConstitutiveFibreError> {
        let values = wides(&self.fibre.surface.read_out(&self.report)?)?;
        if values.len() != 5
            || values[4] < 0
            || values[0] < 0
            || values[2] < 1
            || !(0..=1).contains(&values[3])
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let selected = usize::try_from(values[0]).map_err(invalid)?;
        let ties = usize::try_from(values[2]).map_err(invalid)?;
        if selected >= self.coordinates.len() || ties > self.coordinates.len() {
            return Err(ConstitutiveFibreError::Shape);
        }
        Ok(NormalBasisSelection {
            selected,
            selected_coordinate: self.coordinates[selected],
            centre_score: Rat::new(values[1].into(), BigInt::one() << self.fibre.grain.0),
            score_radius: Rat::new(values[4].into(), BigInt::one() << self.fibre.grain.0),
            centre_ties: ties,
            robust: values[3] == 1,
        })
    }
    pub fn inspect(&self) -> Result<NormalWaveBasisReading, ConstitutiveFibreError> {
        let selection = self.selection()?;
        let values = wides(&self.fibre.surface.read_out(&self.scores)?)?;
        if values.len() != self.coordinates.len() {
            return Err(ConstitutiveFibreError::Shape);
        }
        let scale = BigInt::one() << self.fibre.grain.0;
        let scores = values
            .iter()
            .map(|v| {
                let centre = Rat::new((*v).into(), scale.clone());
                NormalBasisScore {
                    lower: &centre - &selection.score_radius,
                    upper: &centre + &selection.score_radius,
                    centre,
                }
            })
            .collect();
        Ok(NormalWaveBasisReading {
            epoch: self.current.at(),
            transport: self.fibre.transport,
            coordinates: self.coordinates.clone(),
            selection,
            scores,
        })
    }
}
fn read_basis_face<'c>(
    current: NormalWaveCurrent<'c>,
    fibre: NormalWaveFibre<'c>,
    chart: &NormalWaveBasisChart<'c>,
) -> Result<NormalWaveBasisFace<'c>, ConstitutiveFibreError> {
    let s = fibre.surface;
    let n = chart.coordinates.len();
    if !std::ptr::eq(chart.surface, s) || current.width != 2 * n || fibre.roots != n {
        return Err(ConstitutiveFibreError::Shape);
    }
    let scores = s.fresh_section(1, 2 * n, ResidentGrain(0))?;
    let report = s.fresh_section(1, 10, ResidentGrain(0))?;
    let mut passage = s.begin_passage(&[vec![]])?;
    {
        let lane = passage.open(0, &[])?;
        s.record_normal_wave_basis_face(
            &lane,
            current.view(),
            &chart.permutation,
            n,
            fibre.grain.0,
            &scores,
            &report,
        )?;
    }
    passage.close(0, &report, 64)?;
    let returned = passage.finish()?.launch()?;
    if !returned.obstruction.is_empty() {
        return Err(ConstitutiveFibreError::Arithmetic(format!(
            "wave basis receiver: {:?}",
            returned.obstruction
        )));
    }
    Ok(NormalWaveBasisFace {
        current,
        fibre,
        _permutation: Rc::clone(&chart.permutation),
        coordinates: chart.coordinates.clone(),
        scores,
        report,
    })
}
impl<'c> NormalWaveStep<'c> {
    pub fn read_basis_face(
        &self,
        chart: &NormalWaveBasisChart<'c>,
    ) -> Result<NormalWaveBasisFace<'c>, ConstitutiveFibreError> {
        read_basis_face(self.current.snapshot(), self.fibre.snapshot(), chart)
    }
}
impl<'c> ResidentNormalWave<'c> {
    /// Read the current receiver without advancing, developing or replacing any source.
    pub fn read_basis_face(
        &self,
        chart: &NormalWaveBasisChart<'c>,
    ) -> Result<NormalWaveBasisFace<'c>, ConstitutiveFibreError> {
        read_basis_face(self.current.snapshot(), self.fibre(), chart)
    }
}
