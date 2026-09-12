use super::*;
mod rest;
mod source;
mod observation;
mod pullback;
pub use pullback::ResidentWavePullback;
pub use rest::NormalWaveRelationRest;
pub use source::ResidentWaveSourceContact;

/// The receiver chart in which the local law was founded. UnitRealSum is a mean-offset
/// section for a maximum/softmax receiver; actual source offsets stay in the lifted state.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, serde::Deserialize)]
pub enum WaveSourceReceiver {
    #[default]
    Direct,
    UnitRealSum,
}

/// Immutable conditional pullback or source-contact map in the wave family chart.
/// The basis is a derived relation; it owns no learned material and no continuing ecology.
pub struct ResidentWaveRelation<'c> {
    pub(in super::super) surface: &'c ResidentSurface<'c>,
    pub(in super::super) basis: ResidentSection<'c>,
    pub(in super::super) fixed: Rc<ResidentSection<'c>>,
    pub(in super::super) roots: usize,
    pub(in super::super) condition_complex: usize,
    pub(in super::super) relation_cut: u64,
    producing_owner: Rc<()>,
    receiver: WaveSourceReceiver,
    source: Option<ResidentWaveSourceContact<'c>>,
    observation: Option<ResidentSection<'c>>,
    source_geometry: Rc<std::cell::OnceCell<super::condition_contact::ResidentWaveSourceGeometry<'c>>>,
}
impl<'c> ResidentWaveRelation<'c> {
    pub(in super::super) fn new(
        surface: &'c ResidentSurface<'c>,
        basis: ResidentSection<'c>,
        fixed: ResidentSection<'c>,
        roots: usize,
        condition_complex: usize,
        relation_cut: u64,
        producing_owner: Rc<()>,
        receiver: WaveSourceReceiver,
    ) -> Self {
        Self {
            surface,
            basis,
            fixed: Rc::new(fixed),
            roots,
            condition_complex,
            relation_cut,
            producing_owner,
            receiver,
            source: None,
            observation: None,
            source_geometry: Rc::new(std::cell::OnceCell::new()),
        }
    }
    pub fn source_receiver(&self) -> WaveSourceReceiver {
        self.receiver
    }
    pub fn width(&self) -> usize {
        2 + 8 * self.roots
    }
    pub fn relation_cut(&self) -> u64 {
        self.relation_cut
    }
    pub fn roots(&self) -> usize {
        self.roots
    }
    pub fn fixed_condition(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        ResidentConstitutiveCurrent::rational(&self.fixed)
            .expect("completed fixed-condition snapshot")
    }
    pub fn condition_complex(&self) -> usize {
        self.condition_complex
    }
    pub fn same_producing_cut(&self, other: &Self) -> bool {
        Rc::ptr_eq(&self.producing_owner, &other.producing_owner)
            && self.relation_cut == other.relation_cut
    }
}

impl<'chart> ResidentConstitutiveFibre<'chart> {
    pub fn read_wave_relation(
        &self,
        condition: ResidentConstitutiveCurrent<'_, 'chart>,
        roots: usize,
    ) -> Result<ResidentWaveRelation<'chart>, ConstitutiveFibreError> {
        self.read_wave_relation_in_chart(condition, roots, WaveSourceReceiver::Direct)
    }
    pub fn read_wave_relation_in_chart(
        &self,
        condition: ResidentConstitutiveCurrent<'_, 'chart>,
        roots: usize,
        receiver: WaveSourceReceiver,
    ) -> Result<ResidentWaveRelation<'chart>, ConstitutiveFibreError> {
        if !self.usable {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        ResidentWaveRelation::derive(
            self.surface,
            &self.basis,
            self.source_chart,
            self.target_width,
            self.occurrences,
            Rc::clone(&self.basis_owner),
            condition,
            roots,
            receiver,
        )
    }
}
impl<'chart> PreparedConstitutiveFormation<'chart> {
    pub(crate) fn read_wave_relation(
        &self,
        condition: ResidentConstitutiveCurrent<'_, 'chart>,
        roots: usize,
        receiver: WaveSourceReceiver,
    ) -> Result<ResidentWaveRelation<'chart>, ConstitutiveFibreError> {
        ResidentWaveRelation::derive(
            self.returned.surface,
            &self.basis,
            self.returned.source_chart,
            self.returned.target_width,
            self.returned.occurrence,
            Rc::clone(&self.successor_owner),
            condition,
            roots,
            receiver,
        )
    }
}
impl<'chart> ResidentWaveRelation<'chart> {
    #[allow(clippy::too_many_arguments)]
    fn derive(
        surface: &'chart ResidentSurface<'chart>,
        basis: &ResidentSection<'chart>,
        source_chart: ConstitutiveSourceChart,
        target_width: usize,
        occurrence: u64,
        producing_owner: Rc<()>,
        condition: ResidentConstitutiveCurrent<'_, 'chart>,
        roots: usize,
        receiver: WaveSourceReceiver,
    ) -> Result<Self, ConstitutiveFibreError> {
        let ConstitutiveSourceChart::BilinearContact {
            source_complex,
            condition_complex,
        } = source_chart
        else {
            return Err(ConstitutiveFibreError::Shape);
        };
        if roots == 0
            || roots.checked_mul(3) != Some(source_complex)
            || roots.checked_mul(2) != Some(target_width)
            || condition_complex.checked_mul(2) != Some(condition.width)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let ns = roots.checked_mul(3).ok_or(ConstitutiveFibreError::Shape)?;
        let q = roots
            .checked_mul(8)
            .and_then(|v| v.checked_add(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let u = roots
            .checked_mul(10)
            .and_then(|v| v.checked_add(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let feature = ns
            .checked_mul(condition_complex)
            .and_then(|v| {
                v.checked_add(ns)?
                    .checked_add(condition_complex)?
                    .checked_mul(2)
            })
            .ok_or(ConstitutiveFibreError::Shape)?;
        let l = roots
            .checked_mul(2)
            .and_then(|v| v.checked_add(feature))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let relation = l.checked_add(u).ok_or(ConstitutiveFibreError::Shape)?;
        let d = q.checked_mul(2).ok_or(ConstitutiveFibreError::Shape)?;
        relation
            .checked_mul(relation)
            .and_then(|_| d.checked_mul(d))
            .ok_or(ConstitutiveFibreError::Shape)?;
        if relation > u32::MAX as usize || d > u32::MAX as usize {
            return Err(ConstitutiveFibreError::Shape);
        }
        let graph = surface.fresh_section(relation, relation, ResidentGrain(0))?;
        let derived = surface.fresh_section(2 * q, 2 * q, ResidentGrain(0))?;
        let fixed = surface.fresh_section(1, 2 * condition_complex + 1, ResidentGrain(0))?;
        let words = l
            .checked_add(relation.max(d))
            .and_then(|v| v.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let workspace = surface.fresh_section(1, words, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_constitutive_wave_relation(
                &lane,
                basis,
                condition,
                roots,
                condition_complex,
                &graph,
                &derived,
                &fixed,
                &workspace,
                receiver,
            )?;
        }
        passage.close(0, &derived, i64::BITS)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "wave relation: {:?}",
                receipt.obstruction
            )));
        }
        Ok(ResidentWaveRelation::new(
            surface,
            derived,
            fixed,
            roots,
            condition_complex,
            occurrence,
            producing_owner,
            receiver,
        ))
    }
}
