//! An incoming point passage meets its complete learned arrival family before acting on
//! the held family. The reaction is an explicit constitutive operation, not a point cast.
//!
//! [definition] Retention (plan phase 11): a source map retains what its future reads — the
//! source operand (read again when a continuing family is rebound at remount), its field row and
//! the contact reaction whose successor generates the map. The producing law's prediction and
//! arrival family at the map's cut are readings of that passage, returned by
//! [`ResidentWaveRelation::read_source_passage`]; they are no longer anchored on the map.
use super::super::condition_contact::{AffineContactReading, ResidentContactReaction, block};
use super::*;

pub struct ResidentWaveSourceContact<'c> {
    pub(super) source: ResidentSection<'c>,
    pub(super) reaction: ResidentContactReaction<'c>,
    pub(super) relation_cut: u64,
    pub(super) source_row: Option<usize>,
}

/// The readings of one source passage: the relation it founds, and the producing law's
/// prediction and whole arrival family at the relation's cut.
pub struct ResidentWaveSourcePassage<'c> {
    pub relation: ResidentWaveRelation<'c>,
    pub prediction: ResidentConstitutiveReturn<'c>,
    pub arrival: ResidentConstitutiveReturn<'c>,
}

impl<'c> ResidentWaveSourceContact<'c> {
    pub fn source_row(&self) -> Option<usize> {
        self.source_row
    }
    pub fn source(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        ResidentConstitutiveCurrent::rational(&self.source).expect("admitted source snapshot")
    }
    /// The one contact reaction of the offered joint with its arrival family.
    pub fn reaction(&self) -> &ResidentContactReaction<'c> {
        &self.reaction
    }
    pub fn offered_joint(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        self.reaction.block(block::PREDECESSOR, false)
    }
    pub fn reacted_joint(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        self.reaction.block(block::SUCCESSOR, false)
    }
    pub fn returned_normal(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        self.reaction.block(block::RETURNED_NORMAL, false)
    }
    pub fn difference(&self) -> ResidentConstitutiveCurrent<'_, 'c> {
        self.reaction.block(block::DIFFERENCE, false)
    }
    pub fn inspect_reaction(&self) -> Result<AffineContactReading, ConstitutiveFibreError> {
        self.reaction.inspect(self.relation_cut, None)
    }
}
impl<'c> ResidentWaveRelation<'c> {
    pub(crate) fn with_source_row(mut self, row: usize) -> Self {
        self.source.as_mut().expect("source passage").source_row = Some(row);
        self
    }
    pub fn source_contact(&self) -> Option<&ResidentWaveSourceContact<'c>> {
        self.source.as_ref()
    }
    /// Actual incoming (c-p,c,p) is read by the admitted local law. Unit-admittance contact
    /// reacts the offered joint with its whole learned arrival. Only that actual reaction
    /// founds the passive source union; the held joint remains an anchored affine family.
    pub fn read_source_contact(
        &self,
        law: &ResidentConstitutiveFibre<'c>,
        source: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<Self, ConstitutiveFibreError> {
        Ok(self.read_source_passage(law, source)?.relation)
    }
    /// The same passage with its readings: the law's prediction at the fixed condition and the
    /// arrival family the offered joint met. Both are read at this relation's producing cut.
    pub fn read_source_passage(
        &self,
        law: &ResidentConstitutiveFibre<'c>,
        source: ResidentConstitutiveCurrent<'_, 'c>,
    ) -> Result<ResidentWaveSourcePassage<'c>, ConstitutiveFibreError> {
        if !Rc::ptr_eq(&self.producing_owner, &law.basis_owner)
            || self.relation_cut != law.occurrences
        {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        if self.source_geometry.get().is_none() {
            let geometry =
                super::super::condition_contact::ResidentWaveSourceGeometry::compile(law)?;
            self.source_geometry
                .set(geometry)
                .map_err(|_| ConstitutiveFibreError::ForeignOccurrence)?;
        }
        let prediction = law.read_bilinear(source, self.fixed_condition())?;
        let s = self.surface;
        let n = self.roots;
        let (contact, arrival) = prepare_source_contact(
            s,
            n,
            self.receiver,
            source,
            &prediction,
            self.source_geometry.get(),
        )?;
        let basis = source_basis(s, n, contact.reaction.section())?;
        let relation = Self {
            surface: s,
            basis,
            fixed: Rc::clone(&self.fixed),
            roots: n,
            condition_complex: self.condition_complex,
            relation_cut: self.relation_cut,
            producing_owner: Rc::clone(&self.producing_owner),
            receiver: self.receiver,
            source: Some(contact),
            observation: None,
            source_geometry: Rc::clone(&self.source_geometry),
        };
        Ok(ResidentWaveSourcePassage {
            relation,
            prediction,
            arrival,
        })
    }
}
/// The offered joint of `source` meets the arrival family of `prediction`; returns the retained
/// contact and the arrival family as a reading.
pub(super) fn prepare_source_contact<'c>(
    s: &'c ResidentSurface<'c>,
    n: usize,
    receiver: WaveSourceReceiver,
    source: ResidentConstitutiveCurrent<'_, 'c>,
    prediction: &ResidentConstitutiveReturn<'c>,
    geometry: Option<&super::super::condition_contact::ResidentWaveSourceGeometry<'c>>,
) -> Result<
    (
        ResidentWaveSourceContact<'c>,
        ResidentConstitutiveReturn<'c>,
    ),
    ConstitutiveFibreError,
> {
    let r = 2 * n;
    let w = 2 * r;
    if source.width != 3 * r || prediction.target_width != r {
        return Err(ConstitutiveFibreError::Shape);
    }
    let snapshot = s.fresh_section(1, 3 * r + 1, ResidentGrain(0))?;
    let offered = s.fresh_section(1, w + 1, ResidentGrain(0))?;
    let mut arrival = ResidentConstitutiveReturn::allocate(
        s,
        2,
        w,
        prediction.occurrence,
        ConstitutiveSourceChart::Linear,
    )?;
    let work = s.fresh_section(1, 2 * (w + 2), ResidentGrain(0))?;
    let mut p = s.begin_passage(&[vec![]])?;
    {
        let lane = p.open(0, &[])?;
        s.record_wave_source_arrival(
            &lane,
            source,
            prediction.report(),
            prediction.source_width,
            n,
            receiver,
            &snapshot,
            &offered,
            arrival.report(),
            &work,
        )?;
    }
    p.close(0, arrival.report(), 64)?;
    let received = p.finish()?.launch()?;
    if !received.obstruction.is_empty() {
        return Err(ConstitutiveFibreError::Arithmetic(format!(
            "source arrival: {:?}",
            received.obstruction
        )));
    }
    let offered = ResidentConstitutiveCurrent::rational(&offered)?;
    let metric = ConditionContactMetric::UnitAdmittanceRealification;
    let reaction = if let Some(geometry) = geometry {
        arrival.read_contact_with_geometry(offered, metric, geometry)?
    } else {
        arrival.read_contact(offered, metric)?
    }
    .into_reaction();
    if let Some(row) = prediction.source_occurrence {
        arrival.qualify_field_source(row);
    }
    Ok((
        ResidentWaveSourceContact {
            source: snapshot,
            reaction,
            relation_cut: prediction.occurrence,
            source_row: prediction.source_occurrence,
        },
        arrival,
    ))
}
pub(super) fn source_basis<'c>(
    s: &'c ResidentSurface<'c>,
    n: usize,
    reaction: &ResidentSection<'c>,
) -> Result<ResidentSection<'c>, ConstitutiveFibreError> {
    let q = n
        .checked_mul(8)
        .and_then(|v| v.checked_add(2))
        .ok_or(ConstitutiveFibreError::Shape)?;
    let k = q.checked_mul(2).ok_or(ConstitutiveFibreError::Shape)?;
    let basis = s.fresh_section(k, k, ResidentGrain(0))?;
    let workspace = s.fresh_section(1, 2 * (k + 4 * n), ResidentGrain(0))?;
    let mut p = s.begin_passage(&[vec![]])?;
    {
        let lane = p.open(0, &[])?;
        s.record_wave_source_map(&lane, reaction, n, &basis, &workspace)?;
    }
    p.close(0, &basis, 64)?;
    let receipt = p.finish()?.launch()?;
    if !receipt.obstruction.is_empty() {
        return Err(ConstitutiveFibreError::Arithmetic(format!(
            "source union map: {:?}",
            receipt.obstruction
        )));
    }
    Ok(basis)
}

impl<'c> ResidentWaveRelation<'c> {
    /// Specialization of affine relation image for this checked total source graph. Every
    /// generator is mapped; no source support is discarded and no particular is a point cast.
    pub(crate) fn read_source_image(
        &self,
        family: &ResidentConstitutiveReturn<'c>,
    ) -> Result<(ResidentConstitutiveReturn<'c>, ResidentSection<'c>), ConstitutiveFibreError> {
        if !self.is_total_current_map()
            || family.target_width != self.width()
            || !std::ptr::eq(family.surface, self.surface)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let s = self.surface;
        let q = self.width();
        let k = 2 * q;
        let mapped = s.fresh_section(q, q, ResidentGrain(0))?;
        let reduced = s.fresh_section(q, q, ResidentGrain(0))?;
        let output = ResidentConstitutiveReturn::allocate(
            s,
            k,
            q,
            self.relation_cut,
            ConstitutiveSourceChart::Linear,
        )?;
        let coverage = s.fresh_section(1, 4 + 3 * q, ResidentGrain(0))?;
        let workspace = s.fresh_section(q + 1, 2 * k, ResidentGrain(0))?;
        let admitted = s.fresh_section(1, 1, ResidentGrain(0))?;
        let mut p = s.begin_passage(&[vec![], vec![0], vec![1]])?;
        {
            let lane = p.open(0, &[])?;
            s.record_wave_source_image_rows(
                &lane,
                &self.basis,
                family.report(),
                family.source_width,
                q,
                true,
                &admitted,
                &mapped,
                output.report(),
                &workspace,
            )?;
        }
        p.close(0, &admitted, 64)?;
        {
            let lane = p.open(1, &[0])?;
            s.record_wave_source_image_rows(
                &lane,
                &self.basis,
                family.report(),
                family.source_width,
                q,
                false,
                &admitted,
                &mapped,
                output.report(),
                &workspace,
            )?;
        }
        p.close(1, &mapped, 64)?;
        {
            let lane = p.open(2, &[1])?;
            s.record_wave_source_image_finish(
                &lane,
                &mapped,
                q,
                &reduced,
                output.report(),
                &coverage,
                &workspace,
            )?;
        }
        p.close(2, output.report(), 64)?;
        let receipt = p.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "total source image: {:?}",
                receipt.obstruction
            )));
        }
        Ok((output, coverage))
    }
}

#[cfg(test)]
mod tests;
