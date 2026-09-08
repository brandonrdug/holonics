//! Resident receiver of one caused contact's actual internal current, with its full contact.
use super::*;

#[derive(Debug, PartialEq, Eq, Serialize)]
pub enum NativeInternalPointAvailability {
    Exact,
    NumericalEnclosure,
    WordAperture,
}

#[derive(Debug, PartialEq, Eq, Serialize)]
pub struct NativeInternalCurrentReading {
    pub source_occurrence: usize,
    pub receiving_occurrence: usize,
    pub at_state: usize,
    pub contact: Vec<ExactComplexWaveCurrent>,
    pub current: NativeFieldCurrentBall,
    pub point_availability: NativeInternalPointAvailability,
}

/// Immutable receiver return. It retains the defining root contact and producing/current cuts;
/// it owns no ecology. A numerical ball is never silently substituted for its actual current.
pub struct NativeResidentInternalCurrent<'chart> {
    surface: &'chart ResidentSurface<'chart>,
    contact: ResidentSection<'chart>,
    report: ResidentSection<'chart>,
    source_occurrence: usize,
    receiving_occurrence: usize,
    at_state: usize,
}
impl<'chart> NativeResidentInternalCurrent<'chart> {
    /// Native point consumption checks the returned disposition. A nonzero enclosure radius or
    /// an exact value beyond the word representation remains available through `inspect`.
    pub fn current(&self) -> ResidentConstitutiveCurrent<'_, 'chart> {
        ResidentConstitutiveCurrent {
            section: &self.report,
            offset: 8,
            width: 2,
            denominator: Some(10),
            disposition: Some(11),
        }
    }
    pub fn inspect(&self) -> Result<NativeInternalCurrentReading, ConstitutiveFibreError> {
        let (contact, current, point_availability) =
            inspect_sections(self.surface, &self.contact, &self.report)?;
        Ok(NativeInternalCurrentReading {
            source_occurrence: self.source_occurrence,
            receiving_occurrence: self.receiving_occurrence,
            at_state: self.at_state,
            contact,
            current,
            point_availability,
        })
    }
}

pub(super) fn inspect_sections<'c>(
    surface: &ResidentSurface<'c>,
    contact: &ResidentSection<'c>,
    report: &ResidentSection<'c>,
) -> Result<
    (
        Vec<ExactComplexWaveCurrent>,
        NativeFieldCurrentBall,
        NativeInternalPointAvailability,
    ),
    ConstitutiveFibreError,
> {
    let report = surface.read_out(report)?;
    let contact = material_transport::wides(&surface.read_out(contact)?)?;
    let v = material_transport::wides(&report[..8])?;
    let cd = *contact.last().ok_or(ConstitutiveFibreError::Shape)?;
    if cd <= 0 || v[3] <= 0 || v[2] < 0 || report.iter().any(|(l, h)| l != h) {
        return Err(ConstitutiveFibreError::Uncertain);
    }
    let complex = |r: i128, i: i128, d: i128| {
        ExactComplexWaveCurrent::new(Rat::new(r.into(), d.into()), Rat::new(i.into(), d.into()))
    };
    Ok((
        contact[..contact.len() - 1]
            .chunks_exact(2)
            .map(|p| complex(p[0], p[1], cd))
            .collect(),
        NativeFieldCurrentBall {
            center: vec![complex(v[0], v[1], v[3])],
            radius: Rat::new(v[2].into(), v[3].into()),
        },
        match report[11].0 {
            0 => NativeInternalPointAvailability::Exact,
            1 => NativeInternalPointAvailability::NumericalEnclosure,
            2 => NativeInternalPointAvailability::WordAperture,
            _ => return Err(ConstitutiveFibreError::Uncertain),
        },
    ))
}

impl<'chart> NativeConstitutiveField<'chart> {
    /// Receive a component born at an actual available contact, at the contemporary state cut.
    /// The anchor must belong to this body and name a receiving occurrence with a caused source.
    /// This is a particular internal receiver, not a claim that one scalar is complete context.
    pub fn read_internal_current(
        &mut self,
        birth: &NativeFieldSourceAnchor,
    ) -> Result<NativeResidentInternalCurrent<'chart>, ConstitutiveFibreError> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        if !Rc::ptr_eq(&self.owner, &birth.owner) || birth.occurrence >= self.history.len() {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        self.read_internal_current_at(birth.occurrence)
    }

    /// Read an existing body-local contact address. This issues no source/receiving capability
    /// and does not require retaining one merely to inspect the body's own material.
    pub fn read_internal_current_at(
        &mut self,
        receiving: usize,
    ) -> Result<NativeResidentInternalCurrent<'chart>, ConstitutiveFibreError> {
        if self.junction.as_ref().and_then(|j|j.operative.as_ref()).is_some_and(|o|!o.is_fixed()) {
            return Err(ConstitutiveFibreError::Rest("changed operative contacts require their native current carrier".into()));
        }
        let at = self
            .history
            .len()
            .checked_sub(1)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        let (source, contact, report) = self.internal_current_section(receiving, at)?;
        Ok(NativeResidentInternalCurrent {
            surface: self.relation.surface,
            contact,
            report,
            source_occurrence: source,
            receiving_occurrence: receiving,
            at_state: at,
        })
    }

    /// Prefix receiver used by the singleton and by a separately certified shared-drive mode.
    /// Metadata is attached by the corresponding public owner, not inferred from this raw section.
    pub(super) fn internal_current_section(
        &mut self,
        receiving: usize,
        prefix_at: usize,
    ) -> Result<(usize, ResidentSection<'chart>, ResidentSection<'chart>), ConstitutiveFibreError>
    {
        if !self.relation.usable || self.pending.is_some() {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        if receiving >= self.history.len() || prefix_at >= self.history.len() {
            return Err(ConstitutiveFibreError::ForeignOccurrence);
        }
        let source = self.history[receiving]
            .lineage
            .received_from
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        let before = receiving
            .checked_sub(1)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        let representation = self
            .junction_representation()
            .ok_or(ConstitutiveFibreError::Shape)?;
        for at in [source, receiving, before, prefix_at] {
            self.mount_history_source(at)?;
        }
        let s = self.relation.surface;
        let event = &self.history[receiving];
        let input = if let Some(input) = &event.resident()?.incoming {
            Rc::clone(input)
        } else {
            let values = event
                .lineage
                .incoming
                .exterior()
                .ok_or(ConstitutiveFibreError::Uncertain)?;
            Rc::new(
                s.mount_section_rest(
                    &ResidentSectionRest::found(
                        self.nodes(),
                        3,
                        ResidentGrain(0),
                        64,
                        values
                            .iter()
                            .flat_map(|p| p.words())
                            .map(|v| (v, v))
                            .collect(),
                    )
                    .map_err(|_| ConstitutiveFibreError::Shape)?,
                )?,
            )
        };
        let contact = s.fresh_section(1, 2 * (6 * self.nodes() + 1), ResidentGrain(0))?;
        let report = s.fresh_section(1, 12, ResidentGrain(0))?;
        let at = self.history.len() - 1;
        let mut passage = s.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            s.record_field_internal_current(
                &lane,
                &event.resident()?.section,
                &self.history[source].resident()?.section,
                &input,
                &event.frame.native,
                &self.history[source].frame.native,
                self.history[before]
                    .resident()?
                    .junction
                    .as_deref()
                    .ok_or(ConstitutiveFibreError::Uncertain)?,
                self.history[prefix_at]
                    .resident()?
                    .junction
                    .as_deref()
                    .ok_or(ConstitutiveFibreError::Uncertain)?,
                self.nodes(),
                representation,
                at as u64,
                &contact,
                &report,
            )?;
        }
        passage.close(0, &report, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(ConstitutiveFibreError::Arithmetic(format!(
                "internal-current receiver: {:?}",
                receipt.obstruction
            )));
        }
        Ok((source, contact, report))
    }
}

#[cfg(test)]
pub(super) mod tests;
