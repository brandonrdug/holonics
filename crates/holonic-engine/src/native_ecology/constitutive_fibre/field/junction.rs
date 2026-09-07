//! Paired passive junction on the field's root current chart.
//!
//! Each actual joined source/arrival adds the Hermitian moment d d*, with d=(source,-arrival).
//! The native junction acts through that moment and retained internal current. This is a declared
//! unit-admittance junction, not selection of one value from the separate constitutive fibre.

use super::*;

#[derive(Debug, PartialEq, Eq, Serialize)]
pub struct NativeFieldJunctionReading {
    /// All three complex port blocks: two source branches per node, then the arriving-field port.
    pub potential: Vec<ExactComplexWaveCurrent>,
    pub outgoing: Vec<ExactComplexWaveCurrent>,
    /// R* b of the internal currents, sufficient for this junction's next boundary operation.
    pub held_current: Vec<ExactComplexWaveCurrent>,
    /// Alternating prefix of actual junction potentials. Together with each contact's birth
    /// prefix and source it decodes its actual internal current without choosing an inverse.
    pub potential_prefix: Vec<ExactComplexWaveCurrent>,
}

#[derive(Debug, PartialEq, Eq, Serialize)]
pub struct NativeFieldInternalCurrent {
    pub source_occurrence: usize,
    pub receiving_occurrence: usize,
    /// Actual root contact vector, retaining all source and receiving coordinates.
    pub contact: Vec<ExactComplexWaveCurrent>,
    pub current: ExactComplexWaveCurrent,
}

pub(super) struct PairedJunction<'chart> {
    pub(super) covariance: ResidentSection<'chart>,
    pub(super) current: Rc<ResidentSection<'chart>>,
}

pub(super) struct PendingJunction<'chart> {
    pub(super) covariance: ResidentSection<'chart>,
    pub(super) report: Rc<ResidentSection<'chart>>,
}

impl<'chart> NativeConstitutiveField<'chart> {
    /// Found the same field with a coupled passive junction. The initial paired moment and
    /// internal currents are zero. Unit port admittances specify this first junction chart;
    /// arbitrary unit-phase incidence and exact initial held currents remain admitted.
    pub fn found_with_paired_junction(
        surface: &'chart ResidentSurface<'chart>,
        material: Vec<NativeJunctionSeed>,
    ) -> Result<Self, ConstitutiveFibreError> {
        if material
            .iter()
            .any(|seed| seed.incoming_admittance != 1 || seed.held_admittance != 1)
        {
            return Err(ConstitutiveFibreError::Shape);
        }
        let mut body = Self::found(surface, material)?;
        let width = body.relation.source_width + body.relation.target_width;
        let count = width
            .checked_mul(width)
            .and_then(|n| n.checked_add(1))
            .ok_or(ConstitutiveFibreError::Shape)?;
        let mut covariance = vec![(0, 0); count];
        covariance[count - 1] = (1, 1);
        let mut report = vec![(0, 0); 4 * (width + 1)];
        for part in 0..4 {
            report[part * (width + 1) + width] = (1, 1);
        }
        let mount = |words: Vec<(i64, i64)>| -> Result<_, ConstitutiveFibreError> {
            Ok(surface.mount_section_rest(
                &ResidentSectionRest::found(1, words.len(), ResidentGrain(0), 64, words)
                    .map_err(|_| ConstitutiveFibreError::Shape)?,
            )?)
        };
        body.junction = Some(PairedJunction {
            covariance: mount(covariance)?,
            current: Rc::new(mount(report)?),
        });
        Ok(body)
    }

    pub fn has_paired_junction(&self) -> bool {
        self.junction.is_some()
    }

    /// Explicit observers; these create no source or reaction capability.
    pub fn inspect_junction_covariance(
        &self,
    ) -> Result<Option<ResidentSectionRest>, ConstitutiveFibreError> {
        self.junction
            .as_ref()
            .map(|junction| {
                self.relation
                    .surface
                    .detach_section(&junction.covariance, 64)
                    .map_err(Into::into)
            })
            .transpose()
    }

    pub fn inspect_junction(
        &self,
        occurrence: usize,
    ) -> Result<Option<ResidentSectionRest>, ConstitutiveFibreError> {
        let held = self
            .history
            .get(occurrence)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        held.junction
            .as_ref()
            .map(|section| {
                self.relation
                    .surface
                    .detach_section(section, 64)
                    .map_err(Into::into)
            })
            .transpose()
    }

    /// Executable reconstruction of every actual internal current. This is an explicitly
    /// requested cold receiver over immutable native source/prefix sections, never the productive
    /// update. It does not select a vector from the kernel of the moment map or replay cultivation.
    pub fn inspect_internal_currents(
        &self,
    ) -> Result<Option<Vec<NativeFieldInternalCurrent>>, ConstitutiveFibreError> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let Some(junction) = self.junction.as_ref() else {
            return Ok(None);
        };
        let width = self.relation.source_width + self.relation.target_width;
        let prefix = |section: &ResidentSection<'chart>| -> Result<Vec<ExactComplexWaveCurrent>, ConstitutiveFibreError> {
            let words = self.relation.surface.read_out(section)?;
            let at = 3 * (width + 1);
            let den = words[at + width].0;
            if den <= 0 || words.iter().any(|(a,b)| a != b) { return Err(ConstitutiveFibreError::Uncertain); }
            Ok((0..width/2).map(|j| ExactComplexWaveCurrent::new(
                Rat::new(words[at + 2*j].0.into(), den.into()),
                Rat::new(words[at + 2*j+1].0.into(), den.into()),
            )).collect())
        };
        let current_prefix = prefix(&junction.current)?;
        let sign = Rat::from_integer(if self.history.len() % 2 == 1 { 1 } else { -1 }.into());
        let mut internal = Vec::new();
        for (receiving, event) in self.history.iter().enumerate() {
            let Some(source_at) = event.lineage.received_from else {
                continue;
            };
            let source = &self.history[source_at];
            let source_words = self.relation.surface.read_out(&source.section)?;
            let denominator = source_words[self.relation.source_width].0;
            if denominator <= 0 || source_words.iter().any(|(a, b)| a != b) {
                return Err(ConstitutiveFibreError::Uncertain);
            }
            let mut contact = Vec::with_capacity(width / 2);
            for (node, frame) in source.frame.view.root_to_local().iter().enumerate() {
                for branch in 0..2 {
                    let at = 4 * node + 2 * branch;
                    let local = ExactComplexWaveCurrent::new(
                        Rat::new(source_words[at].0.into(), denominator.into()),
                        Rat::new(source_words[at + 1].0.into(), denominator.into()),
                    );
                    contact.push(frame.current().conjugate().multiply(&local));
                }
            }
            let minus_one = Rat::from_integer((-1).into());
            contact.extend(
                event
                    .lineage
                    .incoming
                    .iter()
                    .map(|a| a.current().scaled(&minus_one)),
            );
            let before = if receiving == 0 {
                vec![ExactComplexWaveCurrent::zero(); width / 2]
            } else {
                prefix(
                    self.history[receiving - 1]
                        .junction
                        .as_ref()
                        .ok_or(ConstitutiveFibreError::Uncertain)?,
                )?
            };
            let current = contact
                .iter()
                .zip(current_prefix.iter().zip(&before))
                .fold(
                    ExactComplexWaveCurrent::zero(),
                    |total, (d, (now, birth))| {
                        total.add(&d.conjugate().multiply(&now.subtract(birth)))
                    },
                )
                .scaled(&sign);
            internal.push(NativeFieldInternalCurrent {
                source_occurrence: source_at,
                receiving_occurrence: receiving,
                contact,
                current,
            });
        }
        Ok(Some(internal))
    }

    pub(super) fn prepare_junction(
        &self,
    ) -> Result<Option<(PendingJunction<'chart>, ResidentSection<'chart>)>, ConstitutiveFibreError>
    {
        if self.junction.is_none() {
            return Ok(None);
        }
        let width = self.relation.source_width + self.relation.target_width;
        let surface = self.relation.surface;
        // The scratch section is apparatus storage for signed wide words. Its low allocation is
        // interpreted as i128 only by the private native kernel; no interval readout is made.
        let scratch_words = width
            .checked_mul(width + 1)
            .and_then(|n| n.checked_add(6 * width))
            .and_then(|n| n.checked_mul(2))
            .ok_or(ConstitutiveFibreError::Shape)?;
        Ok(Some((
            PendingJunction {
                covariance: surface.fresh_section(1, width * width + 1, ResidentGrain(0))?,
                report: Rc::new(surface.fresh_section(1, 4 * (width + 1), ResidentGrain(0))?),
            },
            surface.fresh_section(1, scratch_words, ResidentGrain(0))?,
        )))
    }

    pub(super) fn read_pending_junction(
        &self,
    ) -> Result<Option<NativeFieldJunctionReading>, ConstitutiveFibreError> {
        let Some(pending) = self.pending_junction.as_ref() else {
            return Ok(None);
        };
        let words = self.relation.surface.read_out(&pending.report)?;
        let width = self.relation.source_width + self.relation.target_width;
        let stride = width + 1;
        if words.len() != 4 * stride
            || words.iter().any(|(lo, hi)| lo != hi)
            || (0..4).any(|part| words[part * stride + width].0 <= 0)
        {
            return Err(ConstitutiveFibreError::Uncertain);
        }
        let decode = |part: usize| -> Vec<ExactComplexWaveCurrent> {
            let at = part * stride;
            let denominator = words[at + width].0;
            (0..width / 2)
                .map(|i| {
                    ExactComplexWaveCurrent::new(
                        Rat::new(words[at + 2 * i].0.into(), denominator.into()),
                        Rat::new(words[at + 2 * i + 1].0.into(), denominator.into()),
                    )
                })
                .collect()
        };
        Ok(Some(NativeFieldJunctionReading {
            potential: decode(0),
            outgoing: decode(1),
            held_current: decode(2),
            potential_prefix: decode(3),
        }))
    }
}

#[cfg(test)]
mod tests;
