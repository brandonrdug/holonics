//! Native complete-current source geometry and its explicit construction receiver.
//! The receiver observes completed returns; material owners reuse the same source chart.
use super::*;
use num_bigint::BigInt;
use num_traits::{One, Zero};

pub struct NativeCurrentHistorySource<'chart> {
    owner: Rc<()>,
    occurrence: usize,
    section: ResidentSection<'chart>,
}
impl NativeCurrentHistorySource<'_> {
    pub fn occurrence(&self) -> usize {
        self.occurrence
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Serialize)]
pub struct NativeCurrentHistorySourceReading {
    pub occurrence: usize,
    pub outgoing_center: Vec<ExactComplexWaveCurrent>,
    pub prefix_center: Vec<ExactComplexWaveCurrent>,
    pub numerical_prefix_image: Vec<ExactComplexWaveCurrent>,
    pub numerical_birth_offset: ExactComplexWaveCurrent,
    pub numerical_norm_square: Rat,
    pub source_radius: Rat,
    pub contact_trace: BigInt,
    pub numerical_norm_upper: Rat,
}

impl NativeCurrentHistorySourceReading {
    /// Cold numerical pairing in one field's common root/birth chart. This is not the
    /// unknown exact physical pairing; its operands keep their separate source radii.
    pub(super) fn numerical_pairing(&self, other: &Self) -> ExactComplexWaveCurrent {
        let dot = |a: &[ExactComplexWaveCurrent], b: &[ExactComplexWaveCurrent]| {
            a.iter()
                .zip(b)
                .fold(ExactComplexWaveCurrent::zero(), |s, (a, b)| {
                    s.add(&a.conjugate().multiply(b))
                })
        };
        let (old, now) = if self.occurrence <= other.occurrence {
            (self, other)
        } else {
            (other, self)
        };
        let internal = dot(&old.numerical_prefix_image, &now.prefix_center)
            .subtract(&old.numerical_birth_offset.conjugate());
        let sign = Rat::from_integer(
            (if (old.occurrence + now.occurrence) % 2 == 0 {
                1
            } else {
                -1
            })
            .into(),
        );
        let value = dot(&old.outgoing_center, &now.outgoing_center).add(&internal.scaled(&sign));
        if self.occurrence <= other.occurrence {
            value
        } else {
            value.conjugate()
        }
    }
}

/// One prefix expression over completed returns from one field. Its scalar/vector carriers are
/// computed on the device and retain the original numerical uncertainty. It owns no ecology.
pub struct NativeCurrentHistorySourceReceiver<'chart> {
    owner: Rc<()>,
    surface: &'chart ResidentSurface<'chart>,
    nodes: usize,
    grain: u32,
    next: usize,
    state: ResidentSection<'chart>,
    before: Rc<ResidentSection<'chart>>,
}
type Error = ConstitutiveFibreError;
fn invalid(detail: impl std::fmt::Display) -> Error {
    Error::Rest(format!("complete-current source: {detail}"))
}
pub(super) fn integer(words: &[(i64, i64)]) -> Result<BigInt, Error> {
    if words.len() != 5 || words.iter().any(|(a, b)| a != b) || !matches!(words[4].0, 0 | 1) {
        return Err(invalid("signed-magnitude wire"));
    }
    let mut value = BigInt::zero();
    for (at, word) in words[..4].iter().enumerate() {
        value += BigInt::from(word.0 as u64) << (64 * at);
    }
    if words[4].0 == 1 {
        if value.is_zero() {
            return Err(invalid("negative zero"));
        }
        value = -value;
    }
    Ok(value)
}

impl<'chart> NativeCurrentHistorySourceReceiver<'chart> {
    pub fn inspect_wire(
        &self,
        source: &NativeCurrentHistorySource<'chart>,
    ) -> Result<ResidentSectionRest, Error> {
        if !Rc::ptr_eq(&self.owner, &source.owner) {
            return Err(Error::ForeignOccurrence);
        }
        Ok(self.surface.detach_section(&source.section, 64)?)
    }
    pub fn inspect_state(&self) -> Result<ResidentSectionRest, Error> {
        Ok(self.surface.detach_section(&self.state, 64)?)
    }
    pub fn on_empty(field: &NativeConstitutiveField<'chart>) -> Result<Self, Error> {
        if !field.relation.usable || field.pending.is_some() {
            return Err(Error::Uncertain);
        }
        if !field.history.is_empty() {
            return Err(invalid(
                "the prefix receiver starts before the first field occurrence",
            ));
        }
        let grain = match field.junction_representation() {
            Some(NativeFieldJunctionRepresentation::EnclosedDyadic { fractional_bits }) => {
                fractional_bits
            }
            _ => return Err(invalid("enclosed junction required")),
        };
        let d = 6 * field.nodes();
        let mut words = vec![(0, 0); 2 * d + 8];
        words[2 * d + 6] = (grain as i64, grain as i64);
        let surface = field.relation.surface;
        let state = surface.mount_section_rest(
            &ResidentSectionRest::found(1, words.len(), ResidentGrain(0), 64, words)
                .map_err(invalid)?,
        )?;
        Ok(Self {
            owner: Rc::clone(&field.owner),
            surface,
            nodes: field.nodes(),
            grain,
            next: 0,
            state,
            before: Rc::clone(&field.junction.as_ref().expect("enclosed junction").current),
        })
    }
    /// Observe the next actually completed return while its receiving carriers are resident.
    /// Failure retains this receiver's preceding expression and never rolls back the field.
    pub fn receive_completed(
        &mut self,
        field: &NativeConstitutiveField<'chart>,
    ) -> Result<NativeCurrentHistorySource<'chart>, Error> {
        if !Rc::ptr_eq(&self.owner, &field.owner) {
            return Err(Error::ForeignOccurrence);
        }
        if !field.relation.usable || field.pending.is_some() {
            return Err(Error::Uncertain);
        }
        if field.history.len() != self.next + 1 {
            return Err(invalid("completed field/prefix chronology mismatch"));
        }
        let at = self.next;
        let event = &field.history[at];
        let d = 6 * self.nodes;
        let incoming = if let Some(input) = &event.resident()?.incoming {
            Rc::clone(input)
        } else {
            Rc::new(
                self.surface.mount_section_rest(
                    &ResidentSectionRest::found(
                        self.nodes,
                        3,
                        ResidentGrain(0),
                        64,
                        event
                            .lineage
                            .incoming
                            .exterior()
                            .ok_or_else(|| invalid("missing resident input"))?
                            .iter()
                            .flat_map(|p| p.words())
                            .map(|w| (w, w))
                            .collect(),
                    )
                    .map_err(invalid)?,
                )?,
            )
        };
        let next = self.surface.fresh_section(1, 2 * d + 8, ResidentGrain(0))?;
        let source = self
            .surface
            .fresh_section(1, 6 * d + 22, ResidentGrain(0))?;
        let origin = event.lineage.received_from.map(|i| &field.history[i]);
        let junction = field
            .junction
            .as_ref()
            .ok_or_else(|| invalid("missing junction"))?;
        let mut passage = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.surface.record_field_current_history_source(
                &lane,
                &event.resident()?.section,
                origin
                    .map(|s| s.resident().map(|s| &s.section))
                    .transpose()?,
                &incoming,
                &event.frame.native,
                origin.map(|s| &s.frame.native),
                &junction.covariance,
                &self.before,
                &junction.current,
                &self.state,
                self.nodes,
                self.grain,
                at as u64,
                &next,
                &source,
            )?;
        }
        passage.close(0, &source, 64)?;
        let reading = passage.finish()?.launch()?;
        if !reading.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "integral-contact complete-current source: {:?}",
                reading.obstruction
            )));
        }
        self.state = next;
        self.before = Rc::clone(&junction.current);
        self.next += 1;
        Ok(NativeCurrentHistorySource {
            owner: Rc::clone(&self.owner),
            occurrence: at,
            section: source,
        })
    }
    /// Exact factorization of the numerical representatives. source_radius bounds the complete
    /// actual source (outgoing plus born internal currents), not the auxiliary prefix coordinates.
    pub fn inspect(
        &self,
        source: &NativeCurrentHistorySource<'chart>,
    ) -> Result<NativeCurrentHistorySourceReading, Error> {
        if !Rc::ptr_eq(&self.owner, &source.owner) {
            return Err(Error::ForeignOccurrence);
        }
        let words = self.surface.read_out(&source.section)?;
        decode_source(&words, self.nodes, self.grain, source.occurrence)
    }
    /// Enclose the full actual source pairing. The centre is the exact pairing of numerical
    /// representatives; the radius retains both complete-source uncertainties.
    pub fn pairing(
        &self,
        left: &NativeCurrentHistorySource<'chart>,
        right: &NativeCurrentHistorySource<'chart>,
    ) -> Result<NativeFieldCurrentBall, Error> {
        if !Rc::ptr_eq(&self.owner, &left.owner) || !Rc::ptr_eq(&self.owner, &right.owner) {
            return Err(Error::ForeignOccurrence);
        }
        let output = self.surface.fresh_section(1, 15, ResidentGrain(0))?;
        let mut passage = self.surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            self.surface.record_field_current_history_pairing(
                &lane,
                &left.section,
                &right.section,
                6 * self.nodes,
                &output,
            )?;
        }
        passage.close(0, &output, 64)?;
        let reading = passage.finish()?.launch()?;
        if !reading.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "complete-current pairing: {:?}",
                reading.obstruction
            )));
        }
        let words = self.surface.read_out(&output)?;
        let scale = BigInt::one() << (2 * self.grain);
        Ok(NativeFieldCurrentBall {
            center: vec![ExactComplexWaveCurrent::new(
                Rat::new(integer(&words[..5])?, scale.clone()),
                Rat::new(integer(&words[5..10])?, scale.clone()),
            )],
            radius: Rat::new(integer(&words[10..])?, scale),
        })
    }
}

#[cfg(test)]
mod tests;

pub(super) fn decode_source(
    words: &[(i64, i64)],
    nodes: usize,
    grain: u32,
    occurrence: usize,
) -> Result<NativeCurrentHistorySourceReading, Error> {
    let d = 6 * nodes;
    if words.len() != 6 * d + 22
        || words.iter().any(|(a, b)| a != b)
        || words[6 * d + 15].0 != grain as i64
        || words[6 * d + 19].0 != occurrence as i64
    {
        return Err(invalid("source wire"));
    }
    let wide = material_transport::wides(&words[..6 * d])?;
    let scale = BigInt::one() << grain;
    let square = &scale * &scale;
    let vector = |offset: usize| -> Vec<ExactComplexWaveCurrent> {
        (0..d / 2)
            .map(|i| {
                ExactComplexWaveCurrent::new(
                    Rat::new(wide[offset + 2 * i].into(), scale.clone()),
                    Rat::new(wide[offset + 2 * i + 1].into(), scale.clone()),
                )
            })
            .collect()
    };
    let norm = integer(&words[6 * d + 10..6 * d + 15])?;
    let radius = material_transport::wides(&words[6 * d + 16..6 * d + 18])?[0];
    if norm < BigInt::zero() || radius < 0 || words[6 * d + 18].0 < 0 {
        return Err(invalid("negative source radius, norm or trace"));
    }
    Ok(NativeCurrentHistorySourceReading {
        occurrence: occurrence,
        outgoing_center: vector(0),
        prefix_center: vector(d),
        numerical_prefix_image: vector(2 * d),
        numerical_birth_offset: ExactComplexWaveCurrent::new(
            Rat::new(integer(&words[6 * d..6 * d + 5])?, square.clone()),
            Rat::new(integer(&words[6 * d + 5..6 * d + 10])?, square.clone()),
        ),
        numerical_norm_square: Rat::new(norm, square),
        source_radius: Rat::new(radius.into(), scale.clone()),
        contact_trace: words[6 * d + 18].0.into(),
        numerical_norm_upper: Rat::new(
            material_transport::wides(&words[6 * d + 20..6 * d + 22])?[0].into(),
            scale,
        ),
    })
}
