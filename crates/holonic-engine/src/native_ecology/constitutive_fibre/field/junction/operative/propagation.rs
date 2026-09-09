//! Resident propagation on the existing borrowed operative source. This stages the actual
//! word and its forward carriers; publication awaits the complete joined field return.
use super::*;
use crate::resident_section::CausalPropagationLayout as Layout;
use num_bigint::BigInt;
use num_traits::One;
mod return_path;

pub struct NativeCausalContactPropagation<'f, 'c> {
    field: &'f NativeConstitutiveField<'c>,
    _origin: Rc<()>,
    _producing: Rc<OperativeSections<'c>>,
    births: Vec<NativeOperativeContactBirth>,
    grain: u32,
    _births: ResidentSection<'c>,
    pub(super) current: Rc<ResidentSection<'c>>,
    pub(super) bounds: Rc<ResidentSection<'c>>,
    pub(super) trace: Rc<ResidentSection<'c>>,
    summary: ResidentSection<'c>,
}

#[derive(Debug, Serialize)]
pub struct NativeCausalContactJoinReading {
    pub before: usize,
    pub after: usize,
    pub joining_occurrence: usize,
    pub incoming_pair: Vec<ExactComplexWaveCurrent>,
    pub incoming_radius: Rat,
    pub overlap: ExactComplexWaveCurrent,
    pub overlap_error: Rat,
    pub omitted_components: usize,
}

#[derive(Debug, Serialize)]
pub struct NativeCausalContactPropagationReading {
    pub field_cut: usize,
    pub fractional_bits: u32,
    pub internal: NativeFieldCurrentBall,
    pub contact_radius: Rat,
    pub rounding_radius: Rat,
    pub joins: Vec<NativeCausalContactJoinReading>,
}

impl<'f, 'c> NativeOperativeContactStaging<'f, 'c> {
    /// The device finds joins from this field's chronology and evaluates the complete word.
    /// This returns fresh current/trace carriers without changing the borrowed continuing field.
    pub fn propagate_causal_contacts(
        &self,
    ) -> Result<NativeCausalContactPropagation<'f, 'c>, Error> {
        let surface = self.field.relation.surface;
        let count = self.births.len();
        let d = 6 * self.field.nodes();
        let mut addresses = Vec::with_capacity(2 * count.max(1));
        for birth in &self.births {
            for at in [birth.source, birth.receiving] {
                let at = i64::try_from(at).map_err(invalid)?;
                addresses.push((at, at));
            }
        }
        if addresses.is_empty() {
            addresses.resize(2, (0, 0));
        }
        let births = surface.mount_section_rest(
            &ResidentSectionRest::found(count.max(1), 2, ResidentGrain(0), 64, addresses)
                .map_err(invalid)?,
        )?;
        let current = Rc::new(surface.fresh_section(count.max(1), 4, ResidentGrain(0))?);
        let bounds = Rc::new(surface.fresh_section(1, 4, ResidentGrain(0))?);
        let trace =
            Rc::new(surface.fresh_section(count.max(1), Layout::WORDS, ResidentGrain(0))?);
        let summary = surface.fresh_section(1, 4, ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_causal_contact_propagation(
                &lane,
                &births,
                self.sections.current(),
                d,
                count,
                self.grain,
                &current,
                &bounds,
                &trace,
                &summary,
            )?;
        }
        passage.close(0, &bounds, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "causal contact propagation: {:?}",
                receipt.obstruction
            )));
        }
        Ok(NativeCausalContactPropagation {
            field: self.field,
            _origin: Rc::clone(&self.origin),
            _producing: Rc::clone(&self.sections),
            births: self.births.clone(),
            grain: self.grain,
            _births: births,
            current,
            bounds,
            trace,
            summary,
        })
    }
}

impl NativeCausalContactPropagation<'_, '_> {
    /// Cold numerical observation. Staging itself performs no section readout.
    pub fn inspect(&self) -> Result<NativeCausalContactPropagationReading, Error> {
        let surface = self.field.relation.surface;
        let read = |s: &ResidentSection<'_>| surface.detach_section(s, 64).map_err(Error::from);
        let current = wides(&read(&self.current)?.intervals)?;
        let bounds = wides(&read(&self.bounds)?.intervals)?;
        let summary = wides(&read(&self.summary)?.intervals)?;
        let trace = read(&self.trace)?;
        let scale = BigInt::one() << self.grain;
        let rat = |v: i128| Rat::new(v.into(), scale.clone());
        let waves = |values: &[i128]| {
            values
                .chunks_exact(2)
                .map(|v| ExactComplexWaveCurrent::new(rat(v[0]), rat(v[1])))
                .collect::<Vec<_>>()
        };
        let history = |wire: &[(i64, i64)]| -> Result<Rat, Error> {
            if wire.len() != Layout::HISTORY_WORDS
                || wire.iter().any(|(a, b)| a != b)
                || !matches!(wire[Layout::HISTORY_WORDS - 1].0, 0 | 1)
            {
                return Err(Error::Shape);
            }
            let mut value = BigInt::from(0);
            for (at, part) in wire[..Layout::HISTORY_WORDS - 1].iter().enumerate() {
                value += BigInt::from(part.0 as u64) << (at * u64::BITS as usize);
            }
            if wire[Layout::HISTORY_WORDS - 1].0 != 0 {
                value = -value;
            }
            Ok(Rat::new(value, &scale * &scale))
        };
        let mut joins = Vec::new();
        for (after, row) in trace
            .intervals
            .chunks_exact(Layout::WORDS)
            .take(self.births.len())
            .enumerate()
        {
            if row.iter().any(|(a, b)| a != b)
                || row[1].0 != i64::try_from(self.births[after].receiving).map_err(invalid)?
            {
                return Err(Error::Shape);
            }
            if row[0].0 == -1 {
                continue;
            }
            let before = usize::try_from(row[0].0).map_err(invalid)?;
            if before >= after || self.births[before].receiving != self.births[after].source {
                return Err(Error::Shape);
            }
            let incoming = waves(&wides(&row[Layout::BEFORE..Layout::OVERLAP])?);
            let radius = wides(&row[Layout::RADIUS..Layout::OVERLAP_ERROR])?[0];
            let omitted = wides(&row[Layout::ROUNDS..Layout::WORDS])?[0];
            joins.push(NativeCausalContactJoinReading {
                before,
                after,
                joining_occurrence: self.births[after].source,
                incoming_pair: incoming,
                incoming_radius: rat(radius),
                overlap: ExactComplexWaveCurrent::new(
                    history(&row[Layout::OVERLAP..Layout::OVERLAP + Layout::HISTORY_WORDS])?,
                    history(&row[Layout::OVERLAP + Layout::HISTORY_WORDS..Layout::RADIUS])?,
                ),
                overlap_error: history(
                    &row[Layout::OVERLAP_ERROR..Layout::OVERLAP_ERROR + Layout::HISTORY_WORDS],
                )?,
                omitted_components: usize::try_from(omitted).map_err(invalid)?,
            });
        }
        if usize::try_from(summary[0]).map_err(invalid)? != joins.len()
            || summary[1]
                != joins
                    .iter()
                    .map(|j| j.omitted_components as i128)
                    .sum::<i128>()
            || bounds.iter().any(|v| *v < 0)
        {
            return Err(Error::Shape);
        }
        Ok(NativeCausalContactPropagationReading {
            field_cut: self.field.occurrence_count(),
            fractional_bits: self.grain,
            internal: NativeFieldCurrentBall {
                center: waves(&current[..2 * self.births.len()]),
                radius: rat(bounds[1]),
            },
            contact_radius: rat(bounds[0]),
            rounding_radius: rat(summary[1]),
            joins,
        })
    }
}

#[cfg(test)]
mod tests;
