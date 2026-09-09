//! One retained adjoint factor is the actual source interior difference. Its source address
//! survives archival; no old history current is pinned on the device by the generator.
use super::*;

#[derive(Debug, Serialize)]
pub struct NativeOperativeCurrentFactorCondensation {
    pub at_cut: usize,
    pub converted: usize,
    pub already_generated: usize,
    pub retained_materialized: usize,
    pub factor_octets_before: u64,
    pub factor_octets_after: u64,
}

impl OperativeState<'_> {
    fn has_current_deposit_at(&self, cut: usize) -> bool {
        let first = self.returns.partition_point(|r| r.at_cut < cut);
        self.returns[first..]
            .iter()
            .take_while(|r| r.at_cut == cut)
            .any(|r| r.b.is_some())
    }
}

impl<'c> NativeConstitutiveField<'c> {
    fn operative_current_boundary(
        &self,
        source: usize,
        count: usize,
    ) -> Result<(Rc<ResidentSection<'c>>, Rc<ResidentSection<'c>>, usize), Error> {
        let op = self
            .junction
            .as_ref()
            .and_then(|j| j.operative.as_ref())
            .ok_or(Error::Shape)?;
        if source < op.activated_at {
            return Err(Error::ForeignOccurrence);
        }
        let read = |at: usize| -> Result<(Rc<ResidentSection<'c>>, usize), Error> {
            let h = self.history.get(at).ok_or(Error::ForeignOccurrence)?;
            if let Some(resident) = &h.resident {
                let o = resident.operative.as_ref().ok_or(Error::Shape)?;
                return Ok((Rc::clone(&o.b), o.count));
            }
            let o = h
                .rest(self.relation.surface)?
                .operative
                .ok_or(Error::Shape)?;
            Ok((
                Rc::new(self.relation.surface.mount_section_rest(&o.b)?),
                o.count,
            ))
        };
        let (after, after_count) = read(source)?;
        let (before, before_count) = if source == op.activated_at {
            (
                Rc::clone(&op.initial.b),
                op.births
                    .iter()
                    .filter(|b| b.receiving < op.activated_at)
                    .count(),
            )
        } else {
            read(source - 1)?
        };
        if after_count != count || before_count > count {
            return Err(Error::Shape);
        }
        // A separate nonzero current deposit between these boundaries has its own source.
        // Such returns retain their materialized factor until that larger generator is bound.
        if op.has_current_deposit_at(source) {
            return Err(Error::Arithmetic(
                "source interior has an intervening current deposit".into(),
            ));
        }
        Ok((before, after, before_count))
    }

    pub(super) fn condense_operative_current_factors(
        &self,
        source: usize,
        count: usize,
        factors: &Rc<ResidentSection<'c>>,
    ) -> Result<Option<Rc<ResidentSection<'c>>>, Error> {
        let op = self
            .junction
            .as_ref()
            .and_then(|j| j.operative.as_ref())
            .ok_or(Error::Shape)?;
        if op.has_current_deposit_at(source) {
            return Ok(None);
        }
        let (before, after, before_count) = self.operative_current_boundary(source, count)?;
        self.transcode_operative_current_factors(
            &before,
            &after,
            factors,
            before_count,
            count,
            count,
            true,
        )
        .map(Some)
    }

    pub(super) fn resolve_operative_current_factors(
        &self,
        returned: &OperativeReturn<'c>,
    ) -> Result<Rc<ResidentSection<'c>>, Error> {
        self.resolve_operative_current_factor_prefix(returned, returned.factor_count)
            .map(|v| v.0)
    }

    pub(super) fn resolve_operative_current_factor_prefix(
        &self,
        returned: &OperativeReturn<'c>,
        limit: usize,
    ) -> Result<(Rc<ResidentSection<'c>>, usize), Error> {
        let Some(source) = returned.current_difference_source else {
            return Ok((Rc::clone(&returned.currents), returned.factor_count));
        };
        let count = returned.factor_count.min(limit);
        let (before, after, before_count) =
            self.operative_current_boundary(source, returned.factor_count)?;
        let factors = self.transcode_operative_current_factors(
            &before,
            &after,
            &returned.currents,
            before_count,
            returned.factor_count,
            count,
            false,
        )?;
        Ok((factors, count))
    }

    fn transcode_operative_current_factors(
        &self,
        before: &ResidentSection<'c>,
        after: &ResidentSection<'c>,
        factors: &ResidentSection<'c>,
        before_count: usize,
        count: usize,
        prefix_count: usize,
        encode: bool,
    ) -> Result<Rc<ResidentSection<'c>>, Error> {
        let surface = self.relation.surface;
        let complex_words = 2 * (std::mem::size_of::<i128>() / std::mem::size_of::<i64>());
        let output = Rc::new(surface.fresh_section(
            if encode { 1 } else { 2 },
            complex_words * prefix_count.max(1),
            ResidentGrain(0),
        )?);
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_operative_current_difference(
                &lane,
                before,
                after,
                factors,
                before_count,
                count,
                prefix_count,
                encode,
                &output,
            )?;
        }
        passage.close(0, &output, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "current-factor boundary: {:?}",
                receipt.obstruction
            )));
        }
        Ok(output)
    }

    /// Condense already retained returns without replaying an occurrence or changing current.
    /// Stage every new immutable factor before publishing the representation. A legacy factor
    /// with a different domain or an intervening current deposit remains materialized.
    pub fn condense_operative_current_journal(
        &mut self,
    ) -> Result<NativeOperativeCurrentFactorCondensation, Error> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(Error::Uncertain);
        }
        let op = self
            .junction
            .as_ref()
            .and_then(|j| j.operative.as_ref())
            .ok_or(Error::Shape)?;
        let mut result = NativeOperativeCurrentFactorCondensation {
            at_cut: self.history.len(),
            converted: 0,
            already_generated: 0,
            retained_materialized: 0,
            factor_octets_before: op
                .returns
                .iter()
                .map(|r| r.currents.resident_octets())
                .sum(),
            factor_octets_after: 0,
        };
        let mut prepared = Vec::with_capacity(op.returns.len());
        for r in &op.returns {
            if r.current_difference_source.is_some() {
                result.already_generated += 1;
                prepared.push(Rc::clone(r));
                continue;
            }
            let source = r
                .at_cut
                .checked_sub(1)
                .and_then(|at| self.history.get(at))
                .and_then(|h| h.lineage.observed_source());
            let Some(source) = source.filter(|&source| {
                source >= op.activated_at
                    && op.births.partition_point(|b| b.receiving <= source) == r.factor_count
            }) else {
                result.retained_materialized += 1;
                prepared.push(Rc::clone(r));
                continue;
            };
            let Some(currents) =
                self.condense_operative_current_factors(source, r.factor_count, &r.currents)?
            else {
                result.retained_materialized += 1;
                prepared.push(Rc::clone(r));
                continue;
            };
            prepared.push(Rc::new(OperativeReturn {
                at_cut: r.at_cut,
                contact_count: r.contact_count,
                factor_count: r.factor_count,
                realization: r.realization,
                origin: Rc::clone(&r.origin),
                ports: Rc::clone(&r.ports),
                currents,
                current_difference_source: Some(source),
                b: r.b.clone(),
                bounds: Rc::clone(&r.bounds),
            }));
            result.converted += 1;
        }
        result.factor_octets_after = prepared.iter().map(|r| r.currents.resident_octets()).sum();
        self.junction
            .as_mut()
            .unwrap()
            .operative
            .as_mut()
            .unwrap()
            .returns = prepared;
        Ok(result)
    }
}
