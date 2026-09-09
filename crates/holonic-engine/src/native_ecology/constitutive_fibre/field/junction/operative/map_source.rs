//! The existing return journal extended by source-map expressions. One immutable anchor and
//! actual later birth columns generate historical maps; this is not a second continuing field.
use super::*;
#[cfg(test)]
mod tests;

#[derive(Clone)]
pub(super) struct OperativeMapProgram<'c> {
    pub at_cut: usize,
    pub return_count: usize,
    pub contact_count: usize,
    pub map: Rc<ResidentSection<'c>>,
    pub births: Vec<Rc<ResidentSection<'c>>>,
}

#[derive(Clone)]
pub(super) struct OperativeSourceOverlap<'c> {
    pub source: usize,
    pub count: usize,
    pub coefficients: Rc<ResidentSection<'c>>,
    pub errors: Rc<ResidentSection<'c>>,
}

impl<'c> NativeConstitutiveField<'c> {
    /// Retain one coefficient anchor. Later columns are captured by their actual birth passage.
    /// This changes representation only; it creates no occurrence, coefficient or current.
    pub(super) fn retain_operative_map_program(&mut self) -> Result<(), Error> {
        if !self.relation.usable || self.pending.is_some() {
            return Err(Error::Uncertain);
        }
        let cut = self.history.len();
        let op = self
            .junction
            .as_mut()
            .and_then(|j| j.operative.as_mut())
            .ok_or(Error::Shape)?;
        if op.program.is_none() {
            op.program = Some(OperativeMapProgram {
                at_cut: cut,
                return_count: op.returns.len(),
                contact_count: op.births.len(),
                map: Rc::clone(&op.sections.map),
                births: Vec::new(),
            });
        }
        Ok(())
    }

    pub(super) fn operative_birth_addresses(
        &self,
        count: usize,
    ) -> Result<ResidentSection<'c>, Error> {
        let op = self
            .junction
            .as_ref()
            .and_then(|j| j.operative.as_ref())
            .ok_or(Error::Shape)?;
        if count > op.births.len() {
            return Err(Error::Shape);
        }
        let mut words = Vec::with_capacity(2 * count.max(1));
        for birth in &op.births[..count] {
            for at in [birth.source, birth.receiving] {
                let at = i64::try_from(at).map_err(invalid)?;
                words.push((at, at));
            }
        }
        if words.is_empty() {
            words.resize(2, (0, 0));
        }
        Ok(self.relation.surface.mount_section_rest(
            &ResidentSectionRest::found(count.max(1), 2, ResidentGrain(0), 64, words)
                .map_err(invalid)?,
        )?)
    }

    fn operative_legacy_map(
        &self,
        map: &ResidentSection<'c>,
        returns: &[Rc<OperativeReturn<'c>>],
        source: usize,
        count: usize,
    ) -> Result<Rc<ResidentSection<'c>>, Error> {
        let surface = self.relation.surface;
        let d = 6 * self.nodes();
        let grain = self
            .junction
            .as_ref()
            .and_then(|j| j.operative.as_ref())
            .ok_or(Error::Shape)?
            .grain;
        let later = returns
            .iter()
            .filter(|r| count > 0 && r.at_cut > source)
            .collect::<Vec<_>>();
        if later.iter().any(|r| r.source_overlap.is_some()) {
            return Err(invalid(
                "source-dependent increment requires its map program",
            ));
        }
        let mut retained = Vec::new();
        let mut pointers = Vec::new();
        for r in &later {
            let (factors, n) = self.resolve_operative_current_factor_prefix(r, count)?;
            for v in [r.ports.lo_device_ptr(), factors.lo_device_ptr(), n as u64] {
                pointers.push((v as i64, v as i64));
            }
            retained.push(factors);
        }
        if pointers.is_empty() {
            pointers.resize(3, (0, 0));
        }
        let table = surface.mount_section_rest(
            &ResidentSectionRest::found(later.len().max(1), 3, ResidentGrain(0), 64, pointers)
                .map_err(invalid)?,
        )?;
        let output = Rc::new(surface.fresh_section(count.max(1), 2 * d, ResidentGrain(0))?);
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_operative_producing_map(
                &lane,
                map,
                &table,
                later.len(),
                d,
                count,
                grain,
                &output,
            )?;
        }
        passage.close(0, &output, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "legacy map source: {:?}",
                receipt.obstruction
            )));
        }
        Ok(output)
    }

    /// The numerical map which produced this exact emission, before its later material return.
    /// Earlier source maps are dependencies of immutable coefficient expressions, not replayed
    /// learning operations. Matrices are released after their last actual decoder consumer.
    pub(super) fn operative_producing_map(
        &self,
        source: usize,
    ) -> Result<Rc<ResidentSection<'c>>, Error> {
        use std::collections::BTreeMap;
        let op = self
            .junction
            .as_ref()
            .and_then(|j| j.operative.as_ref())
            .ok_or(Error::Shape)?;
        if source < op.activated_at || source >= self.history.len() {
            return Err(Error::ForeignOccurrence);
        }
        let count = op.births.partition_point(|b| b.receiving <= source);
        if let Some((_, _, s)) = op
            .recent_producers
            .iter()
            .find(|(at, k, _)| *at == source && *k == count)
        {
            return Ok(Rc::clone(&s.map));
        }
        let Some(program) = &op.program else {
            return self.operative_legacy_map(&op.sections.map, &op.returns, source, count);
        };
        if source < program.at_cut {
            return self.operative_legacy_map(
                &program.map,
                &op.returns[..program.return_count],
                source,
                count,
            );
        }
        let end = op.returns.partition_point(|r| r.at_cut <= source);
        let start = program.return_count;
        if end < start
            || count < program.contact_count
            || count - program.contact_count > program.births.len()
        {
            return Err(Error::Shape);
        }
        let surface = self.relation.surface;
        let d = 6 * self.nodes();
        let mut birth_ptrs = program.births[..count - program.contact_count]
            .iter()
            .map(|b| {
                let p = b.lo_device_ptr() as i64;
                (p, p)
            })
            .collect::<Vec<_>>();
        if birth_ptrs.is_empty() {
            birth_ptrs.push((0, 0));
        }
        let columns = surface.mount_section_rest(
            &ResidentSectionRest::found(birth_ptrs.len(), 1, ResidentGrain(0), 64, birth_ptrs)
                .map_err(invalid)?,
        )?;
        let initial = Rc::new(surface.fresh_section(count.max(1), 2 * d, ResidentGrain(0))?);
        let mut passage = surface.begin_passage(&[vec![]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_operative_map_anchor(
                &lane,
                &program.map,
                &columns,
                program.contact_count,
                count,
                d,
                &initial,
            )?;
        }
        passage.close(0, &initial, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "map anchor: {:?}",
                receipt.obstruction
            )));
        }
        let addresses = self.operative_birth_addresses(count)?;
        let mut last_use = BTreeMap::new();
        let mut legacy_last = BTreeMap::new();
        for i in start..end {
            last_use
                .entry(i)
                .and_modify(|v: &mut usize| *v = (*v).max(i))
                .or_insert(i);
            if let Some(h) = &op.returns[i].source_overlap {
                if h.source >= source
                    || h.source
                        .checked_add(1)
                        .is_none_or(|s| s >= op.returns[i].at_cut)
                {
                    return Err(invalid("cyclic map source"));
                }
                if h.source < program.at_cut {
                    legacy_last.insert(h.source, i);
                } else {
                    let parent = op.returns.partition_point(|r| r.at_cut <= h.source);
                    if parent < start || parent > i {
                        return Err(invalid("map source order"));
                    }
                    last_use
                        .entry(parent)
                        .and_modify(|v: &mut usize| *v = (*v).max(i))
                        .or_insert(i);
                }
            }
        }
        let mut maps = BTreeMap::from([(start, initial)]);
        let mut legacy = BTreeMap::new();
        let history_words = 2 * std::mem::size_of::<i128>() / std::mem::size_of::<i64>() + 1;
        let scratch =
            surface.fresh_section(d / 2, 2 * history_words * count.max(1), ResidentGrain(0))?;
        let rounds = surface.fresh_section(1, d, ResidentGrain(0))?;
        for i in start..end {
            let r = &op.returns[i];
            let source_map = if let Some(h) = &r.source_overlap {
                if h.source < program.at_cut {
                    if !legacy.contains_key(&h.source) {
                        let k = op.births.partition_point(|b| b.receiving <= h.source);
                        legacy.insert(
                            h.source,
                            self.operative_legacy_map(
                                &program.map,
                                &op.returns[..start],
                                h.source,
                                k,
                            )?,
                        );
                    }
                    Some(Rc::clone(&legacy[&h.source]))
                } else {
                    let parent = op.returns.partition_point(|r| r.at_cut <= h.source);
                    Some(Rc::clone(maps.get(&parent).ok_or(Error::Shape)?))
                }
            } else {
                None
            };
            let (factors, factor_count) = self.resolve_operative_current_factor_prefix(r, count)?;
            let output = Rc::new(surface.fresh_section(count.max(1), 2 * d, ResidentGrain(0))?);
            let mut passage = surface.begin_passage(&[vec![]])?;
            {
                let lane = passage.open(0, &[])?;
                surface.record_operative_map_expression(
                    &lane,
                    maps.get(&i).ok_or(Error::Shape)?,
                    source_map
                        .as_ref()
                        .zip(r.source_overlap.as_ref())
                        .map(|(map, h)| (map.as_ref(), h.coefficients.as_ref(), h.count)),
                    &addresses,
                    &r.ports,
                    &factors,
                    count,
                    factor_count,
                    d,
                    op.grain,
                    &output,
                    &scratch,
                    &rounds,
                )?;
            }
            passage.close(0, &output, 64)?;
            let receipt = passage.finish()?.launch()?;
            if !receipt.obstruction.is_empty() {
                return Err(Error::Arithmetic(format!(
                    "map expression: {:?}",
                    receipt.obstruction
                )));
            }
            maps.insert(i + 1, output);
            maps.retain(|node, _| {
                *node == i + 1 || last_use.get(node).is_some_and(|until| *until > i)
            });
            legacy.retain(|node, _| legacy_last.get(node).is_some_and(|until| *until > i));
        }
        maps.remove(&end).ok_or(Error::Shape)
    }
}

impl<'f, 'c> NativeOperativeContactStaging<'f, 'c> {
    pub(super) fn stage_source_return(
        &self,
        returned: Rc<OperativeReturn<'c>>,
        factors: &Rc<ResidentSection<'c>>,
    ) -> Result<Self, Error> {
        let h = returned.source_overlap.as_ref().ok_or(Error::Shape)?;
        if !Rc::ptr_eq(&self.origin, &returned.origin)
            || returned.at_cut != self.field_cut()
            || returned.contact_count != self.births.len()
            || h.source
                .checked_add(1)
                .is_none_or(|s| s >= self.field_cut())
            || h.count > returned.factor_count
        {
            return Err(Error::ForeignOccurrence);
        }
        let surface = self.field.relation.surface;
        let count = self.births.len();
        let d = 6 * self.field.nodes();
        let source = self.field.operative_producing_map(h.source)?;
        let births = self.field.operative_birth_addresses(count)?;
        let next = sections(surface, d, count)?;
        let history_words = 2 * std::mem::size_of::<i128>() / std::mem::size_of::<i64>() + 1;
        let scratch =
            surface.fresh_section(d / 2, 2 * history_words * count.max(1), ResidentGrain(0))?;
        let rounds = surface.fresh_section(1, d, ResidentGrain(0))?;
        let moments =
            surface.fresh_section(1, 2 * ((d / 2) * (d / 2) + d / 2), ResidentGrain(0))?;
        let mut passage = surface.begin_passage(&[vec![], vec![0], vec![1]])?;
        {
            let lane = passage.open(0, &[])?;
            surface.record_operative_map_expression(
                &lane,
                &self.sections.map,
                Some((&source, &h.coefficients, h.count)),
                &births,
                &returned.ports,
                factors,
                count,
                returned.factor_count,
                d,
                self.grain,
                &next.map,
                &scratch,
                &rounds,
            )?;
        }
        passage.close(0, &next.map, 64)?;
        {
            let lane = passage.open(1, &[0])?;
            surface.record_operative_expression_current(
                &lane,
                &self.sections.b,
                &self.sections.bounds,
                returned.b.as_deref(),
                &returned.bounds,
                &rounds,
                count,
                d / 2,
                returned.realization == NativeContactRealization::DyadicDeposit,
                &next.b,
                &next.bounds,
            )?;
        }
        passage.close(1, &next.bounds, 64)?;
        {
            let lane = passage.open(2, &[1])?;
            surface.record_operative_moments(
                &lane,
                d,
                count,
                self.grain,
                next.current(),
                next.moments(),
                &moments,
            )?;
        }
        passage.close(2, &next.moment_bounds, 64)?;
        let receipt = passage.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "source-map return: {:?}",
                receipt.obstruction
            )));
        }
        let program = self.program.clone().unwrap_or_else(|| OperativeMapProgram {
            at_cut: self.field_cut(),
            return_count: self.returns.len(),
            contact_count: count,
            map: Rc::clone(&self.sections.map),
            births: Vec::new(),
        });
        let mut returns = self.returns.clone();
        returns.push(returned);
        Ok(Self {
            field: self.field,
            origin: Rc::new(()),
            grain: self.grain,
            births: self.births.clone(),
            sections: next,
            returns,
            program: Some(program),
        })
    }
}
