//! Continue the sparse incidence owner by retaining actual material factors and current changes.
use super::*;
impl<'f, 'c> NativeOperativeContactStaging<'f, 'c> {
    pub(super) fn stage_factor_return(
        &self,
        returned: Rc<OperativeReturn<'c>>,
        currents: &Rc<ResidentSection<'c>>,
        image: Option<ResidentNormalEnclosureView<'_, 'c>>,
    ) -> Result<Self, Error> {
        let old = self.sections.factor_program.as_ref().ok_or(Error::Shape)?;
        let d = old.boundary_components;
        let k = old.rows;
        if k != self.births.len()
            || returned.source_overlap.is_some()
            || returned.current_difference_source.is_some()
            || (returned.factor_count != 0 && returned.factor_count != k)
        {
            return Err(Error::Shape);
        }
        if returned.bound_kind() == NativeOperativeBoundKind::FactorBalls
            && (returned.realization != NativeContactRealization::DyadicDeposit
                || returned.b.is_some())
        {
            return Err(Error::Shape);
        }
        let surface = self.field.relation.surface;
        let append = returned.factor_count != 0;
        let next_rank = old
            .rank
            .checked_add(if append { 2 } else { 0 })
            .ok_or(Error::Shape)?;
        let left = if append {
            Rc::new(surface.fresh_section(next_rank, 2 * d, ResidentGrain(0))?)
        } else {
            Rc::clone(&old.left)
        };
        let right = if append {
            Rc::new(surface.fresh_section(next_rank, 4 * k, ResidentGrain(0))?)
        } else {
            Rc::clone(&old.right)
        };
        let defects = if append {
            Rc::new(surface.fresh_section(next_rank, 2, ResidentGrain(0))?)
        } else {
            Rc::clone(&old.defects)
        };
        let next_b = if returned.b.is_some() {
            Rc::new(surface.fresh_section(k, 4, ResidentGrain(0))?)
        } else {
            Rc::clone(&self.sections.b)
        };
        let active_bounds = if returned.bound_kind() == NativeOperativeBoundKind::FactorBalls {
            Rc::new(
                surface.mount_section_rest(
                    &ResidentSectionRest::found(1, 4, ResidentGrain(0), 64, vec![(0, 0); 4])
                        .map_err(|_| Error::Shape)?,
                )?,
            )
        } else {
            Rc::clone(&returned.bounds)
        };
        let bounds = Rc::new(surface.fresh_section(1, 4, ResidentGrain(0))?);
        let mut pass = surface.begin_passage(&[vec![]])?;
        {
            let lane = pass.open(0, &[])?;
            if append {
                surface.record_field_factor_append(
                    &lane,
                    [&old.left, &old.right, &old.defects],
                    [&returned.ports, currents, &active_bounds],
                    old.rank,
                    d,
                    k,
                    self.grain,
                    returned.realization == NativeContactRealization::DyadicDeposit,
                    [&left, &right, &defects],
                )?;
            }
            // A material-only return preserves the current allocation. Copying it into itself
            // is avoided: only its bound is needed and it is unchanged by a D update.
            surface.record_field_factor_current(
                &lane,
                &self.sections.b,
                &self.sections.bounds,
                returned.b.as_deref(),
                &active_bounds,
                image,
                d,
                k,
                &next_b,
                &bounds,
            )?;
        }
        pass.close(0, &bounds, 64)?;
        let receipt = pass.finish()?.launch()?;
        if !receipt.obstruction.is_empty() {
            return Err(Error::Arithmetic(format!(
                "factor return: {:?}",
                receipt.obstruction
            )));
        }
        let program = if append {
            Rc::new(OperativeFactorProgram {
                row_offsets: Rc::clone(&old.row_offsets),
                columns: Rc::clone(&old.columns),
                values: Rc::clone(&old.values),
                transpose_offsets: Rc::clone(&old.transpose_offsets),
                transpose_rows: Rc::clone(&old.transpose_rows),
                transpose_values: Rc::clone(&old.transpose_values),
                left,
                right,
                defects,
                rows: k,
                boundary_components: d,
                rank: next_rank,
                nonzeros: old.nonzeros,
            })
        } else {
            Rc::clone(old)
        };
        let sections = Rc::new(OperativeSections {
            map: Rc::clone(&self.sections.map),
            b: next_b,
            bounds,
            covariance: std::cell::OnceCell::new(),
            aggregate: surface.fresh_section(1, 2 * d, ResidentGrain(0))?,
            moment_bounds: surface.fresh_section(1, 8, ResidentGrain(0))?,
            factor_program: Some(program),
        });
        sections.refresh_factor_aggregate(surface, self.grain)?;
        let mut returns = self.returns.clone();
        returns.push(returned);
        Ok(Self {
            field: self.field,
            origin: Rc::new(()),
            grain: self.grain,
            births: self.births.clone(),
            declared_origins: self.declared_origins.clone(),
            sections,
            returns,
            program: None,
        })
    }
}
