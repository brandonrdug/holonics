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
        if append && old.amplitude_family.is_some() {
            // A free operator delta is outside this declared positive pair family.
            return Err(Error::Shape);
        }
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
                amplitude_family: None,
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
        // A source-only field never appends an occurrence (its `history` stays empty and every
        // return has `at_cut == 0`), so no occurrence decoder can read a current-only return:
        // `operative_before_current`, the response comparison and `has_legacy_current_decoder`
        // all require that history. After a current-only return the complete current factor
        // programme and b are sufficient for every subsequent operation; outstanding
        // comparisons own their producing sections independently. Keeping the already applied
        // delta would duplicate b as an ever-growing event archive, at any factor rank.
        //
        // Retained: (1) an appended factor return (rank growth), whose packet is read by the
        // cold deposit inspectors `inspect_contact_deposit{,_bound}` (deposit.rs), themselves
        // consumed by holonics-hna `inspect_incident_material_return_bounds`; (2) every return on
        // a field that appends occurrences, whose b deltas are read at `at_cut == source` by
        // `operative_before_current` (propagation.rs) and the response comparison
        // (response/comparison.rs), and whose presence disables the legacy alternating-prefix
        // current decoder (`OperativeState::has_legacy_current_decoder`).
        // Earlier retained append packets stay; only this applied current delta is not added.
        let returns = if self.field.relation.source_only() && !append {
            self.returns.clone()
        } else {
            let mut returns = self.returns.clone();
            returns.push(returned);
            returns
        };
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

#[cfg(test)]
mod tests {
    //! CUDA-scoped: run serially under the GPU lock (`--include-ignored --test-threads=1`).
    use super::*;
    use crate::embedding_fiber::ResidentReadout;
    use crate::native_ecology::constitutive_fibre::{
        NativeConstitutiveField, NativeFieldContactOrigin, NativeFieldDeclaredIncidence,
        NativeJunctionSeed, NativePhaseCurrent, ResidentConstitutiveSection,
        ResidentNormalEnclosureSection,
    };
    use crate::resident_section::{ResidentSectionRest, ResidentSurface};

    fn packet<'c>(
        surface: &'c ResidentSurface<'c>,
        rows: usize,
        width: usize,
        values: Vec<i128>,
    ) -> ResidentSection<'c> {
        let words = values
            .into_iter()
            .flat_map(|value| [value as i64, (value >> 64) as i64].map(|word| (word, word)))
            .collect();
        surface
            .mount_section_rest(
                &ResidentSectionRest::found(rows, width, ResidentGrain(0), 64, words).unwrap(),
            )
            .unwrap()
    }

    fn current<'c>(
        surface: &'c ResidentSurface<'c>,
        values: &[i64],
        grain: ResidentGrain,
    ) -> ResidentNormalEnclosureSection<'c> {
        let raw = surface
            .mount_section_rest(
                &ResidentSectionRest::found(
                    1,
                    values.len(),
                    ResidentGrain(0),
                    64,
                    values.iter().map(|value| (*value, *value)).collect(),
                )
                .unwrap(),
            )
            .unwrap();
        ResidentNormalEnclosureSection::from_points(
            ResidentConstitutiveSection::integers(&raw).unwrap(),
            grain,
        )
        .unwrap()
    }

    /// One node, six declared complex contact rows over three ports, rank-0 low-rank factor and
    /// no amplitude family: the unconstrained sparse field the legacy slot chart uses.
    fn declared<'c>(
        surface: &'c ResidentSurface<'c>,
        grain: ResidentGrain,
    ) -> NativeConstitutiveField<'c> {
        let seed = NativeJunctionSeed {
            incoming_admittance: 1,
            held_admittance: 1,
            incoming_transport: NativePhaseCurrent::unit(),
            initial_held: NativePhaseCurrent::zero(),
        };
        let mut field =
            NativeConstitutiveField::found_incident_source_only(surface, vec![seed], grain)
                .unwrap();
        let s = 1i128 << grain.0;
        let coefficients = [
            (0usize, s / 4, s / 8),
            (1, s / 4, -(s / 8)),
            (2, s / 8, s / 4),
            (0, s / 8, s / 16),
            (1, s / 16, -(s / 8)),
            (2, s / 4, s / 8),
        ];
        let mut transpose_rows = Vec::new();
        let mut transpose_values = Vec::new();
        for port in 0..3 {
            transpose_rows.extend([port as i128, port as i128 + 3]);
            for row in [port, port + 3] {
                transpose_values.extend([coefficients[row].1, coefficients[row].2]);
            }
        }
        let incidence = NativeFieldDeclaredIncidence {
            row_offsets: packet(surface, 1, 14, vec![0, 1, 2, 3, 4, 5, 6]),
            columns: packet(
                surface,
                1,
                12,
                coefficients.iter().map(|c| 2 * c.0 as i128).collect(),
            ),
            values: packet(
                surface,
                1,
                24,
                coefficients.iter().flat_map(|c| [c.1, c.2]).collect(),
            ),
            transpose_offsets: packet(surface, 1, 8, vec![0, 2, 4, 6]),
            transpose_rows: packet(surface, 1, 12, transpose_rows),
            transpose_values: packet(surface, 1, 24, transpose_values),
            left: packet(surface, 1, 12, vec![0; 6]),
            right: packet(surface, 1, 24, vec![0; 12]),
            defects: packet(surface, 1, 2, vec![0]),
            rows: 6,
            boundary_components: 6,
            rank: 0,
            nonzeros: 6,
        };
        let origins = (0..6)
            .map(|column| NativeFieldContactOrigin::declared(column, 0, 0))
            .collect();
        field
            .register_declared_incidence(
                incidence,
                packet(surface, 6, 4, vec![0; 12]),
                packet(surface, 1, 4, vec![1, 0]),
                origins,
            )
            .unwrap();
        field
    }

    #[test]
    #[ignore = "requires CUDA; source-only current-only return after a rank-two factor append"]
    fn current_only_return_after_factor_append_retains_no_journal_entry() {
        let readout = ResidentReadout::new().unwrap();
        let surface = ResidentSurface::on(&readout).unwrap();
        let grain = ResidentGrain(32);
        let mut field = declared(&surface, grain);
        let input = current(&surface, &(1..=18).collect::<Vec<i64>>(), grain);
        let gy = current(&surface, &(1..=18).rev().collect::<Vec<i64>>(), grain);
        {
            let source = field.read_current_source().unwrap();
            let action = source
                .action_matrix_free_auto(input.row(0).unwrap(), 128)
                .unwrap();
            let pullback = action.pullback_full_auto(gy.row(0).unwrap(), 128).unwrap();
            let prepared = field
                .prepare_global_action_material_return(
                    &[&pullback],
                    3,
                    NativeContactRealization::DyadicDeposit,
                )
                .unwrap();
            drop(pullback);
            drop(action);
            drop(source);
            field
                .commit_global_action_material_return(prepared)
                .unwrap();
        }
        let appended = field.operative_return_storage().unwrap();
        let (d, k, origin, rank) = {
            let op = field.junction.as_ref().unwrap().operative.as_ref().unwrap();
            let program = op.sections.factor_program.as_ref().unwrap();
            (
                program.boundary_components,
                op.births.len(),
                Rc::clone(&op.origin),
                program.rank,
            )
        };
        assert!(rank > 0, "the fixture must exercise the rank-growth path");
        assert!(
            appended.returns > 0,
            "an appended factor return keeps its packet"
        );
        // A current-only return: factor_count = 0, an exact internal delta and zero radius.
        let delta = (0..k)
            .flat_map(|i| {
                [
                    (i as i128 + 1) << (grain.0 - 3),
                    -((i as i128) << (grain.0 - 4)),
                ]
            })
            .collect::<Vec<_>>();
        let currents = Rc::new(surface.fresh_section(2, 4, ResidentGrain(0)).unwrap());
        let returned = Rc::new(OperativeReturn {
            at_cut: field.occurrence_count(),
            contact_count: k,
            factor_count: 0,
            realization: NativeContactRealization::EnclosedFlow,
            bound_kind: NativeOperativeBoundKind::MatrixAndInternal,
            origin,
            ports: Rc::new(surface.fresh_section(2, 2 * d, ResidentGrain(0)).unwrap()),
            currents: Rc::clone(&currents),
            current_difference_source: None,
            source_overlap: None,
            b: Some(Rc::new(packet(&surface, k, 4, delta.clone()))),
            bounds: Rc::new(packet(&surface, 1, 4, vec![0, 0])),
        });
        let omitted = returned.ports.resident_octets()
            + returned.currents.resident_octets()
            + returned.b.as_ref().unwrap().resident_octets()
            + returned.bounds.resident_octets();
        let read = |s: &ResidentSection<'_>| {
            wides(&surface.detach_section(s, 64).unwrap().intervals).unwrap()
        };
        let b_before = read(
            &field
                .junction
                .as_ref()
                .unwrap()
                .operative
                .as_ref()
                .unwrap()
                .sections
                .b,
        );
        let (sections, origin, returns, program) = {
            let view = field.stage_operative_contacts().unwrap();
            let staged = view.stage_return_using(returned, &currents).unwrap();
            (
                staged.sections,
                staged.origin,
                staged.returns,
                staged.program,
            )
        };
        {
            let op = field.junction.as_mut().unwrap().operative.as_mut().unwrap();
            op.sections = sections;
            op.origin = origin;
            op.returns = returns;
            op.program = program;
        }
        let b_after = read(
            &field
                .junction
                .as_ref()
                .unwrap()
                .operative
                .as_ref()
                .unwrap()
                .sections
                .b,
        );
        let expected = b_before
            .iter()
            .zip(&delta)
            .map(|(b, e)| b + e)
            .collect::<Vec<_>>();
        assert_eq!(
            b_after, expected,
            "the applied current is the complete retained state"
        );
        let after = field.operative_return_storage().unwrap();
        assert_eq!(after.returns, appended.returns);
        assert_eq!(after.total_octets, appended.total_octets);
        let mut wire = Vec::new();
        field.rest(&[], &[]).unwrap().write(&mut wire).unwrap();
        eprintln!(
            "operative return storage: after factor append {} returns / {} bytes; after a \
             current-only return {} returns / {} bytes (the previous rank>0 rule retained {} \
             more bytes in one more return); field rest {} bytes",
            appended.returns,
            appended.total_octets,
            after.returns,
            after.total_octets,
            omitted,
            wire.len()
        );
        let (restored, _, _) =
            NativeConstitutiveField::remount(&surface, field.rest(&[], &[]).unwrap()).unwrap();
        assert_eq!(
            restored.operative_return_storage().unwrap().returns,
            after.returns
        );
        assert_eq!(
            read(
                &restored
                    .junction
                    .as_ref()
                    .unwrap()
                    .operative
                    .as_ref()
                    .unwrap()
                    .sections
                    .b
            ),
            expected
        );
    }
}
