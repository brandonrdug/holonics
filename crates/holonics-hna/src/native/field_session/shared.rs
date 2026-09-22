//! A complete source supplies overlapping receiving regions to one shared native field law.
//! Offsets belong to the declared incidence chart; symbols remain exterior unit-basis codewords.
use super::*;
use holonic_engine::native_ecology::constitutive_fibre::{
    ResidentHeldSection, ResidentNormalInput,
};

struct SharedPreparation<'c> {
    input: Option<ResidentSection<'c>>,
    conditions: Option<ResidentSection<'c>>,
    given: ResidentSection<'c>,
    held: Vec<bool>,
    destinations: Vec<usize>,
    output_symbols: usize,
    center: std::ops::Range<usize>,
}

impl FieldSessionSpec {
    pub(super) fn shared_extents(&self) -> Result<(usize, usize, usize)> {
        if self.region_offsets.is_empty() || !self.region_offsets.contains(&0) {
            return Err(invalid(
                "shared regions require explicit incidence offsets including zero",
            ));
        }
        let mut unique = self.region_offsets.clone();
        unique.sort_unstable();
        unique.dedup();
        if unique.len() != self.region_offsets.len() {
            return Err(invalid("duplicate region incidence offset"));
        }
        let width = self
            .symbols
            .len()
            .checked_add(2)
            .and_then(|n| n.checked_mul(unique.len()))
            .ok_or_else(|| invalid("local region extent"))?;
        let nodes = width
            .checked_add(2)
            .ok_or_else(|| invalid("local field extent"))?
            / 3;
        let features = nodes
            .checked_mul(6)
            .and_then(|n| n.checked_add(1))
            .ok_or_else(|| invalid("shared feature extent"))?;
        Ok((nodes, 1, features))
    }
}

impl<'c> NativeFieldSession<'c> {
    fn prepare_shared(&self, request: &FieldSectionRequest) -> Result<SharedPreparation<'c>> {
        if request.commit {
            return Err(invalid(
                "shared regions are receiving cuts at one field state; use observe-field-source, or retain this cut's comparison, for a complete source/target update",
            ));
        }
        if request.partial.is_some() && !request.text.is_empty() {
            return Err(invalid("supply text or partial regions, not both"));
        }
        let partial =
            match &request.partial {
                Some(parts) => {
                    parts
                        .iter()
                        .map(|p| {
                            p.as_ref()
                                .map(|s| {
                                    self.presentation.chart.alphabet().symbol_of(s).ok_or_else(|| {
                                invalid("partial region must name one declared codec symbol")
                            })
                                })
                                .transpose()
                        })
                        .collect::<Result<Vec<_>>>()?
                }
                None => self
                    .presentation
                    .spec
                    .symbols_of(&self.presentation.chart, &request.text)?
                    .into_iter()
                    .map(Some)
                    .collect(),
            };
        let output_symbols = request.output_symbols.unwrap_or(partial.len());
        if output_symbols == 0
            || output_symbols > self.presentation.spec.section_symbols
            || partial.len() > self.presentation.spec.section_symbols
        {
            return Err(invalid(
                "source/receiver exceeds its declared section aperture",
            ));
        }
        let context = request
            .context
            .iter()
            .map(|s| {
                self.presentation
                    .spec
                    .symbols_of(&self.presentation.chart, s)
            })
            .collect::<Result<Vec<_>>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        if context.len() > self.presentation.spec.context_symbols {
            return Err(invalid("context exceeds its declared source aperture"));
        }
        let prefix = context.len();
        let mut source = context.into_iter().map(Some).collect::<Vec<_>>();
        source.extend(partial.iter().copied());
        source.resize(prefix + partial.len().max(output_symbols), None);
        let symbols = self.presentation.spec.symbols.len();
        let local = 6 * self.presentation.spec.shared_extents()?.0;
        let center_slot = self
            .presentation
            .spec
            .region_offsets
            .iter()
            .position(|x| *x == 0)
            .unwrap();
        let center_start = 2 * center_slot * (symbols + 2);
        let center = center_start..center_start + 2 * symbols;
        let global_width = output_symbols
            .checked_mul(2)
            .and_then(|n| n.checked_mul(symbols))
            .ok_or_else(|| invalid("receiving extent"))?;
        let mut given = vec![(0i64, 0i64); global_width];
        let mut held = vec![false; global_width / 2];
        let mut destinations = Vec::new();
        for i in 0..output_symbols {
            if let Some(Some(symbol)) = partial.get(i) {
                given[2
                    * (i * symbols + self.presentation.chart.coordinates()[symbol.0 as usize])] =
                    (1, 1);
            }
            let fixed = request.partial.is_some() && partial.get(i).is_some_and(Option::is_some);
            held[i * symbols..(i + 1) * symbols].fill(fixed);
            if !fixed {
                destinations.push(i);
            }
        }
        let mut rows = vec![
            (0i64, 0i64);
            local
                .checked_mul(destinations.len())
                .ok_or_else(|| invalid("region packet extent"))?
        ];
        for (row, destination) in destinations.iter().enumerate() {
            let origin = prefix + destination;
            for (slot, offset) in self.presentation.spec.region_offsets.iter().enumerate() {
                let at = origin.checked_add_signed(*offset);
                let active = at.is_some_and(|at| at < source.len());
                let observed = at.and_then(|at| source.get(at)).copied().flatten();
                let start = row * local + 2 * slot * (symbols + 2);
                if let Some(symbol) = observed {
                    rows[start + 2 * self.presentation.chart.coordinates()[symbol.0 as usize]] =
                        (1, 1);
                }
                let a = i64::from(active);
                let o = i64::from(observed.is_some());
                rows[start + 2 * symbols] = (a, a);
                rows[start + 2 * (symbols + 1)] = (o, o);
            }
        }
        let mount = |rows, width, values| {
            self.surface
                .mount_section_rest(
                    &ResidentSectionRest::found(rows, width, ResidentGrain(0), 64, values)
                        .map_err(invalid)?,
                )
                .map_err(invalid)
        };
        let given = mount(1, global_width, given)?;
        let (input, conditions) = if destinations.is_empty() {
            (None, None)
        } else {
            let count = destinations.len();
            (
                Some(mount(count, local, rows)?),
                Some(mount(
                    count,
                    3,
                    (0..count).flat_map(|_| [(1, 1), (0, 0), (1, 1)]).collect(),
                )?),
            )
        };
        Ok(SharedPreparation {
            input,
            conditions,
            given,
            held,
            destinations,
            output_symbols,
            center,
        })
    }

    pub(super) fn shared_request(&mut self, request: &FieldSectionRequest) -> Result<Value> {
        let start = Instant::now();
        let prepared = self.prepare_shared(request)?;
        // Retention is the shared chart's producing cut: the operands that built these rows are
        // kept so their recorded target can arrive later, here or after reopen, exactly once.
        if request.retain_comparison && prepared.destinations.is_empty() {
            return Err(invalid(
                "a retained comparison requires at least one free receiving position",
            ));
        }
        let grain = ResidentGrain(self.presentation.spec.fractional_bits);
        let given =
            ResidentNormalInput::from(ResidentConstitutiveCurrent::integers(&prepared.given)?)
                .enclosure(self.surface, grain)?;
        let generation = Instant::now();
        let received =
            if let (Some(input), Some(conditions)) = (&prepared.input, &prepared.conditions) {
                let output = self.body.preview_field_rows(
                    ResidentConstitutiveSection::integers(input)?,
                    ResidentConstitutiveSection::rationals(conditions)?,
                )?;
                let full = output.scatter_components(
                    prepared.center.clone(),
                    &prepared.destinations,
                    prepared.output_symbols,
                )?;
                ResidentHeldSection::found(given.view(), &prepared.held)?.receive(full.view())?
            } else {
                given
            };
        let generation_us = generation.elapsed().as_micros();
        let chart = self.presentation.chart.receiver(self.surface)?;
        let selections = received
            .view()
            .read_basis_sections(&chart, prepared.output_symbols)?
            .selections()?;
        let symbols = selections
            .iter()
            .map(|r| self.presentation.spec.symbols[r.selected].clone())
            .collect::<Vec<_>>();
        let (text, bytes, decode_error) = match self.presentation.spec.codec {
            FieldTextCodec::Utf8Nibbles => {
                let codes = selections
                    .iter()
                    .map(|r| r.selected as u8)
                    .collect::<Vec<_>>();
                if codes.len() % 2 != 0 {
                    (None, None, Some("odd nibble receiving extent".to_owned()))
                } else {
                    let bytes = codes
                        .chunks_exact(2)
                        .map(|p| (p[0] << 4) | p[1])
                        .collect::<Vec<_>>();
                    match String::from_utf8(bytes.clone()) {
                        Ok(text) => (Some(text), Some(bytes), None),
                        Err(error) => (None, Some(bytes), Some(error.to_string())),
                    }
                }
            }
            FieldTextCodec::UnicodeScalars => (Some(symbols.join("")), None, None),
            FieldTextCodec::WhitespaceWords => (Some(symbols.join(" ")), None, None),
        };
        let comparison = if request.retain_comparison {
            let id = self.presentation.issued_shared;
            self.presentation.issued_shared = id
                .checked_add(1)
                .ok_or_else(|| invalid("shared-source comparison identifiers exhausted"))?;
            self.presentation.retained_shared.insert(
                id,
                RetainedSharedSource {
                    request: request.clone(),
                    held: prepared.held.clone(),
                    output_symbols: prepared.output_symbols,
                    producing_epoch: self.body.epoch(),
                    exposure_pairing: None,
                },
            );
            Some(id)
        } else {
            None
        };
        Ok(
            json!({"schema":"org.holonics.hna.field-section.v1","scope":"shared-field receiving section; supplied local incidence and shared constitutive material",
            "text":text,"output_bytes":bytes,"decode_error":decode_error,"symbols":symbols,"selections":selections,
            "comparison":comparison,"committed":false,"producing_epoch":self.body.epoch(),
            "output_symbols":prepared.output_symbols,"generated_positions":prepared.destinations,
            "source_chart":"shared-regions","local_complex":self.presentation.spec.shared_extents()?.0*3,
            "generation_us":generation_us,"elapsed_us":start.elapsed().as_micros(),
            "selection_bound":selections.first().map(|v|v.score_radius.clone())}),
        )
    }

    /// Observe actual source/target regions at the current producing material. Targets are
    /// separate from the source preparation and never determine its neighborhood or inputs.
    pub fn observe_source(
        &mut self,
        request: &FieldSectionRequest,
        text: &str,
        step_bits: u32,
    ) -> Result<Value> {
        if self.presentation.spec.source_chart == FieldSourceChart::GeometricRegions {
            return self.observe_geometric_source(request, text, step_bits, true);
        }
        if self.presentation.spec.source_chart != FieldSourceChart::SharedRegions {
            return Err(invalid("observe-field-source requires shared-regions"));
        }
        let prepared = self.prepare_shared(request)?;
        self.observe_prepared(&prepared, request, text, step_bits)
    }

    /// Apply one retained comparison exactly once, in this process or after reopen. The retained
    /// request re-prepares the producing rows and must agree with the receiving face it was
    /// retained at; the epoch that produced the cut and the epoch that applies it are both
    /// reported, because a shared-source update acts at the material current when it arrives.
    pub(super) fn observe_retained_source(
        &mut self,
        id: u64,
        text: &str,
        step_bits: u32,
    ) -> Result<Value> {
        let retained = self
            .presentation
            .retained_shared
            .get(&id)
            .ok_or_else(|| invalid("unknown retained shared-source comparison"))?
            .clone();
        let prepared = self.prepare_shared(&retained.request)?;
        if prepared.held != retained.held || prepared.output_symbols != retained.output_symbols {
            return Err(invalid(
                "retained comparison operands disagree with their re-prepared receiving face",
            ));
        }
        let mut returned = self.observe_prepared(&prepared, &retained.request, text, step_bits)?;
        self.presentation.retained_shared.remove(&id);
        returned["comparison"] = json!(id);
        returned["producing_epoch"] = json!(retained.producing_epoch);
        returned["applied_epoch"] = json!(self.body.epoch());
        returned["anatomy"] = self.inspect();
        Ok(returned)
    }

    fn observe_prepared(
        &mut self,
        prepared: &SharedPreparation<'c>,
        request: &FieldSectionRequest,
        text: &str,
        step_bits: u32,
    ) -> Result<Value> {
        let start = Instant::now();
        let target = self
            .presentation
            .spec
            .symbols_of(&self.presentation.chart, text)?;
        if target.len() != prepared.output_symbols {
            return Err(invalid(
                "target does not match the requested receiving extent",
            ));
        }
        let held_disagreements=request.partial.as_ref().map(|parts|parts.iter().take(target.len()).enumerate()
            .filter_map(|(i,value)|value.as_ref().and_then(|value|(self.presentation.chart.alphabet().symbol_of(value)!=Some(target[i]))
                .then(||json!({"position":i,"given":value,"target":self.presentation.spec.symbols[target[i].0 as usize]})))).collect::<Vec<_>>()).unwrap_or_default();
        if prepared.destinations.is_empty() {
            return Ok(
                json!({"scope":"shared-field-source-observation","rows":0,"parameter_update":"zero: all receiving positions supplied","held_disagreements":held_disagreements,"anatomy":self.inspect()}),
            );
        }
        let local = 6 * self.presentation.spec.shared_extents()?.0;
        let mut values = vec![(0i64, 0i64); local * prepared.destinations.len()];
        for (row, i) in prepared.destinations.iter().enumerate() {
            values[row * local
                + prepared.center.start
                + 2 * self.presentation.chart.coordinates()[target[*i].0 as usize]] = (1, 1);
        }
        let target = self
            .surface
            .mount_section_rest(
                &ResidentSectionRest::found(
                    prepared.destinations.len(),
                    local,
                    ResidentGrain(0),
                    64,
                    values,
                )
                .map_err(invalid)?,
            )
            .map_err(invalid)?;
        let mut mask = vec![true; local / 2];
        mask[prepared.center.start / 2..prepared.center.end / 2].fill(false);
        let returned = self.body.observe_field_rows(
            ResidentConstitutiveSection::integers(prepared.input.as_ref().unwrap())?,
            ResidentConstitutiveSection::rationals(prepared.conditions.as_ref().unwrap())?,
            ResidentConstitutiveSection::integers(&target)?,
            &mask,
            step_bits,
        )?;
        Ok(
            json!({"scope":"shared-field-source-observation","returned":returned,"held_disagreements":held_disagreements,"elapsed_us":start.elapsed().as_micros(),"anatomy":self.inspect()}),
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn spec() -> FieldSessionSpec {
        FieldSessionSpec {
            symbols: (0..16).map(|n| format!("{n:x}")).collect(),
            section_symbols: 4096,
            context_symbols: 4096,
            region_offsets: vec![-1, 0, 1],
            source_chart: FieldSourceChart::SharedRegions,
            geometry: None,
            incident: None,
            generator: None,
            codec: FieldTextCodec::Utf8Nibbles,
            fractional_bits: 48,
        }
    }
    fn partial(text: &str, hidden: usize) -> FieldSectionRequest {
        let mut parts = text
            .as_bytes()
            .iter()
            .flat_map(|b| [Some(format!("{:x}", b >> 4)), Some(format!("{:x}", b & 15))])
            .collect::<Vec<_>>();
        parts[2 * hidden] = None;
        parts[2 * hidden + 1] = None;
        FieldSectionRequest {
            text: String::new(),
            partial: Some(parts),
            output_symbols: None,
            context: vec![],
            incident_preparation: None,
            commit: false,
            retain_comparison: false,
        }
    }
    #[test]
    fn coefficient_shape_is_independent_of_the_complete_source_aperture() {
        let mut s = spec();
        let small = s.extents().unwrap();
        s.section_symbols = 1_000_000;
        s.context_symbols = 2_000_000;
        assert_eq!(s.extents().unwrap(), small);
        assert_eq!(small, (18, 1, 109));
        s.region_offsets = vec![-1, 1];
        assert!(s.chart().is_err());
        s.region_offsets = vec![0, 0];
        assert!(s.chart().is_err());
    }
    #[test]
    #[ignore = "requires CUDA; complete source observation updates shared material and reopens the same receiving face"]
    fn shared_source_updates_and_reopens_without_a_position_sized_model() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("shared.session");
        let request = partial("faces carry current", 6);
        let expected = with_field_session(&spec(), |s| {
            let before = s.inspect_current()?;
            assert!(s.observe_source(&request, "short", 1).is_err());
            assert_eq!(s.inspect_current()?, before);
            let r = s.observe_source(&request, "faces carry current", 1)?;
            assert_eq!(r["returned"]["rows"], 2);
            let after = s.inspect_current()?;
            assert_ne!(before["reaction"], after["reaction"]);
            assert_eq!(before["material"], after["material"]);
            let output = s.request(&request)?;
            assert_eq!(output["output_symbols"], 38);
            assert_eq!(output["generated_positions"], json!([12, 13]));
            assert_eq!(output["symbols"][0], "6");
            s.checkpoint(&path, &HnaStreamState::default())?;
            Ok(output)
        })
        .unwrap();
        NativeFieldSavedSession::open(&path)
            .unwrap()
            .with_session(|s, _| {
                let actual = s.request(&request)?;
                for k in [
                    "text",
                    "output_bytes",
                    "symbols",
                    "selections",
                    "producing_epoch",
                    "generated_positions",
                    "selection_bound",
                ] {
                    assert_eq!(actual[k], expected[k], "{k}");
                }
                Ok(())
            })
            .unwrap();
    }
    #[test]
    #[ignore = "requires CUDA; a retained shared-source comparison survives reopen and applies exactly once"]
    fn retained_shared_comparison_applies_once_after_reopen() {
        let dir = tempfile::tempdir().unwrap();
        let path = dir.path().join("retained.session");
        let mut request = partial("faces carry current", 6);
        request.retain_comparison = true;
        let (before, produced) = with_field_session(&spec(), |s| {
            let produced = s.request(&request)?;
            assert_eq!(produced["comparison"], 0);
            assert_eq!(s.inspect()["retained_shared"], json!([0]));
            // The comparison is retained, not applied: this cut's material is untouched.
            let before = s.inspect_current()?;
            s.checkpoint(&path, &HnaStreamState::default())?;
            Ok((before, produced))
        })
        .unwrap();
        NativeFieldSavedSession::open(&path)
            .unwrap()
            .with_session(|s, _| {
                assert_eq!(s.retained_shared_comparisons(), [0]);
                assert!(s.observe(1, "faces carry current", 1).is_err());
                assert!(s.observe(0, "short", 1).is_err());
                assert_eq!(s.inspect_current()?, before);
                let returned = s.observe(0, "faces carry current", 1)?;
                assert_eq!(returned["comparison"], 0);
                assert_eq!(returned["producing_epoch"], produced["producing_epoch"]);
                assert_eq!(returned["returned"]["rows"], 2);
                assert_ne!(s.inspect_current()?["reaction"], before["reaction"]);
                assert!(s.observe(0, "faces carry current", 1).is_err());
                assert_eq!(s.retained_shared_comparisons(), Vec::<u64>::new());
                Ok(())
            })
            .unwrap();
    }
    #[test]
    #[ignore = "requires CUDA; fixed source disagreements are reported rather than trained as invented observations"]
    fn completely_observed_source_reports_a_conflict_without_deposition() {
        with_field_session(&spec(), |s| {
            let request = FieldSectionRequest {
                text: String::new(),
                partial: Some(vec![Some("6".into()), Some("1".into())]),
                output_symbols: None,
                context: vec![],
                incident_preparation: None,
                commit: false,
                retain_comparison: false,
            };
            let before = s.inspect_current()?;
            assert_eq!(s.request(&request)?["text"], "a");
            let result = s.observe_source(&request, "b", 1)?;
            assert_eq!(result["held_disagreements"].as_array().unwrap().len(), 1);
            assert_eq!(s.inspect_current()?, before);
            Ok(())
        })
        .unwrap();
    }
}
