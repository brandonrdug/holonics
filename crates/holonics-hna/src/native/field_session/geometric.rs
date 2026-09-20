use super::super::field_geometry::CompiledFieldGeometry;
use super::*;
use holonic_engine::{
    ExactWavePhaseTransport, native_ecology::constitutive_fibre::ResidentNormalEnclosureSection,
};
use std::rc::Rc;

struct GeometricPreparation<'c> {
    layout: Rc<CompiledFieldGeometry>,
    seed: Rc<ResidentNormalEnclosureSection<'c>>,
    held: Vec<bool>,
    receiving_rows: Vec<usize>,
    receiving_held: Vec<bool>,
    output_symbols: usize,
}
impl FieldSessionSpec {
    pub(super) fn geometric_extents(&self) -> Result<(usize, usize, usize)> {
        if !self.region_offsets.is_empty() {
            return Err(invalid(
                "geometric incidence comes from analytic arcs, not text offsets",
            ));
        }
        let geometry = self
            .geometry
            .as_ref()
            .ok_or_else(|| invalid("geometric source chart requires its source geometry"))?
            .compile()?;
        if self.section_symbols > geometry.slot_rows.len()
            || self.context_symbols > geometry.slot_rows.len()
        {
            return Err(invalid(
                "source/receiver part capacity exceeds geometric slot chart",
            ));
        }
        let nodes = self
            .symbols
            .len()
            .checked_add(2)
            .ok_or_else(|| invalid("geometric local width"))?
            / 3;
        let sources = nodes
            .checked_mul(3)
            .ok_or_else(|| invalid("geometric local width"))?;
        let conditions = geometry.condition_complex;
        let features = sources
            .checked_mul(conditions)
            .and_then(|n| n.checked_add(sources)?.checked_add(conditions))
            .ok_or_else(|| invalid("geometric feature width"))?;
        Ok((nodes, conditions, features))
    }
}
impl<'c> NativeFieldSession<'c> {
    fn prepare_geometric(&self, request: &FieldSectionRequest) -> Result<GeometricPreparation<'c>> {
        if request.commit {
            return Err(invalid(
                "geometric receiving cuts use an observed comparison for material update",
            ));
        }
        if request.partial.is_some() && !request.text.is_empty() {
            return Err(invalid("supply text or partial regions, not both"));
        }
        let layout = self
            .compiled_geometry
            .as_ref()
            .ok_or_else(|| invalid("geometric source"))?
            .clone();
        let parts = match &request.partial {
            Some(parts) => parts
                .iter()
                .map(|p| {
                    p.as_ref()
                        .map(|s| {
                            self.chart
                                .alphabet()
                                .symbol_of(s)
                                .ok_or_else(|| invalid("geometric source codec symbol"))
                        })
                        .transpose()
                })
                .collect::<Result<Vec<_>>>()?,
            None => self
                .spec
                .symbols_of(&self.chart, &request.text)?
                .into_iter()
                .map(Some)
                .collect(),
        };
        let output_symbols = request.output_symbols.unwrap_or(parts.len());
        if output_symbols == 0
            || output_symbols > self.spec.section_symbols
            || parts.len() > self.spec.section_symbols
        {
            return Err(invalid("geometric source/receiving aperture"));
        }
        let context = request
            .context
            .iter()
            .map(|s| self.spec.symbols_of(&self.chart, s))
            .collect::<Result<Vec<_>>>()?
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        if context.len() > self.spec.context_symbols {
            return Err(invalid("geometric context aperture"));
        }
        let width = self
            .body
            .roots()
            .checked_mul(6)
            .ok_or_else(|| invalid("geometric source width"))?;
        let n = layout
            .rows
            .checked_mul(width)
            .ok_or_else(|| invalid("geometric source section"))?;
        let mut values = vec![(0i64, 0i64); n];
        let mut held = vec![false; n / 2];
        let symbols = self.spec.symbols.len();
        for (slot, symbol) in context.iter().enumerate() {
            let row = layout.slot_rows[slot];
            values[row * width + 2 * self.chart.coordinates()[symbol.0 as usize]] = (1, 1);
            held[row * (width / 2)..row * (width / 2) + symbols].fill(true);
        }
        let prefix = context.len();
        if prefix
            .checked_add(parts.len().max(output_symbols))
            .is_none_or(|n| n > layout.slot_rows.len())
        {
            return Err(invalid(
                "combined source/context exceeds the geometric receiving chart",
            ));
        }

        let receiving_rows = layout.slot_rows[prefix..prefix + output_symbols].to_vec();
        let mut receiving_held = vec![
            false;
            output_symbols
                .checked_mul(symbols)
                .ok_or_else(|| invalid("geometric receiver mask"))?
        ];
        for (at, symbol) in parts.iter().enumerate() {
            let row = layout.slot_rows[prefix + at];
            if let Some(symbol) = symbol {
                values[row * width + 2 * self.chart.coordinates()[symbol.0 as usize]] = (1, 1);
                if request.partial.is_some() {
                    held[row * (width / 2)..row * (width / 2) + symbols].fill(true);
                    if at < output_symbols {
                        receiving_held[at * symbols..(at + 1) * symbols].fill(true);
                    }
                }
            }
        }
        let raw = self
            .surface
            .mount_section_rest(
                &ResidentSectionRest::found(layout.rows, width, ResidentGrain(0), 64, values)
                    .map_err(invalid)?,
            )
            .map_err(invalid)?;
        let seed = Rc::new(ResidentNormalEnclosureSection::from_points(
            ResidentConstitutiveSection::integers(&raw)?,
            ResidentGrain(self.spec.fractional_bits),
        )?);
        Ok(GeometricPreparation {
            layout,
            seed,
            held,
            receiving_rows,
            receiving_held,
            output_symbols,
        })
    }
    pub(super) fn geometric_request(&mut self, request: &FieldSectionRequest) -> Result<Value> {
        let start = Instant::now();
        let prepared = self.prepare_geometric(request)?;
        if request.retain_comparison && prepared.receiving_held.iter().all(|v| *v) {
            return Err(invalid(
                "retained geometric comparison requires a free receiving coordinate",
            ));
        }
        let generated =
            self.body
                .preview_geometric_rows(&prepared.layout, prepared.seed, &prepared.held)?;
        let placement = prepared.layout.certify_placement(
            self.surface,
            self.body.roots() * 6,
            prepared.layout.condition_complex * 2,
        )?;
        let placement_summary = json!({
            "schema": placement["schema"],
            "rows": placement["rows"],
            "components": placement["components"],
            "condition_components": placement["condition_components"],
            "forward_cells": placement["forward"]["cells"],
            "reverse_cells": placement["reverse"]["cells"],
            "forward_disjoint": placement["forward"]["disjointness"],
            "reverse_disjoint": placement["reverse"]["disjointness"],
            "forward_complete": placement["forward"]["partition_complete"],
            "reverse_complete": placement["reverse"]["partition_complete"],
            "cover": placement["forward"]["cover"],
            "normal_material": placement["normal_material"],
        });
        let rows = generated.gather_phase_rows(
            &prepared.receiving_rows,
            &vec![ExactWavePhaseTransport::identity(); prepared.output_symbols],
            2 * self.spec.symbols.len(),
        )?;
        let received = rows.flatten_components(0..2 * self.spec.symbols.len())?;
        let chart = self.chart.receiver(self.surface)?;
        let selections = received
            .view()
            .read_basis_sections(&chart, prepared.output_symbols)?
            .selections()?;
        let symbols = selections
            .iter()
            .map(|v| self.spec.symbols[v.selected].clone())
            .collect::<Vec<_>>();
        let (text, bytes, decode_error) = match self.spec.codec {
            FieldTextCodec::Utf8Nibbles => {
                let codes = selections
                    .iter()
                    .map(|s| s.selected as u8)
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
                        Err(e) => (None, Some(bytes), Some(e.to_string())),
                    }
                }
            }
            FieldTextCodec::UnicodeScalars => (Some(symbols.join("")), None, None),
            FieldTextCodec::WhitespaceWords => (Some(symbols.join(" ")), None, None),
        };
        let comparison = if request.retain_comparison {
            let id = self.issued_shared;
            let next = id
                .checked_add(1)
                .ok_or_else(|| invalid("shared comparison identifiers exhausted"))?;
            self.retained_shared.insert(
                id,
                RetainedSharedSource {
                    request: request.clone(),
                    held: prepared.receiving_held,
                    output_symbols: prepared.output_symbols,
                    producing_epoch: self.body.epoch(),
                    exposure_pairing: None,
                },
            );
            self.issued_shared = next;
            Some(id)
        } else {
            None
        };
        Ok(
            json!({"schema":"org.holonics.hna.field-section.v1","scope":"analytic geometric incidence, phase participation and whole-field refinement; supplied geometry and symbol receiver",
            "text":text,"output_bytes":bytes,"decode_error":decode_error,"symbols":symbols,"selections":selections,
            "comparison":comparison,"committed":false,"producing_epoch":self.body.epoch(),"source_chart":"geometric-regions",
            "output_symbols":prepared.output_symbols,"geometric_rows":prepared.layout.rows,"refinement_steps":prepared.layout.steps,
            "condition_complex":prepared.layout.condition_complex,"placement":placement_summary,"elapsed_us":start.elapsed().as_micros()}),
        )
    }
    pub(super) fn observe_geometric_source(
        &mut self,
        request: &FieldSectionRequest,
        text: &str,
        step_bits: u32,
        commit: bool,
    ) -> Result<Value> {
        let prepared = self.prepare_geometric(request)?;
        let target = self.spec.symbols_of(&self.chart, text)?;
        if target.len() != prepared.output_symbols {
            return Err(invalid("target does not match geometric receiving extent"));
        }
        let width = prepared.seed.components();
        let mut values = vec![
            (0i64, 0i64);
            prepared
                .layout
                .rows
                .checked_mul(width)
                .ok_or_else(|| invalid("geometric target section"))?
        ];
        let mut observed = vec![false; values.len() / 2];
        let symbols = self.spec.symbols.len();
        for (at, symbol) in target.iter().enumerate() {
            let row = prepared.receiving_rows[at];
            values[row * width + 2 * self.chart.coordinates()[symbol.0 as usize]] = (1, 1);
            observed[row * (width / 2)..row * (width / 2) + symbols].fill(true);
        }
        let raw = self
            .surface
            .mount_section_rest(
                &ResidentSectionRest::found(
                    prepared.layout.rows,
                    width,
                    ResidentGrain(0),
                    64,
                    values,
                )
                .map_err(invalid)?,
            )
            .map_err(invalid)?;
        let target_section = ResidentNormalEnclosureSection::from_points(
            ResidentConstitutiveSection::integers(&raw)?,
            ResidentGrain(self.spec.fractional_bits),
        )?;
        let (returned, covector) = self.body.observe_geometric_rows(
            &prepared.layout,
            prepared.seed,
            &target_section,
            &prepared.held,
            &observed,
            step_bits,
            commit,
        )?;
        let held_disagreements=request.partial.as_ref().map(|parts|parts.iter().take(target.len()).enumerate().filter_map(|(i,p)|p.as_ref().and_then(|value|
            (self.chart.alphabet().symbol_of(value)!=Some(target[i])).then(||json!({"position":i,"given":value,"target":self.spec.symbols[target[i].0 as usize]})))).collect::<Vec<_>>()).unwrap_or_default();
        let mut value = json!({"scope":"geometric-field-source-observation","returned":returned,"held_disagreements":held_disagreements,"anatomy":self.inspect()});
        if !commit {
            value["input_covector"] = json!(
                (0..covector.rows())
                    .map(|i| covector.row(i).and_then(|r| r.inspect()))
                    .collect::<std::result::Result<Vec<_>, _>>()?
            );
        }
        Ok(value)
    }
    pub(super) fn observe_retained_geometric(
        &mut self,
        id: u64,
        text: &str,
        step_bits: u32,
    ) -> Result<Value> {
        let retained = self
            .retained_shared
            .get(&id)
            .ok_or_else(|| invalid("unknown retained geometric comparison"))?
            .clone();
        let prepared = self.prepare_geometric(&retained.request)?;
        if prepared.output_symbols != retained.output_symbols
            || prepared.receiving_held != retained.held
        {
            return Err(invalid("retained geometric receiving chart mismatch"));
        }
        let mut value = self.observe_geometric_source(&retained.request, text, step_bits, true)?;
        self.retained_shared.remove(&id);
        value["comparison"] = json!(id);
        value["producing_epoch"] = json!(retained.producing_epoch);
        value["applied_epoch"] = json!(self.body.epoch());
        Ok(value)
    }
    /// Inspect the complete input pullback without depositing material.
    pub fn compare_geometric_source(
        &mut self,
        request: &FieldSectionRequest,
        text: &str,
        step_bits: u32,
    ) -> Result<Value> {
        if self.spec.source_chart != FieldSourceChart::GeometricRegions {
            return Err(invalid("geometric source chart required"));
        }
        self.observe_geometric_source(request, text, step_bits, false)
    }
}

#[cfg(test)]
mod tests;
