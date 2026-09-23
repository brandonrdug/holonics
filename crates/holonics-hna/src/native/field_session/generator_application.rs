//! Ordered source and shared phase reception on the fixed generator body.
use super::boundary::BoundaryMaterial;
use super::incident_encoder::IncidentEncoder;
use super::incident_receiver::phase::GeneratorTextReceiver;
use super::*;
use crate::native::{
    GeneratorIncidentFieldSpec, GeneratorPhaseReceiverBinding, GeneratorSourceBinding,
    GeneratorSourceContact, GeneratorSourceContactKind,
};
use holonic_engine::native_ecology::constitutive_fibre::BoundaryMaterialSeed;
use holonic_engine::resident_section::SeriesAperture;
use std::rc::Rc;
mod codec;
#[cfg(test)]
mod deposition_probe;
mod rest;
#[cfg(test)]
mod tests;
pub(super) use rest::GeneratorPresentationRest;

/// The source and receiving clocks are declared boundaries of one fixed machine. The last
/// receiving row supplies termination at the largest admitted text length; it is not another
/// independently learned support parameter.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GeneratorSessionOptions {
    pub field: GeneratorIncidentFieldSpec,
    pub source: GeneratorSourceBinding,
    pub receiver: GeneratorPhaseReceiverBinding,
    pub material_seed: u64,
}
/// An outstanding generator comparison, as the session holds it. The body retains the source
/// Holon as per-symbol phase-weighted sums (`C_(a,i)`, per-port `D_(p,a,i)`), fixed in `N`, and
/// reads it through the contemporary encoder table when it is observed. The session keeps no
/// resident operand and no per-cell or per-edge relation: only the clock origin, the passage
/// length and the alphabet binding — each admitted symbol's occurrence count, which the encoder's
/// normal law needs (one observation per occurrence) and which is `|A|` words, fixed in `N`.
pub(super) struct GeneratorPending {
    start: u64,
    cells: usize,
    /// Occurrences of each codec identity `0..|A|` in the passage; `|A|` at request time.
    symbol_counts: Vec<usize>,
    /// The presentation's fixed-size record of the request (extents, epoch, a digest of the held
    /// text) and the exterior exposure pairing, when one was attached.
    pub(super) record: GeneratorRetainedRecord,
}

/// What the presentation keeps of an outstanding generator request: extents and a digest, fixed
/// in the passage length. The request text itself is not retained; an exposure pairing is
/// checked against the digest of the held text it names.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GeneratorRetainedRecord {
    pub request_extent: usize,
    pub response_aperture: usize,
    pub output_symbols: usize,
    pub producing_epoch: u64,
    /// Leading held partial parts of the request (the exterior pairing's held extent).
    pub held_parts: usize,
    /// SHA-256 (hex) of the concatenated held partial text.
    pub held_text_sha256: String,
    /// The exterior exposure pairing as digests: the driver owns the request text and events
    /// for resume and confirms them against these (`confirm_exposure_pairing`).
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub exposure_pairing: Option<GeneratorExposureDigest>,
}

/// A generator comparison's exterior exposure pairing, fixed size: the family, the response
/// extent, and digests of the request text and its sorted event coordinates.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct GeneratorExposureDigest {
    pub family: crate::alpha::exposure::ExposureFamily,
    pub response_symbols: usize,
    pub request_text_sha256: String,
    pub request_events_sha256: String,
}

impl GeneratorExposureDigest {
    pub(super) fn of(pairing: &super::RetainedExposurePairing) -> Self {
        Self {
            family: pairing.family.clone(),
            response_symbols: pairing.response_symbols,
            request_text_sha256: held_text_digest(&pairing.request_text),
            request_events_sha256: events_digest(&pairing.request_events),
        }
    }
    /// Whether a driver-held pairing is the one this comparison recorded.
    pub(super) fn confirms(&self, pairing: &super::RetainedExposurePairing) -> bool {
        *self == Self::of(pairing)
    }
}

pub(super) fn events_digest(events: &[u64]) -> String {
    held_text_digest(
        &events
            .iter()
            .map(u64::to_string)
            .collect::<Vec<_>>()
            .join(","),
    )
}

pub(super) fn held_text_digest(text: &str) -> String {
    use sha2::{Digest, Sha256};
    Sha256::digest(text.as_bytes())
        .iter()
        .map(|byte| format!("{byte:02x}"))
        .collect()
}

impl GeneratorRetainedRecord {
    fn from_request(
        request: &FieldSectionRequest,
        preparation: &IncidentPreparation,
        producing_epoch: u64,
    ) -> Self {
        let held = request
            .partial
            .as_ref()
            .map(|parts| {
                parts
                    .iter()
                    .take_while(|part| part.is_some())
                    .map(|part| part.as_deref().unwrap_or_default())
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        Self {
            request_extent: preparation.request_extent,
            response_aperture: preparation.response_aperture,
            output_symbols: preparation.request_extent + preparation.response_aperture,
            producing_epoch,
            held_parts: held.len(),
            held_text_sha256: held_text_digest(&held.concat()),
            exposure_pairing: None,
        }
    }

    /// The generator branch of the exposure-pairing check, on the fixed record.
    pub(super) fn validate_pairing(
        &self,
        pairing: &super::RetainedExposurePairing,
        spec: &FieldSessionSpec,
    ) -> Result<()> {
        if pairing.family.provider.is_empty()
            || pairing.family.record_group.is_empty()
            || pairing.request_events.is_empty()
            || pairing.request_events.contains(&0)
            || pairing.request_events.windows(2).any(|p| p[0] >= p[1])
            || pairing.response_symbols == 0
            || held_text_digest(&pairing.request_text) != self.held_text_sha256
            || self.response_aperture != pairing.response_symbols
            || spec.response_aperture()? != pairing.response_symbols
            || self.output_symbols != self.request_extent + self.response_aperture
        {
            return Err(invalid(
                "generator retained exposure source/receiver mismatch",
            ));
        }
        Ok(())
    }
}
/// Read-only operands of an outstanding generator comparison.
#[cfg_attr(not(test), allow(dead_code))]
impl GeneratorPending {
    /// First source clock event and passage length at which the request was read.
    pub(super) fn source_clock(&self) -> (u64, usize) {
        (self.start, self.cells)
    }
    /// The alphabet binding: occurrence count per codec identity at request time.
    pub(super) fn symbol_counts(&self) -> &[usize] {
        &self.symbol_counts
    }
    /// Host words this comparison holds beyond its clock: `|A|`, fixed in `N`.
    pub(super) fn pending_relation_words(&self) -> usize {
        self.symbol_counts.len()
    }
}
pub(super) struct GeneratorPresentation<'c> {
    encoder: IncidentEncoder<'c>,
    receiver: GeneratorTextReceiver<'c>,
    pub(super) pending: BTreeMap<u64, GeneratorPending>,
    next_event: u64,
    /// The target-independent receiving binding every comparison is read through.
    receiver_binding: GeneratorPhaseReceiverBinding,
    /// Exterior observer memory for readings across observations; never read by the machine.
    pub(super) readings: super::measurement::GeneratorReadingMemory,
}

/// The one-cut operands of an observe, kept only until its readings are taken.
pub(super) struct GeneratorObserveCut<'c> {
    pub faces: super::incident_receiver::phase::GeneratorRatioFaces<'c>,
    pub target: Vec<usize>,
    /// Per-symbol pooled occurrence counts of the encoder return: the collapse the observe
    /// performs on the source passage (blocks of the Landauer erasure reading).
    pub pooled_symbol_counts: Vec<usize>,
    /// How the target Holon was read: `word` (same machine, same cut), `moment` (a target
    /// symbol outside the request's alphabet), or `none` (empty target).
    pub target_holon: &'static str,
}

fn receiver_boundary<'c>(
    surface: &'c ResidentSurface<'c>,
    spec: &FieldSessionSpec,
    class_count: Option<usize>,
) -> Result<BoundaryMaterial<'c>> {
    let options = spec
        .generator
        .as_ref()
        .ok_or_else(|| invalid("generator session options"))?;
    let mut receiver_spec = spec.clone();
    if let Some(count) = class_count {
        if count == 0 || count > spec.symbols.len() {
            return Err(invalid("generator producing codec extent"));
        }
        receiver_spec.symbols.truncate(count);
    }
    let local = options
        .receiver
        .ports
        .len()
        .checked_mul(6)
        .ok_or_else(|| invalid("generator receiving chart extent"))?;
    BoundaryMaterial::found(
        surface,
        receiver_spec.chart()?,
        local,
        1,
        ResidentGrain(spec.fractional_bits),
        BoundaryMaterialSeed::new(options.material_seed, spec.fractional_bits),
    )
}

/// The passage's directed contacts of the kinds the binding declares a condition port for. A
/// contact of an undeclared kind has no port to enter, so it is not part of this source relation.
fn source_contacts(
    preparation: &IncidentPreparation,
    kinds: &[GeneratorSourceContactKind],
) -> Vec<GeneratorSourceContact> {
    preparation
        .contacts
        .iter()
        .map(|c| GeneratorSourceContact {
            from: c.from_cell,
            to: c.to_cell,
            kind: match c.kind {
                IncidentContactKind::IntraPart => GeneratorSourceContactKind::IntraPart,
                IncidentContactKind::DirectJoin { .. } => GeneratorSourceContactKind::DirectJoin,
                IncidentContactKind::RecordedParent { .. } => {
                    GeneratorSourceContactKind::RecordedParent
                }
                IncidentContactKind::RecordedReply { .. } => {
                    GeneratorSourceContactKind::RecordedReply
                }
            },
        })
        .filter(|c| kinds.contains(&c.kind))
        .collect()
}

/// Reading only (never in the covector): the machine's ring winding at receiving phase `j`: the first receiving port's ring, action
/// exponent `origin + j * step`, full lifted turns `floor(W e / P)` when its closure witness
/// `P` (with lifted winding `W` per period) exists; otherwise zero without a witness.
pub(super) fn receiving_branch(
    options: &GeneratorSessionOptions,
    row: usize,
) -> Result<(i64, bool)> {
    let machine = options.field.machine.compile().map_err(invalid)?;
    let Some(port) = options.receiver.ports.first() else {
        return Ok((0, false));
    };
    let site = machine
        .sites()
        .iter()
        .find(|site| site.id() == port.site_id)
        .ok_or_else(|| invalid("receiving port site"))?;
    let exponent = site
        .phase_origin_exponent()
        .checked_add(port.origin_exponent)
        .and_then(|v| port.step_exponent.checked_mul(row as i64)?.checked_add(v))
        .ok_or_else(|| invalid("receiving exponent"))?;
    let Some(period) = site.closure() else {
        return Ok((0, false));
    };
    let Ok(winding) = site.phase().lifted_winding(period) else {
        return Ok((0, false));
    };
    let turns = (i128::from(winding.lifted) * i128::from(exponent)).div_euclid(period as i128);
    Ok((i64::try_from(turns).map_err(invalid)?, true))
}

impl<'c> NativeFieldSession<'c> {
    pub(super) fn found_generator(
        surface: &'c ResidentSurface<'c>,
        spec: &FieldSessionSpec,
    ) -> Result<Self> {
        let chart = spec.chart()?;
        let options = spec
            .generator
            .as_ref()
            .ok_or_else(|| invalid("generator session options"))?;
        let grain = ResidentGrain(spec.fractional_bits);
        let body = NativeCoupledBody::found_generator_field(surface, options.field.clone(), grain)?;
        let source_width = options
            .source
            .injection_sites
            .len()
            .checked_mul(3)
            .ok_or_else(|| invalid("generator source material extent"))?;
        let seed = BoundaryMaterialSeed::new(options.material_seed, grain.0);
        let source_maps = seed
            .initial_maps(spec.symbols.len(), source_width)
            .map_err(invalid)?;
        let encoder = IncidentEncoder::found_with_seed(surface, &source_maps, grain, seed)?;
        let receiver =
            GeneratorTextReceiver::found(surface, receiver_boundary(surface, spec, None)?)?;
        Ok(Self {
            surface,
            body,
            incident: None,
            generator: Some(GeneratorPresentation {
                encoder,
                receiver,
                pending: BTreeMap::new(),
                next_event: 0,
                receiver_binding: options.receiver.clone(),
                readings: Default::default(),
            }),
            presentation: FieldTextPresentation {
                spec: spec.clone(),
                chart,
                compiled_geometry: None,
                pending_extents: BTreeMap::new(),
                retained_shared: BTreeMap::new(),
                issued_shared: 0,
                exposure: None,
            },
        })
    }

    pub(super) fn generator_request(&mut self, request: &FieldSectionRequest) -> Result<Value> {
        let started = Instant::now();
        let preparation = IncidentPreparation::from_request(&self.presentation.spec, request)?;
        let options = self
            .presentation
            .spec
            .generator
            .as_ref()
            .ok_or_else(|| invalid("generator session options"))?;
        let model = self
            .generator
            .as_mut()
            .ok_or_else(|| invalid("generator presentation"))?;
        let count = u64::try_from(preparation.source_extent).map_err(invalid)?;
        let next_event = model
            .next_event
            .checked_add(count)
            .ok_or_else(|| invalid("generator source clock exhausted"))?;
        let symbols = preparation
            .source_cells
            .iter()
            .map(|c| c.symbol_index)
            .collect::<Vec<_>>();
        // The passage enters as per-symbol sums read through the encoder table `|A| × 6S`
        // (one row per codec identity); offsets are owned by the binding (A6).
        let alphabet = self.presentation.spec.symbols.len();
        let table = model.encoder.table(alphabet)?;
        let contacts = source_contacts(&preparation, &options.source.contact_kinds);
        let generated = self.body.prepare_generator_symbol_episode(
            Rc::new(table),
            &symbols,
            options.source.clone(),
            model.next_event,
            contacts,
        )?;
        let phases = generated.receive_generator_phases(options.receiver.clone())?;
        let received = model
            .receiver
            .forward(phases.output(), SeriesAperture(options.field.series_terms))?;
        let selected = model.receiver.select_text(&received)?;
        let stop = model.receiver.choose_stop(&received)?;
        if stop > selected.len()
            || selected
                .iter()
                .any(|i| *i >= self.presentation.spec.symbols.len())
        {
            return Err(invalid("generator receiver left its declared text chart"));
        }
        let text = selected[..stop]
            .iter()
            .map(|&i| self.presentation.spec.symbols[i].as_str())
            .collect::<String>();
        let mut result = json!({"schema":"org.holonics.hna.field-section.v1", "scope":"incident-field-joint",
            "source_chart":"generator-machine", "codec":"unicode-scalars", "text":text,
            "symbols":selected[..stop].iter().map(|&i| &self.presentation.spec.symbols[i]).collect::<Vec<_>>(),
            "support":stop, "response_aperture":options.receiver.aperture-1,
            "source_cells":preparation.source_extent, "source_contacts":preparation.contacts.len(),
            "field_sites":options.field.machine.sites().len(), "local_complex":6,
            "source_clock_start":model.next_event, "source_clock_end":next_event,
            "receiver_binding":options.receiver, "producing_epoch":generated.producing_epoch(),
            "material_update":false, "committed":request.commit,
            "generation_us":started.elapsed().as_micros(),
            "native_receipt":{"device":self.surface.device_name(),"kernel_sha256":self.surface.ptx_sha256(),"census":self.surface.census()}});
        let generated = self.body.publish_incident_field(
            generated,
            request.commit,
            request.retain_comparison,
        )?;
        if request.commit {
            model.next_event = next_event;
        }
        if let Some(id) = generated.comparison_id() {
            // The comparison keeps its declared passage relation; its producing phases and faces
            // were read for this generation only and are not retained (one cut at observe).
            drop((phases, received));
            model.pending.insert(
                id,
                GeneratorPending {
                    start: next_event - count,
                    cells: symbols.len(),
                    symbol_counts: {
                        let mut counts = vec![0usize; alphabet];
                        for &symbol in &symbols {
                            counts[symbol] += 1;
                        }
                        counts
                    },
                    record: GeneratorRetainedRecord::from_request(
                        request,
                        &preparation,
                        generated.producing_epoch(),
                    ),
                },
            );
            result["comparison"] = json!(id);
        }
        Ok(result)
    }

    pub(super) fn generator_observe(
        &mut self,
        id: u64,
        text: &str,
        step_bits: u32,
    ) -> Result<Value> {
        Ok(self.generator_observe_cut(id, text, step_bits, false)?.0)
    }

    /// Observe a comparison at one cut. The retained source Holon is re-read at the
    /// contemporary constitution (`U^N q₀(now) + m`, one incident word through the current field
    /// and material), received through the current receiving maps, compared as the Holon ratio
    /// and pulled back through those same operands. The target passage is evaluated at the same
    /// cut through the same machine and receiver; its receiving phases `φ^T` enter the covector's
    /// phase part `½ q (φ^T − φ^H)`, while the magnitude face `q` stays the observation. The
    /// ratio's branch is the continuity of its own lift (`n = 0`; both phases are lifts read
    /// through the same ring, so the ring's winding cancels). With `read`, the faces are also
    /// returned for exterior readings. All fallible preparation precedes the one publication.
    pub(super) fn generator_observe_cut(
        &mut self,
        id: u64,
        text: &str,
        step_bits: u32,
        read: bool,
    ) -> Result<(Value, Option<GeneratorObserveCut<'c>>)> {
        let target = self
            .presentation
            .spec
            .symbols_of(&self.presentation.chart, text)?
            .into_iter()
            .map(|s| s.0 as usize)
            .collect::<Vec<_>>();
        let options = self
            .presentation
            .spec
            .generator
            .as_ref()
            .ok_or_else(|| invalid("generator session options"))?
            .clone();
        let terms = SeriesAperture(options.field.series_terms);
        let counts = self
            .generator
            .as_ref()
            .ok_or_else(|| invalid("generator presentation"))?
            .pending
            .get(&id)
            .ok_or_else(|| invalid("unknown generator comparison"))?
            .symbol_counts
            .clone();
        // One cut: the contemporary word read through the contemporary encoder table restricted
        // to the request's alphabet (identities are stable and appended, so the first |A| rows
        // are exactly the identities the passage's sums index), its phases and the current R.
        let (table, full_table) = {
            let model = self
                .generator
                .as_ref()
                .ok_or_else(|| invalid("generator presentation"))?;
            let alphabet = self.presentation.spec.symbols.len();
            (
                model.encoder.table(counts.len())?,
                (!target.is_empty())
                    .then(|| model.encoder.table(alphabet))
                    .transpose()?,
            )
        };
        let table = Rc::new(table);
        let now = self.body.contemporary_symbol_comparison(id, &table)?;
        let phases = now.receive_generator_phases(options.receiver.clone())?;
        // The target Holon: the observed passage evaluated through the same machine at the same
        // cut (same q₀, one F_Θ word, same material, binding and clock origin, same encoder
        // table) and received through the same phase maps and the current receiver. Its
        // receiving phases enter the comparison. A target that reaches a codec identity admitted
        // after the request is outside that table; it is read as the word-free moment Holon
        // through the full contemporary table instead, and the observe reports which.
        let mut target_holon = "none";
        let target_forward = match full_table {
            None => None,
            Some(full) => {
                let reception = if target.iter().all(|&symbol| symbol < counts.len()) {
                    target_holon = "word";
                    self.body.evaluate_target_holon(
                        id,
                        &table,
                        &target,
                        Vec::new(),
                        options.receiver.clone(),
                    )?
                } else {
                    target_holon = "moment";
                    self.body
                        .accumulate_generator_symbol_moment(
                            Rc::new(full),
                            &target,
                            &options.source,
                        )?
                        .receive_moment_phases(options.receiver.clone())?
                };
                let model = self
                    .generator
                    .as_ref()
                    .ok_or_else(|| invalid("generator presentation"))?;
                Some(model.receiver.forward(reception.output(), terms)?)
            }
        };
        // The ratio's own lift: φ^T and φ^H are real lifts read through the same ring at the same
        // phase, so the ring winding cancels from their difference; n = 0.
        let branches = vec![0i64; options.receiver.aperture];
        let model = self
            .generator
            .as_mut()
            .ok_or_else(|| invalid("generator presentation"))?;
        let received = model.receiver.forward(phases.output(), terms)?;
        let (returned, faces) = model.receiver.compare(
            &received,
            target_forward.as_ref(),
            &target,
            &branches,
            terms,
            step_bits,
        )?;
        let phase_rows = returned
            .boundary_covector
            .split_components(options.receiver.aperture)?;
        let joint = phases.pull_back_joint(&phase_rows)?;
        // The directed-contact relation is inside the body's per-port sums: none is supplied.
        let field_return =
            self.body
                .prepare_generator_material_return(&now, joint.view(), step_bits, &[])?;
        let symbol_covector = field_return
            .symbol_covector()
            .ok_or_else(|| invalid("generator symbol covector absent"))?;
        let encoder_return =
            model
                .encoder
                .prepare_pooled_return(&counts, symbol_covector, step_bits)?;
        // All fallible source/receiver/field preparation precedes the one publication boundary.
        self.body.publish_incident_material_return(field_return)?;
        model.encoder.publish(encoder_return);
        model.receiver.publish(returned.successor);
        model.pending.remove(&id);
        let value = json!({"scope":"incident-field-joint", "source_chart":"generator-machine",
            "comparison":id, "observed_symbols":target.len(), "material_update":true,
            "field_sites":options.field.machine.sites().len(), "comparison_cut":"contemporary",
            "ratio_covector":"(q - p) + i (1/2) q (phi^T - phi^H)", "target_holon":target_holon});
        let cut = read.then(|| GeneratorObserveCut {
            target_holon,
            faces,
            target,
            pooled_symbol_counts: counts.iter().copied().filter(|k| *k > 0).collect(),
        });
        Ok((value, cut))
    }
}

#[cfg(test)]
impl<'c> NativeFieldSession<'c> {
    /// Test reading of an outstanding comparison at the contemporary constitution: its phase
    /// rows and the current receiver's text/stop potentials, without any publication.
    pub(super) fn generator_contemporary_reading(&mut self, id: u64) -> Result<Value> {
        let options = self
            .presentation
            .spec
            .generator
            .as_ref()
            .ok_or_else(|| invalid("generator session options"))?
            .clone();
        let pending = self
            .generator
            .as_ref()
            .ok_or_else(|| invalid("generator presentation"))?
            .pending
            .get(&id)
            .ok_or_else(|| invalid("unknown generator comparison"))?;
        let (start, cells) = pending.source_clock();
        let alphabet = pending.symbol_counts.len();
        let table = self
            .generator
            .as_ref()
            .ok_or_else(|| invalid("generator presentation"))?
            .encoder
            .table(alphabet)?;
        let now = self.body.contemporary_symbol_comparison(id, &table)?;
        let phases = now.receive_generator_phases(options.receiver.clone())?;
        let model = self
            .generator
            .as_ref()
            .ok_or_else(|| invalid("generator presentation"))?;
        let received = model
            .receiver
            .forward(phases.output(), SeriesAperture(options.field.series_terms))?;
        Ok(json!({"phase":phases.output().inspect_rows()?,
            "text":received.text_logits.inspect_rows()?,
            "stop":received.support_logits.inspect_rows()?,
            "binding":phases.binding(),"start":start,"cells":cells}))
    }
}
