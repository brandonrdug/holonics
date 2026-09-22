//! Exterior observer readings of a completed generator request/observe, in bits.
//!
//! These are readings of the same kind as a timing or a byte count. Nothing in the machine reads
//! them, nothing blocks on them, and they are not a loss, a threshold or a gate: the paired
//! adjoint remains the learning law. Floating point is used only here, on host copies of exact
//! readouts, and never enters a resident section.
//!
//! * `H_src`: `N log2|A|` for the admitted exterior codec alphabet, plus the order-0/order-1
//!   empirical code length of the exposure stream the observer has seen.
//! * `L_target|model`: `Σ_j −log2 p_j(t_j)` plus the stop/continue term, where `p` is the
//!   producing receiver's normalized exponential face (`NativeNormalizedSection::read_participation`
//!   of the forward `text_face`/`support_face`; the delayed comparison's prediction is the same
//!   normalized exponential of the same real potentials), read through the pending comparison's
//!   read-only `received()` accessor.
//! * `B_state`: reduced numerator/denominator bit lengths of the continuing exact carriers
//!   (pair amplitudes, joint q/b, reaction material M, source map E, text map R, stop map).
//! * `B_pending`: checkpoint octets with the comparison held minus without it, from the public
//!   `checkpoint`.
//! * navigation: machine steps per site and exact winding where a closure witness exists.
//! * a `CostReceipt` (`holonic_engine::presentation_cost`) with provenance per coordinate.
use super::boundary::BoundaryMaterial;
use super::incident_receiver::phase::GeneratorTextReceiver;
use super::*;
use crate::alpha::exposure::{ExteriorRequestMeasure, ExteriorReturnObserver};
use holonic_engine::ExactInterval;
use holonic_engine::native_ecology::constitutive_fibre::{
    BoundaryMaterialSeed, NormalMaterialRest,
};
use holonic_engine::presentation_cost::{CostReceipt, Counted};
use holonic_engine::resident_section::{SeriesAperture, TransferCensus};
use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};
use relational_geometry::Rat;
use std::io::Cursor;

#[cfg(test)]
mod tests;

/// A bit length read from an exact face interval: the centre and the enclosing interval. An
/// endpoint whose probability bound reaches zero has no finite upper code length (`None`).
#[derive(Clone, Debug, Default, Serialize)]
pub struct BitsReading {
    pub centre_bits: f64,
    pub lower_bits: Option<f64>,
    pub upper_bits: Option<f64>,
}

impl BitsReading {
    fn of(probability: &ExactInterval) -> Self {
        let lower = probability.lower.to_f64().unwrap_or(0.0);
        let upper = probability.upper.to_f64().unwrap_or(0.0);
        let bits = |p: f64| (p > 0.0).then(|| -p.log2());
        Self {
            centre_bits: bits(0.5 * (lower + upper)).unwrap_or(f64::INFINITY),
            lower_bits: bits(upper),
            upper_bits: bits(lower),
        }
    }

    fn add(&mut self, other: &Self) {
        self.centre_bits += other.centre_bits;
        self.lower_bits = self.lower_bits.zip(other.lower_bits).map(|(a, b)| a + b);
        self.upper_bits = self.upper_bits.zip(other.upper_bits).map(|(a, b)| a + b);
    }

    fn zero() -> Self {
        Self {
            centre_bits: 0.0,
            lower_bits: Some(0.0),
            upper_bits: Some(0.0),
        }
    }
}

#[derive(Clone, Debug, Serialize)]
pub struct ReceivingRowReading {
    pub row: usize,
    /// Observed text class at this row, if the target reaches it.
    pub target_class: Option<usize>,
    pub text: Option<BitsReading>,
    /// `1` = continue, `0` = stop; the class the comparison observes at this row.
    pub stop_class: usize,
    pub stop: BitsReading,
}

#[derive(Clone, Debug, Serialize)]
pub struct SourceReading {
    pub source_cells: usize,
    pub alphabet_classes: usize,
    /// `N log2|A|` for this request.
    pub source_bits: f64,
    /// `Σ N_k log2|A_k|` over every request this observer measured.
    pub source_bits_cumulative: f64,
    pub exposure_symbols: u64,
    pub exposure_order0_bits: f64,
    pub exposure_order1_bits: f64,
}

#[derive(Clone, Debug, Serialize)]
pub struct TargetReading {
    pub text_positions: usize,
    pub receiving_rows: usize,
    pub face: &'static str,
    /// The target reached a class admitted after production; the explicit retro face was read.
    pub retro_face: bool,
    pub text: BitsReading,
    pub stop: BitsReading,
    pub model: BitsReading,
    /// Rows whose observed-class probability enclosure reaches zero (no finite upper code
    /// length). When nonzero the centre reading is the midpoint of a broad enclosure, not a
    /// resolved face value; the interval is the reading.
    pub rows_unbounded: usize,
    pub rows: Vec<ReceivingRowReading>,
    pub baseline_uniform_text_bits: f64,
    pub baseline_order0_text_bits: f64,
    pub baseline_order1_text_bits: f64,
    /// One bit per receiving row: the uniform two-class stop/continue face.
    pub baseline_stop_bits: f64,
    /// `log2(A_out+1)`: a uniform length over the admitted response lengths (not the chart the
    /// stop receiver uses; reported for comparison with the plan's length convention).
    pub baseline_length_uniform_bits: f64,
    /// `baseline_text + baseline_stop − model` (centre), bits.
    pub gain_uniform_bits: f64,
    pub gain_order0_bits: f64,
    pub gain_order1_bits: f64,
    /// Gains divided by the receiving rows (text positions plus the stop row), bits/row.
    pub gain_uniform_bits_per_row: f64,
    pub gain_order0_bits_per_row: f64,
    pub gain_order1_bits_per_row: f64,
}

#[derive(Clone, Debug, Default, Serialize)]
pub struct ExactBitCount {
    pub values: u64,
    /// Σ (bitlen|numerator| + 1 sign bit + bitlen denominator) of reduced rationals.
    pub bits: u128,
}

impl ExactBitCount {
    fn rat(&mut self, value: &Rat) {
        self.values += 1;
        self.bits += u128::from(value.numer().abs().bits()) + 1 + u128::from(value.denom().bits());
    }

    fn dyadic(&mut self, numerator: i64, grain: u32) {
        self.values += 1;
        if numerator == 0 {
            self.bits += 2;
            return;
        }
        let shift = numerator.trailing_zeros().min(grain);
        let reduced = (numerator >> shift).unsigned_abs();
        let exponent = grain - shift;
        self.bits += u128::from(64 - reduced.leading_zeros()) + 1 + u128::from(exponent + 1);
    }

    fn json(&mut self, value: &Value) {
        match value {
            Value::String(text) => {
                if let Some(rat) = parse_rat(text) {
                    self.rat(&rat);
                }
            }
            // `BigRational`'s serde chart: `[[sign, limbs], [sign, limbs]]`.
            Value::Array(items)
                if items.len() == 2
                    && items.iter().all(|item| {
                        item.as_array()
                            .is_some_and(|pair| pair.len() == 2 && pair[1].is_array())
                    }) =>
            {
                match serde_json::from_value::<Rat>(value.clone()) {
                    Ok(rat) => self.rat(&Rat::new(rat.numer().clone(), rat.denom().clone())),
                    Err(_) => items.iter().for_each(|item| self.json(item)),
                }
            }
            Value::Array(items) => items.iter().for_each(|item| self.json(item)),
            Value::Object(map) => map.values().for_each(|item| self.json(item)),
            _ => {}
        }
    }

    fn material(&mut self, bytes: &[u8]) -> Result<()> {
        let rest = NormalMaterialRest::read(&mut Cursor::new(bytes), bytes.len() as u64)
            .map_err(invalid)?;
        let grain = rest.grain().0;
        for (lower, upper) in &rest.state().intervals {
            self.dyadic(*lower, grain);
            self.dyadic(*upper, grain);
        }
        Ok(())
    }
}

fn parse_rat(text: &str) -> Option<Rat> {
    let (numerator, denominator) = match text.split_once('/') {
        Some((n, d)) => (n, d),
        None => (text, "1"),
    };
    let numerator: BigInt = numerator.parse().ok()?;
    let denominator: BigInt = denominator.parse().ok()?;
    (!denominator.is_zero()).then(|| Rat::new(numerator, denominator))
}

#[derive(Clone, Debug, Serialize)]
pub struct StateReading {
    /// Exact carrier bit lengths by owner: `rho` pair amplitudes, `joint_qb`, `reaction_m`,
    /// `source_e`, `text_r`, `stop`.
    pub components: BTreeMap<&'static str, ExactBitCount>,
    pub state_bits: u128,
    pub checkpoint_octets: u64,
    /// Checkpoint octets after the request minus before it: the held comparison (`B_pending`).
    pub pending_octets: i128,
    /// Checkpoint octets after observe minus before it.
    pub observe_octets: i128,
}

#[derive(Clone, Debug, Serialize)]
pub struct SiteNavigation {
    pub site: String,
    pub source: bool,
    pub receiver: bool,
    /// Machine step actions applied at this site by committed source occurrences so far.
    pub committed_source_steps: u64,
    /// Step actions this request's source applied at this site.
    pub request_source_steps: u64,
    /// Receiving phase rows read at this site by this request.
    pub receiving_steps: u64,
    pub cayley_parameter: String,
    pub closure_period: Option<usize>,
    /// Full turns completed by the committed steps, when a closure witness exists.
    pub committed_windings: Option<String>,
    /// Depth of the Farey lock address of lifted turns per period, when a closure exists.
    pub lock_address_depth: Option<String>,
    pub turn: &'static str,
}

#[derive(Clone, Debug, Serialize)]
pub struct NavigationReading {
    pub request_source_steps: usize,
    pub committed_source_steps: u64,
    pub sites: Vec<SiteNavigation>,
}

#[derive(Clone, Debug, Serialize)]
pub struct NativeReturnReading {
    pub scope: &'static str,
    pub comparison: u64,
    pub source: SourceReading,
    pub target: TargetReading,
    pub state: StateReading,
    /// `B_state / Σ H_src` over the observer's run.
    pub state_bits_per_source_bit: f64,
    pub navigation: NavigationReading,
    pub cost: CostReceipt,
    pub request_seconds: f64,
    pub observe_seconds: f64,
    pub request_census: BTreeMap<String, i128>,
    pub observe_census: BTreeMap<String, i128>,
}

fn census_difference(before: &TransferCensus, after: &TransferCensus) -> BTreeMap<String, i128> {
    let (Ok(Value::Object(before)), Ok(Value::Object(after))) =
        (serde_json::to_value(before), serde_json::to_value(after))
    else {
        return BTreeMap::new();
    };
    after
        .iter()
        .filter_map(|(key, value)| {
            let after = value.as_i64()?;
            let before = before.get(key)?.as_i64()?;
            Some((key.clone(), i128::from(after) - i128::from(before)))
        })
        .collect()
}

fn launches(census: &BTreeMap<String, i128>) -> u64 {
    ["captured_launches", "control_launches"]
        .iter()
        .map(|key| census.get(*key).copied().unwrap_or(0).max(0) as u64)
        .sum()
}

fn read_material(bytes: &[u8]) -> Result<NormalMaterialRest> {
    NormalMaterialRest::read(&mut Cursor::new(bytes), bytes.len() as u64).map_err(invalid)
}

impl<'c> NativeFieldSession<'c> {
    fn measured_generator(&self) -> Result<&GeneratorSessionOptions> {
        self.presentation
            .spec
            .generator
            .as_ref()
            .filter(|_| self.generator.is_some())
            .ok_or_else(|| invalid("return readings are declared for the generator session"))
    }

    /// Octets of the existing public checkpoint of this session at this moment.
    fn checkpoint_octets(&self) -> Result<u64> {
        let directory = tempfile::tempdir()?;
        let path = directory.path().join("reading.hna");
        self.checkpoint(&path, &HnaStreamState::default())?;
        Ok(std::fs::metadata(&path)?.len())
    }

    /// Issue a generator request and take its exterior request-side reading.
    pub fn measured_request(
        &mut self,
        request: &FieldSectionRequest,
        observer: &mut ExteriorReturnObserver,
    ) -> Result<Value> {
        self.measured_generator()?;
        let preparation = IncidentPreparation::from_request(&self.presentation.spec, request)?;
        let symbols = preparation
            .source_cells
            .iter()
            .map(|cell| cell.symbol_index)
            .collect::<Vec<_>>();
        let alphabet = self.presentation.spec.symbols.len();
        let before_octets = self.checkpoint_octets()?;
        let before = self.surface.census();
        let started = Instant::now();
        let value = self.request(request)?;
        let request_seconds = started.elapsed().as_secs_f64();
        let census = census_difference(&before, &self.surface.census());
        let after_octets = self.checkpoint_octets()?;
        let source_bits = symbols.len() as f64 * (alphabet as f64).log2();
        observer.source_bits_total += source_bits;
        observer.source_cells_total += symbols.len() as u64;
        let committed = value["committed"].as_bool().unwrap_or(false);
        if committed {
            observer.committed_source_steps += symbols.len() as u64;
        }
        observer.stream.ingest(&symbols, None);
        if let Some(id) = value["comparison"].as_u64() {
            observer.requests.insert(
                id,
                ExteriorRequestMeasure {
                    source_cells: symbols.len(),
                    alphabet,
                    source_bits,
                    last_source_symbol: symbols.last().copied(),
                    committed,
                    source_clock_start: value["source_clock_start"].as_u64().unwrap_or(0),
                    source_clock_end: value["source_clock_end"].as_u64().unwrap_or(0),
                    request_seconds,
                    request_launches: launches(&census),
                    request_census: census,
                    checkpoint_octets_before: before_octets,
                    checkpoint_octets_after: after_octets,
                },
            );
        }
        Ok(value)
    }

    /// Read the producing face of a held comparison, observe it, and take the full exterior
    /// return reading. The observe is the ordinary public observe; the reading does not alter it.
    pub fn read_return(
        &mut self,
        comparison: u64,
        text: &str,
        step_bits: u32,
        observer: &mut ExteriorReturnObserver,
    ) -> Result<(Value, NativeReturnReading)> {
        let options = self.measured_generator()?.clone();
        let requested = observer
            .requests
            .remove(&comparison)
            .ok_or_else(|| invalid("comparison was not issued through measured_request"))?;
        let target = self
            .presentation
            .spec
            .symbols_of(&self.presentation.chart, text)?
            .into_iter()
            .map(|symbol| symbol.0 as usize)
            .collect::<Vec<_>>();
        let (text_faces, stop_faces, face_classes, retro_face) =
            self.producing_faces(comparison, &target, &options)?;
        let before_octets = self.checkpoint_octets()?;
        let before = self.surface.census();
        let started = Instant::now();
        let value = self.observe(comparison, text, step_bits)?;
        let observe_seconds = started.elapsed().as_secs_f64();
        let observe_census = census_difference(&before, &self.surface.census());
        let checkpoint_octets = self.checkpoint_octets()?;

        // L_target|model on the producing face.
        let mut rows = Vec::with_capacity(target.len() + 1);
        let (mut text_bits, mut stop_bits) = (BitsReading::zero(), BitsReading::zero());
        for row in 0..=target.len() {
            let text_reading = target
                .get(row)
                .map(|&class| {
                    text_faces
                        .get(row)
                        .and_then(|face| face.get(class))
                        .map(BitsReading::of)
                        .ok_or_else(|| invalid("receiving text face row/class"))
                })
                .transpose()?;
            if let Some(reading) = &text_reading {
                text_bits.add(reading);
            }
            let stop_class = usize::from(row != target.len());
            let stop = stop_faces
                .get(row)
                .and_then(|face| face.get(stop_class))
                .map(BitsReading::of)
                .ok_or_else(|| invalid("receiving stop face row"))?;
            stop_bits.add(&stop);
            rows.push(ReceivingRowReading {
                row,
                target_class: target.get(row).copied(),
                text: text_reading,
                stop_class,
                stop,
            });
        }
        let mut model = text_bits.clone();
        model.add(&stop_bits);
        let receiving_rows = target.len() + 1;
        let alphabet = self.presentation.spec.symbols.len();
        let uniform = target.len() as f64 * (face_classes as f64).log2();
        let (order0, order1) =
            observer
                .stream
                .predictive_bits(&target, requested.last_source_symbol, alphabet);
        let stop_baseline = receiving_rows as f64;
        let gain = |baseline: f64| baseline + stop_baseline - model.centre_bits;
        let per_row = |bits: f64| bits / receiving_rows as f64;
        let target_reading = TargetReading {
            text_positions: target.len(),
            receiving_rows,
            face: "producing receiver normalized exponential face (read_participation)",
            retro_face,
            text: text_bits,
            stop: stop_bits,
            model: model.clone(),
            rows_unbounded: rows
                .iter()
                .filter(|row| {
                    row.stop.upper_bits.is_none()
                        || row
                            .text
                            .as_ref()
                            .is_some_and(|text| text.upper_bits.is_none())
                })
                .count(),
            rows,
            baseline_uniform_text_bits: uniform,
            baseline_order0_text_bits: order0,
            baseline_order1_text_bits: order1,
            baseline_stop_bits: stop_baseline,
            baseline_length_uniform_bits: (options.receiver.aperture as f64).log2(),
            gain_uniform_bits: gain(uniform),
            gain_order0_bits: gain(order0),
            gain_order1_bits: gain(order1),
            gain_uniform_bits_per_row: per_row(gain(uniform)),
            gain_order0_bits_per_row: per_row(gain(order0)),
            gain_order1_bits_per_row: per_row(gain(order1)),
        };
        // The observed target joins the exterior stream after its baseline was read.
        observer
            .stream
            .ingest(&target, Some(requested.last_source_symbol));
        observer.returns += 1;

        let components = self.state_bits()?;
        let state_bits = components.values().map(|count| count.bits).sum::<u128>();
        let state = StateReading {
            components,
            state_bits,
            checkpoint_octets,
            pending_octets: i128::from(requested.checkpoint_octets_after)
                - i128::from(requested.checkpoint_octets_before),
            observe_octets: i128::from(checkpoint_octets) - i128::from(before_octets),
        };
        let navigation = navigation(&options, &requested, observer.committed_source_steps)?;
        let residual = if model.centre_bits.is_finite() {
            Counted::derived(
                model.centre_bits.ceil().max(0.0) as u64,
                "ceil of the observed target's code length Σ−log2 p under the producing face \
                 (centre); the bits the continuing chart did not carry for this target",
            )
        } else {
            Counted::derived(
                0u64,
                "undefined: a producing probability centre was zero; see target.model",
            )
        };
        let cost = CostReceipt {
            presentation: "generator-machine session return (request + observe)".into(),
            bytes: Counted::measured(
                checkpoint_octets,
                "octets of NativeFieldSession::checkpoint after observe",
            ),
            decode_work: Counted::measured(
                requested.request_launches,
                "ResidentSurface census: captured + direct kernel launches during request",
            ),
            update_work: Counted::measured(
                launches(&observe_census),
                "ResidentSurface census: captured + direct kernel launches during observe",
            ),
            certificate_work: Counted::derived(
                0u64,
                "no certificate pass executes inside request/observe; rest validation runs only \
                 when a checkpoint is reopened",
            ),
            residual,
        };
        let source = SourceReading {
            source_cells: requested.source_cells,
            alphabet_classes: requested.alphabet,
            source_bits: requested.source_bits,
            source_bits_cumulative: observer.source_bits_total,
            exposure_symbols: observer.stream.symbols(),
            exposure_order0_bits: observer.stream.order0_bits(),
            exposure_order1_bits: observer.stream.order1_bits(),
        };
        let reading = NativeReturnReading {
            scope: "exterior observer reading; not read by the machine, not a loss or gate",
            comparison,
            state_bits_per_source_bit: if observer.source_bits_total > 0.0 {
                state.state_bits as f64 / observer.source_bits_total
            } else {
                f64::INFINITY
            },
            source,
            target: target_reading,
            state,
            navigation,
            cost,
            request_seconds: requested.request_seconds,
            observe_seconds,
            request_census: requested.request_census,
            observe_census,
        };
        Ok((value, reading))
    }

    /// Read the producing text/stop faces of a held comparison through its read-only pending
    /// accessor. A target class admitted after production is read through the explicit retro
    /// face of the contemporary receiver, rebuilt from the public rest exactly as a reopened
    /// checkpoint rebuilds it. Returns (text rows × classes, stop rows × 2, text classes, retro).
    #[allow(clippy::type_complexity)]
    fn producing_faces(
        &self,
        comparison: u64,
        target: &[usize],
        options: &GeneratorSessionOptions,
    ) -> Result<(
        Vec<Vec<ExactInterval>>,
        Vec<Vec<ExactInterval>>,
        usize,
        bool,
    )> {
        let spec = &self.presentation.spec;
        let generator = self
            .generator
            .as_ref()
            .ok_or_else(|| invalid("generator presentation"))?;
        let producing = generator
            .pending
            .get(&comparison)
            .ok_or_else(|| invalid("unknown generator comparison"))?
            .received();
        let old_classes = producing
            .text_cohorts
            .iter()
            .map(|cohort| cohort.class_count)
            .sum::<usize>();
        let terms = SeriesAperture(options.field.series_terms);
        let retro = target.iter().any(|class| *class >= old_classes);
        let retro_forward = if retro {
            let rest = generator.rest()?;
            let boundary = BoundaryMaterial::found(
                self.surface,
                spec.chart()?,
                options.receiver.ports.len() * 6,
                1,
                ResidentGrain(spec.fractional_bits),
                BoundaryMaterialSeed::new(options.material_seed, spec.fractional_bits),
            )?;
            let current = GeneratorTextReceiver::remount_with_cohorts(
                self.surface,
                boundary,
                read_material(&rest.receiver_text)?,
                read_material(&rest.receiver_support)?,
                rest.receiver_cohorts.clone(),
                rest.receiver_cohort_material
                    .iter()
                    .map(|bytes| read_material(bytes))
                    .collect::<Result<Vec<_>>>()?,
                rest.receiver_cohorts
                    .last()
                    .map_or(0, |cohort| cohort.codec_version),
            )?;
            Some(current.retro_forward(producing, terms)?)
        } else {
            None
        };
        let received = retro_forward.as_ref().unwrap_or(producing);
        let classes = received
            .text_cohorts
            .iter()
            .map(|cohort| cohort.class_count)
            .sum::<usize>();
        let text = received.text_face.read_participation().map_err(invalid)?;
        let stop = received
            .support_face
            .read_participation()
            .map_err(invalid)?;
        Ok((text, stop, classes, retro))
    }

    /// Exact carrier bit lengths of the continuing chart, by owner.
    fn state_bits(&mut self) -> Result<BTreeMap<&'static str, ExactBitCount>> {
        let mut components = BTreeMap::new();
        let current = self.body.inspect_current()?;
        let mut rho = ExactBitCount::default();
        rho.json(&current["operator"]["declared_amplitudes"]);
        components.insert("rho", rho);
        let mut joint = ExactBitCount::default();
        joint.json(&current["joint"]);
        components.insert("joint_qb", joint);
        let mut reaction = ExactBitCount::default();
        for member in 0..self.body.members() {
            reaction.json(&self.body.inspect_predictive_material(member)?);
        }
        components.insert("reaction_m", reaction);
        let rest = self
            .generator
            .as_ref()
            .ok_or_else(|| invalid("generator presentation"))?
            .rest()?;
        let mut source = ExactBitCount::default();
        for bytes in &rest.encoder_material {
            source.material(bytes)?;
        }
        components.insert("source_e", source);
        let mut text = ExactBitCount::default();
        text.material(&rest.receiver_text)?;
        for bytes in &rest.receiver_cohort_material {
            text.material(bytes)?;
        }
        components.insert("text_r", text);
        let mut stop = ExactBitCount::default();
        stop.material(&rest.receiver_support)?;
        components.insert("stop", stop);
        Ok(components)
    }
}

fn navigation(
    options: &GeneratorSessionOptions,
    requested: &ExteriorRequestMeasure,
    committed_source_steps: u64,
) -> Result<NavigationReading> {
    let machine = options.field.machine.compile().map_err(invalid)?;
    let step_exponent = |ports: &[crate::native::GeneratorPhasePort], site: &str| {
        ports
            .iter()
            .filter(|port| port.site_id == site)
            .map(|port| port.step_exponent.unsigned_abs())
            .sum::<u64>()
    };
    let receiving_rows = options.receiver.aperture as u64;
    let sites = machine
        .sites()
        .iter()
        .map(|site| {
            let source_exponent = step_exponent(&options.source.clocks, site.id());
            let committed = committed_source_steps * source_exponent;
            let phase = site.phase();
            let mut reading = SiteNavigation {
                site: site.id().to_owned(),
                source: site.is_source(),
                receiver: site.is_receiver(),
                committed_source_steps: committed,
                request_source_steps: requested.source_cells as u64 * source_exponent,
                receiving_steps: receiving_rows * step_exponent(&options.receiver.ports, site.id()),
                cayley_parameter: phase.parameter().to_string(),
                closure_period: site.closure(),
                committed_windings: None,
                lock_address_depth: None,
                turn: "not a rational turn: no closure witness for this Cayley step",
            };
            if let Some(period) = site.closure() {
                if let Ok(winding) = phase.lifted_winding(period) {
                    let turns = BigInt::from(winding.lifted) * BigInt::from(committed)
                        / BigInt::from(period as u64);
                    reading.committed_windings = Some(turns.to_string());
                    reading.turn = "rational turn: lifted winding per closure period";
                    if winding.lifted > 0 {
                        if let Ok(address) = relational_geometry::winding::LockAddress::from_ratio(
                            &BigInt::from(winding.lifted),
                            &BigInt::from(period as u64),
                        ) {
                            reading.lock_address_depth = Some(address.depth().to_string());
                        }
                    }
                }
            }
            reading
        })
        .collect();
    Ok(NavigationReading {
        request_source_steps: requested.source_cells,
        committed_source_steps,
        sites,
    })
}
