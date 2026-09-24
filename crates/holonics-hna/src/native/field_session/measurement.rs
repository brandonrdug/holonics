//! Exterior observer readings of a completed generator request/observe.
//!
//! These are readings of the same kind as a timing or a byte count. Nothing in the machine reads
//! them, nothing blocks on them, and they are not a gate: the paired adjoint remains the learning
//! law. Floating point is used only here, on host copies of exact readouts, and never enters a
//! resident section. A receipt is a field of readings over the machine's parts, not one scalar.
//!
//! * The ratio `l_j = log(psi^T/psi^H)` at each receiving phase, on the one magnitude face
//!   `p = softmax(Re s)` the comparison is formed on (the same face selection orders by and the
//!   same object that returns the covector): its code-length part `Re (2/ln2) l = -log2 p(t)`
//!   (KL bits against the observed one-hot face) and its phase part
//!   `Im (2/ln2) l = (2/ln2)(phi^T - phi^H)` on the ratio's own lift (branch `n = 0`; both
//!   phases are read through the same ring, so its winding cancels and is reported only as a
//!   ring reading); the supported/partial/unsupported split of
//!   `surprisal::cross_entropy_fiber` where a produced probability enclosure reaches zero; and
//!   the observation jet `l_(n+1) - l_n`.
//! * `H_src`: `N log2|A|` plus the order-0/order-1 empirical code length of the exposure stream.
//! * `B_state`: reduced numerator/denominator bit lengths of the continuing exact carriers.
//! * `B_pending`: the outstanding comparison's own rest octets (the session's declared relation
//!   and the body's source-Holon operands), not a checkpoint difference that would include the
//!   committed `q/b`.
//! * Per ring (site): its declared phase exponent, ticks, winding, and the variability of its
//!   current energy increments per tick over its own observations; per contact (arc): its pair
//!   amplitude and the current contrast across it.
//! * Work and erasure: kernel launches, and the Landauer erasure of the observe's collapse
//!   (`landauer::erasure_of` over the encoder's per-symbol pooling). No power meter is read, so
//!   no energy is reported.
use super::generator_application::GeneratorObserveCut;
use super::*;
use crate::alpha::exposure::{ExteriorRequestMeasure, ExteriorReturnObserver};
use holonics::exact_value::ExactInterval;
use holonic_engine::native_ecology::constitutive_fibre::{
    NativeNormalizedSection, NormalMaterialRest, ResidentNormalEnclosureSection,
};
use holonic_engine::presentation_cost::{CostReceipt, Counted};
use holonic_engine::resident_section::TransferCensus;
use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive, Zero};
use holonics::geometry::Rat;
use std::io::Cursor;

#[cfg(test)]
mod tests;

/// A bit length read from an exact face interval: the centre and the enclosing interval. The
/// probability enclosure is first clamped to `[0, 1]` (a face is a simplex section; an outward
/// enclosure may overhang it), so every bound is a nonnegative code length. An endpoint whose
/// probability bound reaches zero has no finite upper code length (`None`).
#[derive(Clone, Debug, Default, Serialize)]
pub struct BitsReading {
    pub centre_bits: f64,
    pub lower_bits: Option<f64>,
    pub upper_bits: Option<f64>,
}

impl BitsReading {
    fn of(probability: &ExactInterval) -> Self {
        let clamp = |p: f64| p.clamp(0.0, 1.0);
        let lower = clamp(probability.lower.to_f64().unwrap_or(0.0));
        let upper = clamp(probability.upper.to_f64().unwrap_or(0.0));
        let bits = |p: f64| (p > 0.0).then(|| (-p.log2()).max(0.0));
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

/// `surprisal::cross_entropy_fiber`'s split, read on the produced face: a class whose certified
/// probability enclosure reaches zero is outside the logarithmic chart and is not smoothed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum RatioSupport {
    Supported,
    Partial,
    Unsupported,
}

/// The ratio `l = log(psi^T/psi^H)` at one receiving phase and one face, read at the observed
/// class `t`. `kl` is `Re (2/ln2) l = -log2 p_t`; the phase part is
/// `Im (2/ln2) l = (2/ln2)(phi^T_t - phi^H_t)` on the ratio's own lift (branch 0). The receiving
/// ring's absolute winding at this phase is reported beside it as `ring_winding`; it cancels
/// from the ratio (zero, `ring_winding_witness = false`, without a closure witness).
#[derive(Clone, Debug, Serialize)]
pub struct RatioRowReading {
    pub row: usize,
    /// `text` or `stop`.
    pub face: &'static str,
    pub class: usize,
    pub support: RatioSupport,
    pub kl: BitsReading,
    /// `phi^H_t = Im s_t / 2` (radians), centre and outward half width.
    pub produced_phase: Option<(f64, f64)>,
    /// `phi^T_t` of the target Holon through the same maps (radians).
    pub target_phase: Option<(f64, f64)>,
    pub ring_winding: i64,
    pub ring_winding_witness: bool,
    /// `(2/ln2)(phi^T - phi^H + 2 pi n)`, centre, bits: the signed, oriented displacement.
    pub phase_excess_bits: Option<f64>,
    /// `(2/ln2) (1/2) q_t Delta_t^2` (centre): the phase quantity the comparison descends, on
    /// the same `2/ln2` scale (its argument is in rad^2).
    pub phase_descent_bits: Option<f64>,
}

#[derive(Clone, Debug, Serialize)]
pub struct ReceivingRowReading {
    pub row: usize,
    /// Observed text class at this row, if the target reaches it.
    pub target_class: Option<usize>,
    pub text: Option<RatioRowReading>,
    /// `1` = continue, `0` = stop; the class the comparison observes at this row.
    pub stop_class: usize,
    pub stop: RatioRowReading,
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
    /// How the target Holon was read (`word`, `moment` or `none`).
    pub target_holon: &'static str,
    pub text_positions: usize,
    pub receiving_rows: usize,
    pub face: &'static str,
    pub text: BitsReading,
    pub stop: BitsReading,
    /// `Re E_T[(2/ln2) l]` summed over receiving phases: the lifted cross-entropy excess's
    /// code-length face, i.e. `Σ_j −log2 p_j(t_j)` plus the stop term.
    pub model: BitsReading,
    /// `Im E_T[(2/ln2) l]` summed over receiving phases (centre), bits: signed displacement;
    /// `None` for an empty target passage (no target Holon).
    pub phase_excess_bits: Option<f64>,
    /// `(2/ln2) (1/2) Σ q Δ²` summed over receiving phases (centre): the descended quantity.
    pub phase_descent_bits: Option<f64>,
    /// The fibre split over every observed row.
    pub support: RatioSupport,
    pub unsupported_rows: Vec<usize>,
    /// Code length over the supported rows only (centre), bits.
    pub supported_bits: f64,
    /// Rows whose observed-class probability enclosure reaches zero.
    pub rows_unbounded: usize,
    pub rows: Vec<ReceivingRowReading>,
    /// The observation jet: this observation's `Re` and `Im` totals minus the previous
    /// observation's, bits per observation (`None` on the first).
    pub model_bits_per_observation: Option<f64>,
    pub phase_excess_bits_per_observation: Option<f64>,
    pub baseline_uniform_text_bits: f64,
    pub baseline_order0_text_bits: f64,
    pub baseline_order1_text_bits: f64,
    /// One bit per receiving row: the uniform two-class stop/continue face.
    pub baseline_stop_bits: f64,
    /// `log2(A_out+1)`: a uniform length over the admitted response lengths.
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
    /// The outstanding comparison's own operands at request time: the session's pending rest
    /// (declared relation) plus the body's source-Holon rest octets. Committed `q/b` is not in it.
    pub pending_octets: u64,
    pub pending_session_octets: u64,
    pub pending_body_octets: u64,
    pub pending_body_sections: u64,
    /// Host words the session holds for the comparison beyond its clock: `|A|`, fixed in `N`.
    pub pending_relation_words: usize,
    /// Checkpoint octets after observe minus before it.
    pub observe_octets: i128,
    /// The body's commit rebase residual after the observe: commits, grain, and the exact
    /// dropped radius `last`/`max`/`sum` as scaled integers (value `n / 2^grain`), with their
    /// real readings. Exterior; the machine does not read it.
    pub rebase_residual: Value,
}

/// One ring (machine site) over its own ticks.
#[derive(Clone, Debug, Serialize)]
pub struct SiteNavigation {
    pub site: String,
    pub source: bool,
    pub receiver: bool,
    /// Source ticks this ring has taken by committed occurrences so far (its own clock).
    pub ticks: u64,
    /// Step actions applied at this ring by committed source occurrences so far.
    pub committed_source_steps: u64,
    /// Step actions this request's source applied at this ring.
    pub request_source_steps: u64,
    /// Receiving phase rows read at this ring by this request.
    pub receiving_steps: u64,
    /// Declared action exponent reached by the committed ticks: origin + ticks * step.
    pub phase_exponent: i64,
    /// Exponent increment per tick; the declared action is uniform, so its tick-interval
    /// variability is exactly zero.
    pub tick_increment_exponent: i64,
    pub tick_increment_variance: f64,
    pub cayley_parameter: String,
    pub closure_period: Option<usize>,
    /// Full turns completed by the committed steps, when a closure witness exists.
    pub committed_windings: Option<String>,
    /// Depth of the Farey lock address of lifted turns per period, when a closure exists.
    pub lock_address_depth: Option<String>,
    pub turn: &'static str,
    /// `|q_g|²` of this ring's boundary current (centre), in the current chart's squared units.
    pub current_energy: Option<f64>,
    /// Change of `current_energy` since this ring's previous reading, per tick taken since.
    pub energy_increment_per_tick: Option<f64>,
    /// Variance of those per-tick increments over this ring's recorded observations.
    pub energy_increment_variance: Option<f64>,
    pub recorded_observations: usize,
}

/// One pair contact (arc) at the reading's cut.
#[derive(Clone, Debug, Serialize)]
pub struct ContactReading {
    pub arc: String,
    pub source: String,
    pub receiver: String,
    /// Declared positive pair amplitude `rho_a`, when the operator reports it per arc.
    pub amplitude: Option<f64>,
    /// `|q_a − q_b|²` of the two rings' boundary currents in the common current chart (centre):
    /// the contrast the contact's slip acts on. Not a transported flux; no pair map is applied.
    pub interface_contrast: Option<f64>,
}

#[derive(Clone, Debug, Serialize)]
pub struct NavigationReading {
    pub request_source_steps: usize,
    pub committed_source_steps: u64,
    pub sites: Vec<SiteNavigation>,
    pub contacts: Vec<ContactReading>,
}

/// Work and erasure axes of the observe.
#[derive(Clone, Debug, Serialize)]
pub struct WorkReading {
    pub request_launches: u64,
    pub observe_launches: u64,
    /// `landauer::erasure_of` over the encoder's per-symbol pooled occurrence counts: the bits
    /// needed to name an occurrence within its pooled block, which the return does not keep.
    pub erasure_bits: u64,
    pub erasing_blocks: usize,
    pub energy: &'static str,
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
    pub work: WorkReading,
    pub cost: CostReceipt,
    pub request_seconds: f64,
    /// Observe wall time (the target Holon is part of the comparison, so it is included).
    pub observe_seconds: f64,
    pub request_census: BTreeMap<String, i128>,
    pub observe_census: BTreeMap<String, i128>,
}

/// Exterior memory of the observer across observations of one session. Never checkpointed,
/// never read by the machine.
#[derive(Clone, Debug, Default)]
pub(super) struct GeneratorReadingMemory {
    /// Pending operand octets measured at request time, by comparison.
    pending: BTreeMap<u64, (u64, u64, u64, usize)>,
    /// Previous observation's (model bits, phase excess bits).
    previous: Option<(f64, Option<f64>)>,
    /// Per ring: its running summary over its own ticks, fixed size.
    rings: BTreeMap<String, RingSummary>,
}

/// Welford's running summary of one ring's per-tick energy increments: the last reading and its
/// tick, and (count, mean, M2) of the increments. Fixed size; no increment is stored.
#[derive(Clone, Copy, Debug)]
struct RingSummary {
    energy: f64,
    ticks: u64,
    count: u64,
    mean: f64,
    m2: f64,
}

impl GeneratorReadingMemory {
    /// Drop what the observer recorded for a comparison that was released unobserved.
    pub(super) fn forget(&mut self, comparison: u64) {
        self.pending.remove(&comparison);
    }
}

pub(super) fn census_difference(
    before: &TransferCensus,
    after: &TransferCensus,
) -> BTreeMap<String, i128> {
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

fn centre_and_half(value: &ExactInterval) -> (f64, f64) {
    let lower = value.lower.to_f64().unwrap_or(f64::NAN);
    let upper = value.upper.to_f64().unwrap_or(f64::NAN);
    (0.5 * (lower + upper), 0.5 * (upper - lower))
}

fn support_of(probability: &ExactInterval) -> RatioSupport {
    if probability.lower > Rat::zero() {
        RatioSupport::Supported
    } else if probability.upper > Rat::zero() {
        RatioSupport::Partial
    } else {
        RatioSupport::Unsupported
    }
}

/// The ratio reading at one row/class from host copies of the comparison's face.
#[allow(clippy::too_many_arguments)]
fn ratio_row(
    row: usize,
    face: &'static str,
    class: usize,
    produced: &[Vec<ExactInterval>],
    produced_phase: Option<&[Vec<ExactInterval>]>,
    target_phase: Option<&[Vec<ExactInterval>]>,
    branch: (i64, bool),
) -> Result<RatioRowReading> {
    let probability = produced
        .get(row)
        .and_then(|face| face.get(class))
        .ok_or_else(|| invalid("receiving face row/class"))?;
    let phase_h = produced_phase
        .and_then(|p| p.get(row))
        .and_then(|r| r.get(class))
        .map(centre_and_half);
    let phase_t = target_phase
        .and_then(|p| p.get(row))
        .and_then(|r| r.get(class))
        .map(centre_and_half);
    let gap = phase_h.zip(phase_t).map(|((h, _), (t, _))| t - h);
    let excess = gap.map(|gap| 2.0 / std::f64::consts::LN_2 * gap);
    let descent = gap.map(|gap| 2.0 / std::f64::consts::LN_2 * 0.5 * gap * gap);
    Ok(RatioRowReading {
        row,
        face,
        class,
        support: support_of(probability),
        kl: BitsReading::of(probability),
        produced_phase: phase_h,
        target_phase: phase_t,
        ring_winding: branch.0,
        ring_winding_witness: branch.1,
        phase_excess_bits: excess,
        phase_descent_bits: descent,
    })
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

    /// Octets of the existing public checkpoint of this session at this moment. Always taken
    /// outside a timing or census window.
    fn checkpoint_octets(&self) -> Result<u64> {
        let directory = tempfile::tempdir()?;
        let path = directory.path().join("reading.hna");
        self.checkpoint(&path, &HnaStreamState::default())?;
        Ok(std::fs::metadata(&path)?.len())
    }

    /// The outstanding comparison's own operands: session pending rest octets, the body's
    /// retained source-Holon octets and sections, and the relation's host words.
    fn pending_operand_octets(&self, id: u64) -> Result<(u64, u64, u64, usize)> {
        let generator = self
            .generator
            .as_ref()
            .ok_or_else(|| invalid("generator presentation"))?;
        let rest = generator.rest()?;
        let session = rest
            .pending
            .iter()
            .find(|pending| pending.id == id)
            .map(|pending| serde_json::to_vec(pending).map(|bytes| bytes.len() as u64))
            .transpose()?
            .ok_or_else(|| invalid("pending generator rest"))?;
        let census = self.body.generator_comparison_census(id)?;
        let words = generator
            .pending
            .get(&id)
            .map(|pending| pending.pending_relation_words())
            .unwrap_or(0);
        Ok((
            session,
            census["octets"].as_u64().unwrap_or(0),
            census["sections"].as_u64().unwrap_or(0),
            words,
        ))
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
            let pending = self.pending_operand_octets(id)?;
            if let Some(generator) = self.generator.as_mut() {
                generator.readings.pending.insert(id, pending);
            }
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

    /// Observe a held comparison and take the full exterior return reading at the observe's
    /// one cut: the ratio is read on the same face object that returns the covector.
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
        let before_octets = self.checkpoint_octets()?;
        let before = self.surface.census();
        let started = Instant::now();
        let (value, cut) = self.generator_observe_cut(comparison, text, step_bits, true)?;
        let elapsed = started.elapsed().as_secs_f64();
        let observe_census = census_difference(&before, &self.surface.census());
        let cut = cut.ok_or_else(|| invalid("observe reading operands"))?;
        let checkpoint_octets = self.checkpoint_octets()?;
        let observe_seconds = elapsed;

        let target_reading = self.ratio_reading(&cut, &options, &requested, observer)?;
        // The observed target joins the exterior stream after its baseline was read.
        observer
            .stream
            .ingest(&cut.target, Some(requested.last_source_symbol));
        observer.returns += 1;

        let components = self.state_bits()?;
        let state_bits = components.values().map(|count| count.bits).sum::<u128>();
        let (session_octets, body_octets, body_sections, relation_words) = self
            .generator
            .as_mut()
            .and_then(|g| g.readings.pending.remove(&comparison))
            .unwrap_or_default();
        let state = StateReading {
            components,
            state_bits,
            checkpoint_octets,
            pending_octets: session_octets + body_octets,
            pending_session_octets: session_octets,
            pending_body_octets: body_octets,
            pending_body_sections: body_sections,
            pending_relation_words: relation_words,
            observe_octets: i128::from(checkpoint_octets) - i128::from(before_octets),
            rebase_residual: {
                let mut residual = serde_json::to_value(self.body.incident_rebase_residual()?)?;
                let grain = residual["grain"].as_u64().unwrap_or(0) as u32;
                for key in ["last", "max", "sum"] {
                    let value = residual[key]
                        .as_str()
                        .and_then(|text| text.parse::<BigInt>().ok())
                        .map(|n| Rat::new(n, BigInt::from(1u8) << grain));
                    residual[format!("{key}_value")] = json!(value.as_ref().map(|v| v.to_string()));
                    residual[format!("{key}_f64")] = json!(value.and_then(|v| v.to_f64()));
                }
                residual
            },
        };
        let navigation = self.navigation(&options, &requested, observer.committed_source_steps)?;
        let (erased, erasing) = holonic_engine::landauer::erasure_of(&cut.pooled_symbol_counts);
        let observe_launches = launches(&observe_census);
        let work = WorkReading {
            request_launches: requested.request_launches,
            observe_launches,
            erasure_bits: erased.to_u64().unwrap_or(u64::MAX),
            erasing_blocks: erasing.len(),
            energy: "unmeasured: no power reading is taken on this surface",
        };
        let model = &target_reading.model;
        let residual = if model.centre_bits.is_finite() {
            Counted::derived(
                model.centre_bits.ceil().max(0.0) as u64,
                "ceil of the observed target's code length Re E_T[(2/ln2) log R] on the \
                 comparison face (centre); the bits the continuing chart did not carry",
            )
        } else {
            Counted::derived(
                0u64,
                "undefined: a produced probability centre was zero; see target.support",
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
                observe_launches,
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
            scope: "exterior observer reading; not read by the machine, not a gate",
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
            work,
            cost,
            request_seconds: requested.request_seconds,
            observe_seconds,
            request_census: requested.request_census,
            observe_census,
        };
        Ok((value, reading))
    }

    /// The ratio at every receiving phase from host copies of the observe's comparison faces.
    fn ratio_reading(
        &mut self,
        cut: &GeneratorObserveCut<'c>,
        options: &GeneratorSessionOptions,
        requested: &ExteriorRequestMeasure,
        observer: &ExteriorReturnObserver,
    ) -> Result<TargetReading> {
        let target = &cut.target;
        let _ = &cut.faces.classes;
        let read_face = |face: &NativeNormalizedSection<'c>| -> Result<(Vec<Vec<ExactInterval>>, Vec<Vec<ExactInterval>>)> {
            let rows = face.inspect().map_err(invalid)?;
            Ok((
                rows.into_iter().map(|row| row.prediction).collect(),
                face.read_phase().map_err(invalid)?,
            ))
        };
        let read_ball = |ball: &ResidentNormalEnclosureSection<'c>| {
            NativeNormalizedSection::read_phase_ball(ball).map_err(invalid)
        };
        let text = cut.faces.text.as_ref().map(read_face).transpose()?;
        let (stop_p, stop_phase) = read_face(&cut.faces.stop)?;
        // An empty target passage has no target Holon: its stop rows compare agreeing phases.
        let target_phase = (!target.is_empty())
            .then(|| {
                Ok::<_, NativeSessionError>((
                    cut.faces
                        .text
                        .as_ref()
                        .map(|face| read_ball(face.target_phase().map_err(invalid)?))
                        .transpose()?
                        .unwrap_or_default(),
                    read_ball(cut.faces.stop.target_phase().map_err(invalid)?)?,
                ))
            })
            .transpose()?;
        let mut rows = Vec::with_capacity(target.len() + 1);
        let (mut text_bits, mut stop_bits) = (BitsReading::zero(), BitsReading::zero());
        let mut phase_total = target_phase.as_ref().map(|_| 0.0f64);
        let mut descent_total = target_phase.as_ref().map(|_| 0.0f64);
        let mut unsupported_rows = Vec::new();
        let mut supported_bits = 0.0;
        for row in 0..=target.len() {
            let branch = super::generator_application::receiving_branch(options, row)?;
            let text_reading = target
                .get(row)
                .map(|&class| {
                    let (p, phase) = text
                        .as_ref()
                        .ok_or_else(|| invalid("text comparison face"))?;
                    ratio_row(
                        row,
                        "text",
                        class,
                        p,
                        Some(phase),
                        target_phase.as_ref().map(|(t, _)| t.as_slice()),
                        branch,
                    )
                })
                .transpose()?;
            let stop_class = usize::from(row != target.len());
            let stop = ratio_row(
                row,
                "stop",
                stop_class,
                &stop_p,
                Some(&stop_phase),
                target_phase.as_ref().map(|(_, s)| s.as_slice()),
                branch,
            )?;
            for reading in text_reading.iter().chain([&stop]) {
                if reading.face == "text" {
                    text_bits.add(&reading.kl);
                } else {
                    stop_bits.add(&reading.kl);
                }
                if reading.support == RatioSupport::Supported {
                    supported_bits += reading.kl.centre_bits;
                } else if !unsupported_rows.contains(&row) {
                    unsupported_rows.push(row);
                }
                phase_total = phase_total
                    .zip(reading.phase_excess_bits)
                    .map(|(a, b)| a + b);
                descent_total = descent_total
                    .zip(reading.phase_descent_bits)
                    .map(|(a, b)| a + b);
            }
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
        let uniform = target.len() as f64 * (cut.faces.classes as f64).log2();
        let (order0, order1) =
            observer
                .stream
                .predictive_bits(target, requested.last_source_symbol, alphabet);
        let stop_baseline = receiving_rows as f64;
        let gain = |baseline: f64| baseline + stop_baseline - model.centre_bits;
        let per_row = |bits: f64| bits / receiving_rows as f64;
        let memory = &mut self
            .generator
            .as_mut()
            .ok_or_else(|| invalid("generator presentation"))?
            .readings;
        let (model_jet, phase_jet) = match memory.previous {
            Some((model_bits, phase_bits)) => (
                Some(model.centre_bits - model_bits),
                phase_total.zip(phase_bits).map(|(a, b)| a - b),
            ),
            None => (None, None),
        };
        memory.previous = Some((model.centre_bits, phase_total));
        let rows_unbounded = rows
            .iter()
            .filter(|row| {
                row.stop.kl.upper_bits.is_none()
                    || row
                        .text
                        .as_ref()
                        .is_some_and(|text| text.kl.upper_bits.is_none())
            })
            .count();
        let support = if unsupported_rows.is_empty() {
            RatioSupport::Supported
        } else if unsupported_rows.len() == receiving_rows {
            RatioSupport::Unsupported
        } else {
            RatioSupport::Partial
        };
        Ok(TargetReading {
            target_holon: cut.target_holon,
            text_positions: target.len(),
            receiving_rows,
            face: "comparison magnitude face p = softmax(Re s) with phase Im s / 2 (ratio return)",
            text: text_bits,
            stop: stop_bits,
            model: model.clone(),
            phase_excess_bits: phase_total,
            phase_descent_bits: descent_total,
            support,
            unsupported_rows,
            supported_bits,
            rows_unbounded,
            rows,
            model_bits_per_observation: model_jet,
            phase_excess_bits_per_observation: phase_jet,
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
        })
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

    /// Per-ring and per-contact fields at the current cut, with this observer's ring memory.
    fn navigation(
        &mut self,
        options: &GeneratorSessionOptions,
        requested: &ExteriorRequestMeasure,
        committed_source_steps: u64,
    ) -> Result<NavigationReading> {
        let machine = options.field.machine.compile().map_err(invalid)?;
        let current = self.body.inspect_current()?;
        let energies = site_energies(&current["joint"], machine.sites().len());
        let amplitudes = current["operator"]["declared_amplitudes"]
            .as_array()
            .map(|items| {
                items
                    .iter()
                    .map(|item| {
                        serde_json::from_value::<Rat>(item.clone())
                            .ok()
                            .or_else(|| item.as_str().and_then(parse_rat))
                            .and_then(|rat| rat.to_f64())
                    })
                    .collect::<Vec<_>>()
            })
            .unwrap_or_default();
        let port = |ports: &[crate::native::GeneratorPhasePort], site: &str| {
            ports.iter().find(|port| port.site_id == site).cloned()
        };
        let step_exponent = |ports: &[crate::native::GeneratorPhasePort], site: &str| {
            ports
                .iter()
                .filter(|port| port.site_id == site)
                .map(|port| port.step_exponent.unsigned_abs())
                .sum::<u64>()
        };
        let receiving_rows = options.receiver.aperture as u64;
        let memory = &mut self
            .generator
            .as_mut()
            .ok_or_else(|| invalid("generator presentation"))?
            .readings;
        let mut sites = Vec::with_capacity(machine.sites().len());
        for (index, site) in machine.sites().iter().enumerate() {
            let source_exponent = step_exponent(&options.source.clocks, site.id());
            let committed = committed_source_steps * source_exponent;
            let clock = port(&options.source.clocks, site.id());
            let step = clock.as_ref().map_or(0, |p| p.step_exponent);
            let origin =
                site.phase_origin_exponent() + clock.as_ref().map_or(0, |p| p.origin_exponent);
            let phase_exponent = i64::try_from(committed_source_steps)
                .ok()
                .and_then(|ticks| step.checked_mul(ticks))
                .and_then(|value| value.checked_add(origin))
                .unwrap_or(i64::MAX);
            let phase = site.phase();
            let energy = energies.get(index).copied().flatten();
            let (increment, variance, recorded) = match energy {
                Some(energy) => {
                    let entry = memory
                        .rings
                        .entry(site.id().to_owned())
                        .or_insert(RingSummary {
                            energy,
                            ticks: committed_source_steps,
                            count: 0,
                            mean: 0.0,
                            m2: 0.0,
                        });
                    let ticks = committed_source_steps.saturating_sub(entry.ticks);
                    let increment = (ticks > 0).then(|| (energy - entry.energy) / ticks as f64);
                    if let Some(value) = increment {
                        entry.count += 1;
                        let delta = value - entry.mean;
                        entry.mean += delta / entry.count as f64;
                        entry.m2 += delta * (value - entry.mean);
                    }
                    entry.energy = energy;
                    entry.ticks = committed_source_steps;
                    let variance = (entry.count > 1).then(|| entry.m2 / entry.count as f64);
                    (increment, variance, entry.count as usize)
                }
                None => (None, None, 0),
            };
            let mut reading = SiteNavigation {
                site: site.id().to_owned(),
                source: site.is_source(),
                receiver: site.is_receiver(),
                ticks: committed_source_steps,
                committed_source_steps: committed,
                request_source_steps: requested.source_cells as u64 * source_exponent,
                receiving_steps: receiving_rows * step_exponent(&options.receiver.ports, site.id()),
                phase_exponent,
                tick_increment_exponent: step,
                tick_increment_variance: 0.0,
                cayley_parameter: phase.parameter().to_string(),
                closure_period: site.closure(),
                committed_windings: None,
                lock_address_depth: None,
                turn: "not a rational turn: no closure witness for this Cayley step",
                current_energy: energy,
                energy_increment_per_tick: increment,
                energy_increment_variance: variance,
                recorded_observations: recorded,
            };
            if let Some(period) = site.closure() {
                if let Ok(winding) = phase.lifted_winding(period) {
                    let turns = BigInt::from(winding.lifted) * BigInt::from(committed)
                        / BigInt::from(period as u64);
                    reading.committed_windings = Some(turns.to_string());
                    reading.turn = "rational turn: lifted winding per closure period";
                    if winding.lifted > 0 {
                        if let Ok(address) = holonics::geometry::winding::LockAddress::from_ratio(
                            &BigInt::from(winding.lifted),
                            &BigInt::from(period as u64),
                        ) {
                            reading.lock_address_depth = Some(address.depth().to_string());
                        }
                    }
                }
            }
            sites.push(reading);
        }
        let centres = site_centres(&current["joint"], machine.sites().len());
        let contacts = machine
            .arcs()
            .iter()
            .enumerate()
            .map(|(index, arc)| ContactReading {
                arc: arc.id().to_owned(),
                source: arc.source().to_owned(),
                receiver: arc.receiver().to_owned(),
                amplitude: (amplitudes.len() == machine.arcs().len())
                    .then(|| amplitudes[index])
                    .flatten(),
                interface_contrast: centres
                    .get(arc.source_index())
                    .zip(centres.get(arc.receiver_index()))
                    .and_then(|(a, b)| {
                        (a.len() == b.len() && !a.is_empty())
                            .then(|| a.iter().zip(b).map(|(x, y)| (x - y).powi(2)).sum())
                    }),
            })
            .collect();
        Ok(NavigationReading {
            request_source_steps: requested.source_cells,
            committed_source_steps,
            sites,
            contacts,
        })
    }
}

/// Real coordinates of each ring's boundary current centre (12 per site), from the joint
/// readout `{"center": [{"real", "imaginary"}, ...]}`; empty when the readout differs.
pub(super) fn site_centres(joint: &Value, sites: usize) -> Vec<Vec<f64>> {
    let Some(center) = joint["center"].as_array() else {
        return Vec::new();
    };
    let values = center
        .iter()
        .flat_map(|z| {
            ["real", "imaginary"].map(|part| {
                serde_json::from_value::<Rat>(z[part].clone())
                    .ok()
                    .and_then(|rat| rat.to_f64())
            })
        })
        .collect::<Option<Vec<f64>>>();
    let Some(values) = values else {
        return Vec::new();
    };
    if values.len() < 12 * sites {
        return Vec::new();
    }
    values[..12 * sites]
        .chunks_exact(12)
        .map(<[f64]>::to_vec)
        .collect()
}

pub(super) fn site_energies(joint: &Value, sites: usize) -> Vec<Option<f64>> {
    let centres = site_centres(joint, sites);
    (0..sites)
        .map(|site| {
            centres
                .get(site)
                .map(|values| values.iter().map(|v| v * v).sum())
        })
        .collect()
}
