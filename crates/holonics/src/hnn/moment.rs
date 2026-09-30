//! **The source moment: phase-binned counts on closing source rings, and its capacity.**
//!
//! [definition] The source enters as phase-carried moments, never as a tape (design (a), "The law
//! of one passage", `ingest`). For each cell `x_k` (the exterior chart's one-hot vector `e_code`)
//! the lift point takes its selective step ([`crate::hnn::Field::selective_step`]), and on every
//! source ring `g ∈ 𝒮`, at its phase `c = τ_g mod d_g` after the step:
//!
//! ```text
//! M_g[c] += x_k                                      phase-binned counts           (d_g × |A|)
//! C_g(δ)[c] += x_k ⊗ buf[δ],  δ ∈ Δ                    offset counts on the exterior (d_g × |A|²)
//! buf ← shift(buf, x_k)                               the pair buffer: a cell until its pairs are counted
//! n_g = Σ_(c,x) M_g[c,x] ,  n_(g,δ) = Σ_(c,x,a) C_g(δ)[c,x,a]                        populations
//! m̃_g = Σ_c P_g^(−c) (E_g M_g[c] ν̂(n_g) + Σ_δ Σ_(x,a) C_g(δ)[c,x,a] ν̂(n_(g,δ)) E_g^(δ)(e_x ⊗ e_a))   never stored
//! s_g(0) = P_g^(τ_g) m̃_g                                          the word's open on g ∈ 𝒮
//! ```
//!
//! [definition; agent-inferred, U6] **The open is normalized and reads no window** (the
//! [encoding pin](../../../../research/records/2026-09-29_HOLONIC_ENCODING_FOR_THE_FIELD_PINNED_BEFORE_ITS_RUN.md)
//! §1.4; Lean `HNN/IndexedOpen.{pairPopulation, pairNormalized}`, `HNN/Encoding.whole_pair_read_*`):
//! the marginal reads the phase counts over their population, and the pair port reads the whole
//! oriented offset moment over its pair population, so the open's amplitude does not grow with the
//! ingested cells (`normalized_open_population_invariant`) and depends on no raw cell. The read at
//! the address the buffer supplied (the primary's ruling B, the first repair's open) conditioned the
//! open on the last `max Δ` raw cells, a depth-limited context window on the source; it is retired.
//! Each `1/n` is carried by the [`PopulationChart`] on its declared lattice, so the open stays
//! dyadic and the card carries it in parity; an empty population contributes nothing.
//!
//! [definition; agent-inferred, September 30] **One passage, its transported weights**
//! ([`SourceMoment::continued`], [`SourceMoment::phase_weights`]; Lean `HNN/IndexedOpen`, "The
//! passage continued by its section"; the
//! [record](../../../../research/records/2026-09-30_THE_PASSAGE_LAW_THE_SECTION_CONTINUES_THE_REQUEST_AND_THE_TRANSPORT_WEIGHS_ITS_FRONTIER.md)).
//! A generated section continues the request's passage along the receiving ring's clock, so its
//! locked data are counted into the request's phase counts at their residues: one span, one tube.
//! Each crossing's datum is carried to the reading frame by the source navigator's transport, a
//! rotation–dilation of modulus `ρ_g ∈ (0, 1]` a tick (the constitution's
//! [`ConstitutionRead::transport`], one at the founding), and the span is read over its
//! transported mass: a datum `a` ticks old at the span's end weighs `ρ^a / Σ_k ρ^(a_k)`, the same in
//! every frame, whichever side of the request's last tick it lies on. At `ρ = 1` (a closing rotor
//! ring, nothing lost) every datum weighs `ν̂(n + v)`, the one population. Below one the span's
//! frontier weighs most and every crossing still enters: the lossless reading gives every crossing's
//! term in a phase-carried face the same modulus at every lag, so no reading marks the frontier a
//! continuation depends on (Lean `lossless_term_modulus`), and the transport's dissipation, a locus
//! the executed comparison learns (`hnn::executed`), is what marks it. The weights read the ages
//! from the phases, exact within one turn; a passage over more than one turn is refused below
//! modulus one (the leaky count it needs is owed). The retired reading, the section over its own
//! population `v`, weighed a section datum `n/v` times a request cell.
//!
//! [definition; agent-inferred, September 30] **Read from a station** (`hnn::prediction`, "A
//! candidate reads the span from its own station"; Lean `HNN/IndexedOpen.framedWeight`): a
//! candidate at station `j` weighs each datum by its two-sided transport distance,
//! `ρ^|τ_j − τ_k| / Σ_l ρ^|τ_j − τ_l|`, because the section is a joint field. [`SourceMoment::phase_weights`]
//! reads the span from its last datum, which is station `j`'s framed law exactly when no datum lies
//! after `j` (`framed_weight_one_sided`), and in every frame at modulus one; the bank reads each
//! candidate from its own station (`BankPlacement`), and the readout's one anchor is refused below
//! modulus one where a placed datum lies after an open station (`Refinement::anchor_frames`).
//!
//! [definition; agent-inferred, U6] **The pair buffer is the offset moment's one-step state**
//! (Lean `Transport/SourceMoment.streamStep`'s previous value, `HNN/Moment.SourceDecl.StreamState`'s
//! window): the offset-`δ` pair of cell `k` needs cell `k − δ`, so a cell stays in the buffer for
//! `max Δ` ingests until every pair it joins is counted, and then leaves. No receiver reads the
//! buffer, and nothing of the source is discarded by length: every cell is counted once in every
//! source ring's phase counts, and every pair at every declared offset in its offset counts, over the
//! moment's whole passage (the window tests in `hnn::tests::moment`).
//!
//! Every slot is sized once from the field; nothing grows with the cells but the counts'
//! `O(log n)` bits. Ingest stops at a carry-out of the joint clock: the aeon boundary belongs to the
//! winding, not to a caller counter.
//!
//! [definition] **The pair port** [`PairPort`] `E_g^(δ) = Σ_(ρ<m) e_ρ (a_ρ·x)(b_ρ·y)` is carried
//! factored on the exterior pair chart `x ⊗ y` (`x` the current cell, `y` the earlier). The offset
//! counts on the exterior chart are independent of the learned `E` and `E^(δ)`, so the moment stays
//! tape-free when either changes (Lean `HNN/Moment.exteriorOffset_independent_of_E`).
//!
//! [established-bounded; implemented-exact] **The capacity** ([`capacity`], design (a), R3 H1):
//! the persisting source state after `n` cells takes at most
//!
//! ```text
//! N(n) = |A|^(max Δ) · ∏_g (2n + d_g) · ∏_(g∈𝒮) [ C(n + d_g|A| − 1, d_g|A| − 1) · ∏_(δ∈Δ) C(n − δ + d_g|A|² − 1, d_g|A|² − 1) ]
//! ```
//!
//! values. `n*` is the least `n` with `N(n) < |A|^n`; past it the source → state map is not
//! injective (pigeonhole), so the moment is lossy by construction, and by convexity at every
//! `n ≥ n*`. It is found by bisection on exact integers and certified at `n* − 1` and `n*`
//! (Lean `HNN/Moment.moment_capacity`). The binomials are exact products formed by binary
//! splitting. For `n < δ` there are no offset counts, and the factor is 1.
//!
//! | Lean `HNN/Moment` | Rust |
//! |---|---|
//! | `closingRing_moment_is_phaseBinned`, `selective_position` | [`SourceMoment::ingest`] |
//! | `encoderMoment_contract` (`m̃_g = ⟨M_g, E_g⟩`) | [`SourceMoment::encode`] |
//! | `encoder_covector_tape_free` | [`SourceMoment::encoder_covector`] |
//! | `exteriorOffset_independent_of_E` | [`SourceMoment::offset_counts`], [`PairPort::apply_table`] |
//! | `HNN/IndexedOpen.{normalized_phase_counts_mass, normalized_open_population_invariant, normalized_zero_population}`; `HNN/Encoding.{whole_pair_read_counts, whole_pair_read_population_invariant, whole_pair_read_tape_free}` (the open reads no window) | [`PopulationChart`], [`SourceMoment::normalized_counts`], [`SourceMoment::offset_table`], [`SourceMoment::encode`] |
//! | `moment_capacity` | [`capacity`], [`Capacity`] |
//! | `HNN/Prediction.{placed_at_station, joint_residue_determines_position}` (a locked datum at its station's residue; a ring of period `∏ dᵢ`, pairwise coprime, places each datum at its joint residue class); `HNN/IndexedOpen.{passage_population, passage_read, passage_weight_one_population, separate_populations_ratio, transportedWeight, transported_weight_mass, transported_weight_frame_invariant, transported_weight_unitary, passage_weight_split_invariant, decayed_weight_antitone, decayed_weight_frame_free, decayed_weight_lossless, lossless_term_modulus, dissipative_term_modulus}` (the section continues the passage; each datum at its transported weight) | [`SourceMoment::continued`], [`SourceMoment::phase_weights`], [`SourceMoment::open_parts`] |
//! | `HNN/IndexedOpen.{framedWeight, framed_weight_mass, framed_weight_pos, framed_weight_one_sided, framed_weight_ratio, framed_weight_le_pow, oneway_later_weight_ratio, framed_weight_symmetric, framed_weight_translation, framed_weight_lossless}` (a candidate reads the span from its own station, each datum at its two-sided transport distance; the one-way law on data no later than the station) | `hnn::prediction::BankPlacement::{weights, storage, modulus_derivative}`; [`SourceMoment::phase_weights`] is the law read from the span's last datum |

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::hnn::HnnError;
use crate::hnn::field::{ConstitutionRead, Current, Field};
use crate::ratio::Rat;
use crate::ratio::linear::ExactRatMatrix;
use crate::ratio::linear::vector::integral;

// -------------------------------------------------------------------------------------------
// the capacity

/// [established-bounded; implemented-exact] **The capacity crossover** of a declared source state:
/// `n*` with its exact certificate. [definition; agent-inferred] **Its scope: the re-keys.** The
/// lift factor `2n + d_g` counts ring `g`'s own steps and carries over `n` cells from one opening.
/// Each aeon boundary within the `n` cells re-keys the ring, a jump of its phase class by less than
/// `d_g` that keeps its winding, so after `b` boundaries the lift takes at most `2n + (b + 1)d_g`
/// values: a factor the counted `N(n)` does not carry (review C4). Campaign 1's mean aeon on uniform
/// bytes is `1,281,280/1,077 ≈ 1,190` cells (design (a)), so about five boundaries fall within
/// `n* = 6,148` cells, and the factor is below `1 + 5·13/12,296` per ring: over the four rings it
/// moves `log₂N(n)` by less than a thirtieth of a bit. A reading of the capacity's scope; the
/// refusal below `n*` uses the counted `N(n)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Capacity {
    n_star: u64,
    periods: Vec<u64>,
    sources: Vec<usize>,
    alphabet: usize,
    offsets: Vec<usize>,
}

impl Capacity {
    /// `n*`: the least `n` with `N(n) < |A|^n`.
    pub fn n_star(&self) -> u64 {
        self.n_star
    }

    /// **`N(n)`**, the count of distinct persisting source states after `n` cells, exactly.
    pub fn states(&self, n: u64) -> BigUint {
        state_count(
            n,
            &self.periods,
            &self.sources,
            self.alphabet,
            &self.offsets,
        )
    }

    /// Whether the moment is lossy at `n` by counting: `N(n) < |A|^n`.
    pub fn lossy_at(&self, n: u64) -> bool {
        lossy(
            n,
            &self.periods,
            &self.sources,
            self.alphabet,
            &self.offsets,
        )
    }

    /// The source-state bits `⌈log₂ N(n)⌉` as a reading, against the source's `n log₂|A|`.
    pub fn state_bits(&self, n: u64) -> u64 {
        self.states(n).bits()
    }
}

/// **The capacity `n*`** of source rings of the declared periods over `|A|` with offsets `Δ`, by
/// bisection on exact integers, certified at `n* − 1` and `n*`.
pub fn capacity(
    periods: &[u64],
    sources: &[usize],
    alphabet: usize,
    offsets: &[usize],
) -> Result<Capacity, HnnError> {
    if alphabet < 2 {
        return Err(HnnError::NonpositiveDeclaration);
    }
    let test = |n: u64| lossy(n, periods, sources, alphabet, offsets);
    // N(0) ≥ 1 = |A|⁰, so 0 is never lossy; double until lossy, then bisect.
    let (mut below, mut above) = (0u64, 1u64);
    while !test(above) {
        below = above;
        above = above.checked_mul(2).ok_or(HnnError::CountOverflow)?;
    }
    while above - below > 1 {
        let middle = below + (above - below) / 2;
        if test(middle) {
            above = middle;
        } else {
            below = middle;
        }
    }
    debug_assert!(test(above) && !test(above - 1));
    Ok(Capacity {
        n_star: above,
        periods: periods.to_vec(),
        sources: sources.to_vec(),
        alphabet,
        offsets: offsets.to_vec(),
    })
}

fn lossy(n: u64, periods: &[u64], sources: &[usize], alphabet: usize, offsets: &[usize]) -> bool {
    let bound = BigUint::from(alphabet).pow(u32::try_from(n).expect("a declared population fits"));
    state_count(n, periods, sources, alphabet, offsets) < bound
}

fn state_count(
    n: u64,
    periods: &[u64],
    sources: &[usize],
    alphabet: usize,
    offsets: &[usize],
) -> BigUint {
    let a = BigUint::from(alphabet);
    let window = offsets.iter().copied().max().unwrap_or(0);
    let mut count = a.pow(u32::try_from(window).expect("a declared offset fits"));
    for &period in periods {
        count *= BigUint::from(2 * n + period);
    }
    for &source in sources {
        let d = BigUint::from(periods[source]);
        let first = &d * &a;
        count *= binomial(&(BigUint::from(n) + &first - 1u32), &(&first - 1u32));
        let second = &first * &a;
        for &offset in offsets {
            let total = n.saturating_sub(offset as u64);
            count *= binomial(&(BigUint::from(total) + &second - 1u32), &(&second - 1u32));
        }
    }
    count
}

/// `C(m, k)` exactly: the product of `k` consecutive integers over `k!`, each by binary splitting.
fn binomial(m: &BigUint, k: &BigUint) -> BigUint {
    if k > m {
        return BigUint::zero();
    }
    let k = std::cmp::min(k.clone(), m - k);
    let top = m - &k + 1u32;
    range_product(&top, m) / range_product(&BigUint::one(), &k)
}

/// `∏_(i=low)^(high) i`, `1` when empty, by binary splitting.
fn range_product(low: &BigUint, high: &BigUint) -> BigUint {
    if low > high {
        return BigUint::one();
    }
    if high - low < BigUint::from(8u32) {
        let mut product = BigUint::one();
        let mut i = low.clone();
        while &i <= high {
            product *= &i;
            i += 1u32;
        }
        return product;
    }
    let middle = (low + high) >> 1;
    range_product(low, &middle) * range_product(&(middle + 1u32), high)
}

// -------------------------------------------------------------------------------------------
// the pair port

/// [definition] **The pair port** `E^(δ) = Σ_(ρ<m) e_ρ (a_ρ·x)(b_ρ·y)`, factored: its outputs
/// `e_ρ ∈ ℚ^(2d_g)`, its current-cell reads `a_ρ ∈ ℚ^|A|` and its earlier-cell reads `b_ρ ∈ ℚ^|A|`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairPort {
    outputs: Vec<Vec<Rat>>,
    current: Vec<Vec<Rat>>,
    earlier: Vec<Vec<Rat>>,
}

impl PairPort {
    /// A rank-`m` pair port; the three factor families must have `m` members each, the outputs one
    /// width and the reads one width.
    pub fn new(
        outputs: Vec<Vec<Rat>>,
        current: Vec<Vec<Rat>>,
        earlier: Vec<Vec<Rat>>,
    ) -> Result<Self, HnnError> {
        let rank = outputs.len();
        for (found, what) in [
            (current.len(), "pair port reads"),
            (earlier.len(), "pair port reads"),
        ] {
            if found != rank {
                return Err(HnnError::Shape {
                    what,
                    expected: rank,
                    found,
                });
            }
        }
        let width = outputs.first().map_or(0, Vec::len);
        let chart = current.first().map_or(0, Vec::len);
        if outputs.iter().any(|e| e.len() != width)
            || current.iter().chain(&earlier).any(|a| a.len() != chart)
        {
            return Err(HnnError::Shape {
                what: "pair port factor widths",
                expected: width,
                found: chart,
            });
        }
        Ok(Self {
            outputs,
            current,
            earlier,
        })
    }

    pub fn rank(&self) -> usize {
        self.outputs.len()
    }

    pub fn outputs(&self) -> &[Vec<Rat>] {
        &self.outputs
    }

    pub fn current_reads(&self) -> &[Vec<Rat>] {
        &self.current
    }

    pub fn earlier_reads(&self) -> &[Vec<Rat>] {
        &self.earlier
    }

    /// **`E^(δ)` on one phase of the whole normalized offset moment** (module header; Lean
    /// `HNN/Encoding.whole_pair_read_counts`): with the offset counts `C[c, x, a]` and the pair
    /// population's chart weight `ν̂`, `Σ_ρ e_ρ Σ_(x,a) C[c, x, a] ν̂ a_ρ[x] b_ρ[a]`, over the nonzero
    /// counts only. No address is read.
    pub fn apply_table(
        &self,
        table: &OffsetTable,
        phase: usize,
        alphabet: usize,
        width: usize,
    ) -> Vec<Rat> {
        let mut weights = vec![Rat::zero(); self.rank()];
        for (slot, &count) in table.phase(phase, alphabet).iter().enumerate() {
            if count == 0 {
                continue;
            }
            let (x, a) = (slot / alphabet, slot % alphabet);
            let count = Rat::from_integer(BigInt::from(count)) * &table.weight;
            for (rho, weight) in weights.iter_mut().enumerate() {
                *weight += &count * &self.current[rho][x] * &self.earlier[rho][a];
            }
        }
        let mut output = vec![Rat::zero(); width];
        for (weight, e) in weights.iter().zip(&self.outputs) {
            if weight.is_zero() {
                continue;
            }
            for (value, entry) in output.iter_mut().zip(e) {
                *value += weight * entry;
            }
        }
        output
    }
}

// -------------------------------------------------------------------------------------------
// the population chart and the indexed column

/// [definition; agent-inferred] **The population chart** (the primary's ruling B: the first repair's
/// normalized open, carried by the lattice word's rule for an inverse): `1/n` read on the lattice
/// `2^(−L_ν)`, `ν̂(n) = ⌊2^(L_ν)/n + ½⌋ 2^(−L_ν)` (nearest, ties up) with `|ν̂ − 1/n| ≤ 2^(−L_ν−1)`,
/// and `ν̂(0) = 0` (an unsupported fibre contributes nothing, Lean
/// `HNN/IndexedOpen.normalized_zero_population`). `L_ν = ⌈log₂(2 L_R n*)⌉` over the finest
/// admitted grain `L_R` and the declared population `n*`, so a normalized table of population
/// `n ≤ n*` moves by at most `n 2^(−L_ν−1) ≤ 1/(4 L_R)` in ℓ1 against the exact ratios, below the
/// grain for unit-scale ports (the rule's assumption, as `L_ℓ`'s). The word stays dyadic, so the
/// card carries the same chart and the open stays in parity.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PopulationChart {
    exponent: u32,
}

impl PopulationChart {
    /// The chart a field declares by rule.
    pub fn of(field: &Field) -> Self {
        let grain = field
            .receivers()
            .iter()
            .filter_map(|receiver| receiver.tolerance.recip().ceil().to_integer().to_u64())
            .max()
            .unwrap_or(1);
        let reach = BigUint::from(2u32) * BigUint::from(grain) * BigUint::from(field.population());
        Self {
            exponent: u32::try_from(crate::compression::cost::ceil_log2(&reach))
                .expect("a population chart within 32 bits"),
        }
    }

    /// `L_ν`.
    pub fn exponent(&self) -> u32 {
        self.exponent
    }

    /// `⌊2^(L_ν)/n + ½⌋`, the chart's numerator; `0` at `n = 0`.
    pub fn numerator(&self, population: u64) -> u64 {
        if population == 0 {
            return 0;
        }
        let scale = 1u128 << self.exponent;
        let n = u128::from(population);
        u64::try_from((2 * scale + n) / (2 * n)).expect("a chart numerator within 64 bits")
    }

    /// `ν̂(n)`, exact.
    pub fn value(&self, population: u64) -> Rat {
        Rat::new(
            BigInt::from(self.numerator(population)),
            BigInt::one() << self.exponent as usize,
        )
    }

    /// **A weight read on the chart**: `⌊2^(L_ν) w + ½⌋ 2^(−L_ν)` (nearest, ties up), within
    /// `2^(−L_ν−1)` of `w`; at `w = 1/n` it is `ν̂(n)`.
    pub fn chart(&self, weight: &Rat) -> Rat {
        let scale = Rat::from_integer(BigInt::one() << self.exponent as usize);
        let half = Rat::new(BigInt::one(), BigInt::from(2));
        (weight * &scale + half).floor() / scale
    }

    /// The certified residual `|ν̂ − 1/n| ≤ 2^(−L_ν−1)`.
    pub fn residual(&self) -> Rat {
        Rat::new(BigInt::one(), BigInt::one() << (self.exponent as usize + 1))
    }
}

/// [definition] **One offset's whole normalized offset moment** (module header): the offset counts
/// `C_g(δ)[c, x, a]` (phase-major, the current cell `x` then the earlier `a`), their pair population
/// `n_(g,δ)` and its chart weight `ν̂(n_(g,δ))`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OffsetTable {
    pub counts: Vec<u64>,
    pub population: u64,
    pub weight: Rat,
}

impl OffsetTable {
    /// The phase's counts `C_g(δ)[c, ·, ·]`, row the current cell.
    pub fn phase(&self, phase: usize, alphabet: usize) -> &[u64] {
        let block = alphabet * alphabet;
        &self.counts[phase * block..(phase + 1) * block]
    }
}

// -------------------------------------------------------------------------------------------
// the moment

/// One source ring's counts.
#[derive(Clone, Debug, PartialEq, Eq)]
struct RingCounts {
    ring: usize,
    period: usize,
    /// `M_g`: `d_g × |A|`.
    first: Vec<u64>,
    /// `C_g(δ)` per declared offset: `d_g × |A| × |A|`.
    offset: Vec<Vec<u64>>,
    /// The ring's phase at the open.
    start: u64,
    /// The ring's phase after the last ingested cell (the request's last tick `τ_g`).
    end: u64,
    /// The ring's advances since the open.
    ticks: u64,
    /// The ticks a continuing section extends the passage past `end` (`SourceMoment::continued`).
    extent: u64,
}

/// What one ingest did: the cells consumed, and whether it stopped at the joint clock's carry-out.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ingested {
    pub cells: usize,
    pub carry_out: bool,
}

/// [definition] **The source moment on the closing source rings.** Sized once from the [`Field`]
/// (guard 1): every slot exists from the open, and ingest only adds to counts and overwrites the
/// window. It holds no cell list and no per-occurrence record.
///
/// It opens only on a declared [`Field`], and `Field::declare` builds only closing rotor rings, so
/// a rotation transport has no ingest port. The guarantee is structural; the doctest shows a
/// transport refused where the field goes (`E0308`, a type mismatch):
///
/// ```compile_fail,E0308
/// use holonics::hnn::{Current, SourceMoment};
/// use holonics::navigator::Transport;
/// fn ingest_on_a_rotation(rotation: &Transport, current: &Current) -> SourceMoment {
///     SourceMoment::open(rotation, current)
/// }
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceMoment {
    alphabet: usize,
    offsets: Vec<usize>,
    rings: Vec<RingCounts>,
    window: Vec<Option<usize>>,
    cursor: usize,
    cells: u64,
    opening: Vec<BigInt>,
}

impl SourceMoment {
    /// **Open a moment** at the current lift point: every count zero, the window empty.
    pub fn open(field: &Field, current: &Current) -> Self {
        let alphabet = field.alphabet();
        let offsets = field.offsets().to_vec();
        let rings = field
            .sources()
            .iter()
            .map(|&ring| {
                let period = field.ring(ring).placements().len();
                let phase = current
                    .phase(field, ring)
                    .expect("a declared source ring reads its phase");
                RingCounts {
                    ring,
                    period,
                    first: vec![0; period * alphabet],
                    offset: offsets
                        .iter()
                        .map(|_| vec![0; period * alphabet * alphabet])
                        .collect(),
                    start: phase,
                    end: phase,
                    ticks: 0,
                    extent: 0,
                }
            })
            .collect();
        let window = vec![None; offsets.iter().copied().max().unwrap_or(0)];
        Self {
            alphabet,
            offsets,
            rings,
            window,
            cursor: 0,
            cells: 0,
            opening: current.lift().to_vec(),
        }
    }

    /// **Ingest cells in order**: the lift point's selective step, then the phase-binned and offset
    /// counts on every source ring, then the window. Stops after the cell whose step carries the
    /// joint clock out, and reports it.
    pub fn ingest(
        &mut self,
        field: &Field,
        current: &mut Current,
        cells: &[usize],
    ) -> Result<Ingested, HnnError> {
        let a = self.alphabet;
        for (consumed, &code) in cells.iter().enumerate() {
            let step = current.step(field, code)?;
            for counts in &mut self.rings {
                let phase = current.phase(field, counts.ring)? as usize;
                counts.end = phase as u64;
                counts.ticks += u64::from(step.ticks[counts.ring]);
                bump(&mut counts.first[phase * a + code])?;
                for (index, &offset) in self.offsets.iter().enumerate() {
                    if let Some(earlier) = earlier(&self.window, self.cursor, offset) {
                        bump(&mut counts.offset[index][phase * a * a + code * a + earlier])?;
                    }
                }
            }
            if !self.window.is_empty() {
                self.window[self.cursor] = Some(code);
                self.cursor = (self.cursor + 1) % self.window.len();
            }
            self.cells += 1;
            if step.carry_out {
                return Ok(Ingested {
                    cells: consumed + 1,
                    carry_out: true,
                });
            }
        }
        Ok(Ingested {
            cells: cells.len(),
            carry_out: false,
        })
    }

    /// [definition; agent-inferred, September 30] **The passage continued by its section**
    /// (`hnn::prediction`'s header, "The section continues the request's passage"; Lean
    /// `HNN/IndexedOpen.{passage_population, passage_read, passage_weight_one_population}`): the
    /// request's moment with a refinement's locked data counted into the same phase counts at their
    /// stations' residues. Station `j` lies at the receiving ring's clock one tick a station past the
    /// request's last tick (`hnn::prediction`'s header), so its datum is counted at the residue
    /// `τ_R + 1 + j (mod d_R)`: the same phase-carried law as the request's, `m = Σ Ĝ(τ)⁻¹ E u`, at
    /// the same frame, and in the same population. The request and its section are one span of the
    /// receiving ring's clock (one tube), whose transport is the ring's rotation, unit modulus on
    /// every node, so every crossing of the span is carried to the reading frame with the same weight
    /// and the open reads the span's counts over its one population `n + v`
    /// ([`SourceMoment::encode`]): the relative weight of two crossings does not depend on which
    /// side of the request's last tick they lie (the September 30 located cause: a section read over
    /// its own population weighed its datum `n/v` times a request cell's, `40` at the open section).
    /// An unlocked station places nothing. No offset pair of the section is counted (the pair
    /// port reads the request's pairs over their own population, as before), and nothing is kept
    /// but the counts: `v` locked data are `v` more counts on the receiving ring. Refused unless
    /// `ring` is a source ring.
    pub fn continued(
        &self,
        field: &Field,
        current: &Current,
        ring: usize,
        cells: &[Option<usize>],
    ) -> Result<Self, HnnError> {
        let mut passage = self.clone();
        // Nothing placed continues nothing, on any ring (the request's own passage).
        if cells.iter().all(Option::is_none) {
            return Ok(passage);
        }
        let a = passage.alphabet;
        let phase = current.phase(field, ring)? as usize;
        let counts = passage
            .rings
            .iter_mut()
            .find(|counts| counts.ring == ring)
            .ok_or(HnnError::MissingSourcePort { ring })?;
        let period = counts.period;
        let mut placed = 0u64;
        for (station, cell) in cells.iter().enumerate() {
            let Some(code) = *cell else {
                continue;
            };
            if code >= a {
                return Err(HnnError::CellOutside { code, alphabet: a });
            }
            bump(&mut counts.first[((phase + 1 + station) % period) * a + code])?;
            counts.extent = counts.extent.max(station as u64 + 1);
            placed += 1;
        }
        passage.cells += placed;
        Ok(passage)
    }

    /// `|A|`, the exterior chart the moment counts on.
    pub fn alphabet(&self) -> usize {
        self.alphabet
    }

    /// The cells ingested since the open, `n`.
    pub fn cells(&self) -> u64 {
        self.cells
    }

    /// The lift point at the open.
    pub fn opening(&self) -> &[BigInt] {
        &self.opening
    }

    /// The source rings, in order.
    pub fn source_rings(&self) -> Vec<usize> {
        self.rings.iter().map(|counts| counts.ring).collect()
    }

    fn counts(&self, ring: usize) -> Result<&RingCounts, HnnError> {
        self.rings
            .iter()
            .find(|counts| counts.ring == ring)
            .ok_or(HnnError::MissingSourcePort { ring })
    }

    /// `M_g[c]`: the counts of each exterior class at phase `c` of source ring `g`.
    pub fn phase_counts(&self, ring: usize, phase: usize) -> Result<&[u64], HnnError> {
        let counts = self.counts(ring)?;
        let a = self.alphabet;
        Ok(&counts.first[phase * a..(phase + 1) * a])
    }

    /// `C_g(δ)[c]`: the offset counts at phase `c` of source ring `g`, row the current cell.
    pub fn offset_counts(
        &self,
        ring: usize,
        offset: usize,
        phase: usize,
    ) -> Result<&[u64], HnnError> {
        let counts = self.counts(ring)?;
        let index = self
            .offsets
            .iter()
            .position(|declared| *declared == offset)
            .ok_or(HnnError::Offset { offset })?;
        let block = self.alphabet * self.alphabet;
        Ok(&counts.offset[index][phase * block..(phase + 1) * block])
    }

    /// The pair buffer's cells, most recent first (`buf[1], buf[2], …`), `None` before enough
    /// cells: the offset moment's one-step state (module header), which no receiver reads.
    pub fn window(&self) -> Vec<Option<usize>> {
        (1..=self.window.len())
            .map(|offset| earlier(&self.window, self.cursor, offset))
            .collect()
    }

    /// **The population `n_g = Σ_(c,x) M_g[c, x]`** of a source ring's phase counts.
    pub fn population(&self, ring: usize) -> Result<u64, HnnError> {
        Ok(self.counts(ring)?.first.iter().sum())
    }

    /// **The pair population `n_(g,δ) = Σ_(c,x,a) C_g(δ)[c, x, a]`** of a source ring's offset
    /// counts at a declared offset.
    pub fn pair_population(&self, ring: usize, offset: usize) -> Result<u64, HnnError> {
        let index = self
            .offsets
            .iter()
            .position(|declared| *declared == offset)
            .ok_or(HnnError::Offset { offset })?;
        Ok(self.counts(ring)?.offset[index].iter().sum())
    }

    /// [definition; agent-inferred, September 30] **The passage's transported weights** on one
    /// source ring (module header, "One passage, its transported weights"; Lean
    /// `HNN/IndexedOpen.{transportedWeight, transported_weight_unitary, decayed_weight_frame_free}`):
    /// at each phase `c`, the weight a datum counted there enters the open with. At the navigator's
    /// transport modulus `ρ = 1` it is the one population's `ν̂(n)` at every occupied phase. At
    /// `0 < ρ < 1` a datum at phase `c` is `a(c) = (τ + e − c) mod d` ticks old at the passage's
    /// end (`τ` the request's last tick, `e` the section's extent), and weighs
    /// `ρ^(a(c)) / Σ_(c′) n(c′) ρ^(a(c′))` read on the population chart's lattice
    /// ([`PopulationChart::chart`]); the ratio is the same in every frame at or after the span's last
    /// datum, so the end is only its reference: the station-framed law of a station no datum
    /// follows (module header, "Read from a station"). The ages are read from the phases, which
    /// identify the ticks only within one turn:
    /// a passage over more than `d` ticks, or one re-keyed within its span, is refused at `ρ < 1`
    /// ([`HnnError::AliasedAges`]); zero at an empty phase.
    pub fn phase_weights(&self, field: &Field, ring: usize, modulus: &Rat) -> Result<Vec<Rat>, HnnError> {
        let counts = self.counts(ring)?;
        let a = self.alphabet;
        let d = counts.period;
        let chart = PopulationChart::of(field);
        let populations: Vec<u64> = (0..d)
            .map(|c| counts.first[c * a..(c + 1) * a].iter().sum())
            .collect();
        if !modulus.is_positive() || *modulus > Rat::one() {
            return Err(HnnError::Transport {
                ring,
                modulus: modulus.clone(),
            });
        }
        if modulus.is_one() {
            let nu = chart.value(populations.iter().sum());
            return Ok(populations
                .iter()
                .map(|&n| if n == 0 { Rat::zero() } else { nu.clone() })
                .collect());
        }
        let period = d as u64;
        let span = counts.ticks + counts.extent;
        if span > period || (counts.start + counts.ticks) % period != counts.end {
            return Err(HnnError::AliasedAges { ring, span, period });
        }
        let reference = counts.end + counts.extent;
        let ages: Vec<u64> = (0..period)
            .map(|c| (reference + period - c) % period)
            .collect();
        let mut powers = vec![Rat::one(); d];
        let mut mass = Rat::zero();
        for c in 0..d {
            if populations[c] == 0 {
                continue;
            }
            powers[c] = modulus_power(modulus, ages[c]);
            mass += &powers[c] * Rat::from_integer(BigInt::from(populations[c]));
        }
        Ok((0..d)
            .map(|c| {
                if populations[c] == 0 {
                    Rat::zero()
                } else {
                    chart.chart(&(&powers[c] / &mass))
                }
            })
            .collect())
    }

    /// **The weighted phase counts** `M_g[c] w(c)` of one phase: the counts at the passage's
    /// transported weight at the navigator's transport modulus ([`SourceMoment::phase_weights`];
    /// at `ρ = 1` ruling B's `M_g[c] ν̂(n_g)`), zero at an empty population.
    pub fn normalized_counts(
        &self,
        field: &Field,
        ring: usize,
        phase: usize,
        modulus: &Rat,
    ) -> Result<Vec<Rat>, HnnError> {
        let weight = self.phase_weights(field, ring, modulus)?[phase].clone();
        Ok(self
            .phase_counts(ring, phase)?
            .iter()
            .map(|&count| Rat::from_integer(BigInt::from(count)) * &weight)
            .collect())
    }

    /// **The whole normalized offset moment** at offset `δ` (module header; Lean
    /// `HNN/Encoding.whole_pair_read_counts`): the offset counts `C_g(δ)` with their pair
    /// population `n_(g,δ)` and its chart weight `ν̂(n_(g,δ))`; `None` at an empty population, which
    /// contributes nothing. No address is read.
    pub fn offset_table(
        &self,
        field: &Field,
        ring: usize,
        offset: usize,
    ) -> Result<Option<OffsetTable>, HnnError> {
        let index = self
            .offsets
            .iter()
            .position(|declared| *declared == offset)
            .ok_or(HnnError::Offset { offset })?;
        let counts = self.counts(ring)?.offset[index].clone();
        let population: u64 = counts.iter().sum();
        if population == 0 {
            return Ok(None);
        }
        Ok(Some(OffsetTable {
            counts,
            population,
            weight: PopulationChart::of(field).value(population),
        }))
    }

    /// **The source moment `m̃_g`** of one source ring at the constitution's ports, computed from
    /// the counts and never stored, on the normalized open that reads no window (module header):
    /// `Σ_c P_g^(−c)(E_g M_g[c] w(c) + Σ_δ Σ_(x,a) C_g(δ)[c, x, a] ν̂(n_(g,δ)) E_g^(δ)(e_x ⊗ e_a))`,
    /// `w(c)` the passage's transported weight ([`SourceMoment::phase_weights`]; `ν̂(n_g)` at a
    /// transport of modulus one).
    pub fn encode(
        &self,
        field: &Field,
        constitution: &impl ConstitutionRead,
        ring: usize,
    ) -> Result<Vec<Rat>, HnnError> {
        let weights = self.phase_weights(field, ring, &constitution.transport(ring))?;
        let (reads, pairs) = self.moment_parts(field, constitution, ring)?;
        let mut moment = pairs;
        for (phase, read) in reads {
            for (value, add) in moment.iter_mut().zip(read) {
                *value += add * &weights[phase];
            }
        }
        Ok(moment)
    }

    /// **The open's two ports on one source ring**, at the lift (`P_g^(τ_g)` applied): each
    /// occupied phase's marginal read of its raw counts, `P^τ P^(−c) E M[c]` (not yet weighted),
    /// and the pair ports' normalized read. The open is the phases' reads at their transported
    /// weights plus the pairs' ([`SourceMoment::encode`]); `hnn::prediction::BankPlacement` weighs
    /// them over the passage.
    #[allow(clippy::type_complexity)]
    pub fn open_parts(
        &self,
        field: &Field,
        constitution: &impl ConstitutionRead,
        current: &Current,
        ring: usize,
    ) -> Result<(Vec<(usize, Vec<Rat>)>, Vec<Rat>), HnnError> {
        let (reads, pairs) = self.moment_parts(field, constitution, ring)?;
        let geometry = field.ring(ring);
        let lift = &current.lift()[ring];
        Ok((
            reads
                .into_iter()
                .map(|(phase, read)| (phase, geometry.rotate(&read, lift)))
                .collect(),
            geometry.rotate(&pairs, lift),
        ))
    }

    /// The moment's two ports before the lift: each occupied phase's `P^(−c) E M[c]` on the raw
    /// counts, and `Σ_c P^(−c) Σ_δ Σ_(x,a) C(δ)[c, x, a] ν̂(n_δ) E^(δ)(e_x ⊗ e_a)` on the whole
    /// normalized offset moments.
    #[allow(clippy::type_complexity)]
    fn moment_parts(
        &self,
        field: &Field,
        constitution: &impl ConstitutionRead,
        ring: usize,
    ) -> Result<(Vec<(usize, Vec<Rat>)>, Vec<Rat>), HnnError> {
        let counts = self.counts(ring)?;
        let tables = self
            .offsets
            .iter()
            .map(|&offset| self.offset_table(field, ring, offset))
            .collect::<Result<Vec<_>, _>>()?;
        let geometry = field.ring(ring);
        let width = geometry.width();
        let port = constitution
            .source_port(ring)
            .ok_or(HnnError::MissingSourcePort { ring })?;
        if port.rows() != width || port.columns() != self.alphabet {
            return Err(HnnError::Shape {
                what: "source port E_g",
                expected: width * self.alphabet,
                found: port.rows() * port.columns(),
            });
        }
        let a = self.alphabet;
        let mut reads = Vec::new();
        let mut pairs = vec![Rat::zero(); width];
        for phase in 0..counts.period {
            let mut binned = vec![Rat::zero(); width];
            let mut occupied = false;
            for (code, &count) in counts.first[phase * a..(phase + 1) * a].iter().enumerate() {
                if count == 0 {
                    continue;
                }
                occupied = true;
                let count = Rat::from_integer(BigInt::from(count));
                for (row, value) in binned.iter_mut().enumerate() {
                    *value += &count * port.get(row, code)?;
                }
            }
            if occupied {
                reads.push((phase, geometry.rotate(&binned, &-BigInt::from(phase))));
            }
            let mut driven_sum: Option<Vec<Rat>> = None;
            for (&offset, table) in self.offsets.iter().zip(&tables) {
                let Some(table) = table else {
                    continue;
                };
                let pair = constitution
                    .pair_port(ring, offset)
                    .ok_or(HnnError::MissingSourcePort { ring })?;
                let driven = pair.apply_table(table, phase, a, width);
                driven_sum = Some(match driven_sum {
                    Some(sum) => sum.iter().zip(driven).map(|(s, d)| s + d).collect(),
                    None => driven,
                });
            }
            if let Some(driven) = driven_sum {
                let carried = geometry.rotate(&driven, &-BigInt::from(phase));
                for (value, add) in pairs.iter_mut().zip(carried) {
                    *value += add;
                }
            }
        }
        Ok((reads, pairs))
    }

    /// **The word's open on the source rings**: `s_g(0) = P_g^(τ_g) m̃_g` on `g ∈ 𝒮`, zero on every
    /// other ring.
    pub fn open_storage(
        &self,
        field: &Field,
        constitution: &impl ConstitutionRead,
        current: &Current,
    ) -> Result<Vec<Vec<Rat>>, HnnError> {
        let mut storage: Vec<Vec<Rat>> = field
            .rings()
            .iter()
            .map(|ring| vec![Rat::zero(); ring.width()])
            .collect();
        for counts in &self.rings {
            let moment = self.encode(field, constitution, counts.ring)?;
            storage[counts.ring] = field
                .ring(counts.ring)
                .rotate(&moment, &current.lift()[counts.ring]);
        }
        Ok(storage)
    }

    /// **The encoder covector, tape-free** (Lean `HNN/Moment.encoder_covector_tape_free`): for a
    /// covector `g` on the open storage `s_g(0)`, the derivative of `⟨g, s_g(0)⟩` in `E_g` is
    /// `Σ_c (P_g^(c−τ_g) g) ⊗ M_g[c] w(c)` (`2d_g × |A|`; `w(c)` the passage's transported weight,
    /// ruling B's `ν̂(n_g)` at a transport of modulus one), read from the counts, the weights on the
    /// population chart and `g` alone.
    ///
    /// [definition; agent-inferred] `g` is read once in the integral chart (integers over its least
    /// common denominator); each phase's `P_g^(c−τ_g)` permutes those integers, the counts multiply
    /// them as integers, and each entry is normalized once (the same values as the termwise sums).
    pub fn encoder_covector(
        &self,
        field: &Field,
        current: &Current,
        ring: usize,
        covector: &[Rat],
        modulus: &Rat,
    ) -> Result<ExactRatMatrix, HnnError> {
        let counts = self.counts(ring)?;
        let chart = PopulationChart::of(field);
        let scale = BigInt::one() << chart.exponent() as usize;
        let weights: Vec<BigInt> = self
            .phase_weights(field, ring, modulus)?
            .into_iter()
            .map(|w| (w * Rat::from_integer(scale.clone())).to_integer())
            .collect();
        let geometry = field.ring(ring);
        let width = geometry.width();
        if covector.len() != width {
            return Err(HnnError::Shape {
                what: "open storage covector",
                expected: width,
                found: covector.len(),
            });
        }
        let a = self.alphabet;
        let (values, denominator) = integral(covector);
        // The rotation's permutation of the realified coordinates, read on their indices.
        let indices: Vec<Rat> = (0..width)
            .map(|index| Rat::from_integer(BigInt::from(index)))
            .collect();
        let mut sums = vec![vec![BigInt::zero(); a]; width];
        for phase in 0..counts.period {
            let binned = &counts.first[phase * a..(phase + 1) * a];
            if binned.iter().all(|count| *count == 0) {
                continue;
            }
            let order = geometry.rotate(&indices, &(BigInt::from(phase) - &current.lift()[ring]));
            for (row, source) in order.iter().enumerate() {
                let value = &values[source
                    .to_integer()
                    .to_usize()
                    .expect("a rotation permutes the coordinates")];
                if value.is_zero() {
                    continue;
                }
                for (sum, &count) in sums[row].iter_mut().zip(binned) {
                    if count != 0 {
                        *sum += value * count * &weights[phase];
                    }
                }
            }
        }
        let rows = sums
            .into_iter()
            .map(|row| {
                row.into_iter()
                    .map(|sum| Rat::new(sum, &denominator * &scale))
                    .collect()
            })
            .collect();
        Ok(ExactRatMatrix::shaped(width, a, rows)?)
    }

    /// **The moment's dense code bits**, a reading (design R2 H1): each slot self-delimited,
    /// `max(1, bits) + 1`, plus the window's raw cells at `⌈log₂|A|⌉ + 1` bits each.
    pub fn dense_bits(&self) -> u64 {
        let slot = |count: &u64| u64::from((u64::BITS - count.leading_zeros()).max(1)) + 1;
        let counts: u64 = self
            .rings
            .iter()
            .map(|ring| {
                ring.first.iter().map(slot).sum::<u64>()
                    + ring.offset.iter().flatten().map(slot).sum::<u64>()
            })
            .sum();
        let cell = crate::compression::cost::ceil_log2(&BigUint::from(self.alphabet)) + 1;
        counts + cell * self.window.len() as u64
    }
}

/// `ρ^a`, exactly.
pub(crate) fn modulus_power(modulus: &Rat, age: u64) -> Rat {
    let mut power = Rat::one();
    for _ in 0..age {
        power *= modulus;
    }
    power
}

fn bump(count: &mut u64) -> Result<(), HnnError> {
    *count = count.checked_add(1).ok_or(HnnError::CountOverflow)?;
    Ok(())
}

/// The window's cell `offset` cells before the next write.
fn earlier(window: &[Option<usize>], cursor: usize, offset: usize) -> Option<usize> {
    if offset == 0 || offset > window.len() {
        return None;
    }
    window[(cursor + window.len() - offset) % window.len()]
}
