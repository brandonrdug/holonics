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
//! [definition; agent-inferred, U6] **The open is normalized and reads no held cell** (the
//! [encoding pin](../../../../research/records/2026-09-29_HOLONIC_ENCODING_FOR_THE_FIELD_PINNED_BEFORE_ITS_RUN.md)
//! §1.4; Lean `HNN/IndexedOpen.{pairPopulation, pairNormalized}`, `HNN/Encoding.whole_pair_read_*`):
//! the marginal reads the phase counts over their population, and the pair port reads the whole
//! oriented offset moment over its pair population, so the open's amplitude does not grow with the
//! ingested cells (`normalized_open_population_invariant`) and depends on no raw cell. The read at
//! the address the buffer supplied (the primary's ruling B, the first repair's open) conditioned the
//! open on the last `max Δ` raw cells, a context cut off at depth `max Δ` on the source; it is
//! retired.
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
//! modulus one unless the moment carries the leaky count (below). The retired reading, the section
//! over its own population `v`, weighed a section datum `n/v` times a request cell.
//!
//! [definition; agent-inferred, September 30; the
//! [modulus's record](../../../../research/records/2026-09-30_THE_MODULUS_FOUNDED_OFF_ONE_PINNED_BEFORE_ITS_RUNS.md)]
//! **The founding off the lossless boundary** (`Constitution::founding_transport`; Lean
//! `HNN/IndexedOpen`, "The founding off the lossless boundary"). The modulus one is the passive
//! set's boundary and the law's degenerate point: no recency is marked (`lossless_term_modulus`),
//! and a datum a whole turn older weighs what the newer one does (`founded_modulus_alias` at
//! `ρ = 1`), so the phase record, which carries a datum's age only within one turn, reads the
//! transport only by not reading it. Founded there, the executed comparison's certified move stays
//! there: at the opening its slope in `ρ` points outward (every term threshold-led, the target's
//! growth rising toward the lossless mixture) and, on three of four development batches, turns
//! inward by `63/64`: a boundary local minimum (the modulus's record, §1). The transport is
//! founded instead at the
//! largest modulus `ρ₀` on the source port's lattice whose one-turn transport carries a datum to
//! one unit of the weights' chart, `ρ₀^d ≤ 2^(−L_ν)`: the least dissipative transport whose
//! one-turn alias is at most one chart unit, the phase record sufficient at the chart's grain. It
//! reads the ring's period and the chart's grain, nothing of a terrain; the order-2 declaration
//! (`d = 60`, `L_ν = 21`) founds at `102837/131072`. The consumers that do not yet read a modulus
//! below one (the card; a passage over one turn on a moment without the leaky count) keep the lossless founding and refuse it, typed;
//! the bank's face path and the readout's one anchor refused it too until their retirement
//! (September 30, batch H).
//!
//! [definition; agent-inferred, October 2; the
//! [contact loop record](../../../../research/records/2026-10-02_THE_CONTACT_LOOP_THE_RETURN_REACHES_EVERY_CONTACT_AND_ITS_CHANGE_IS_RELEASED_BEFORE_THE_LATER_CUT.md)
//! §24] **The leaky count** (#62's owed item: "per-phase counts decayed at the founding modulus
//! read a passage of any length within one chart unit of its transported weights"). A moment
//! opened at a source ring whose transport has modulus `ρ < 1` ([`SourceMoment::open_with`])
//! carries, beside the raw counts, its counts decayed by the transport: at each of the ring's ticks
//! every decayed count is multiplied by `ρ`, and the cell then enters at its phase with weight one,
//!
//! ```text
//! L_g[c] ← ρ^t L_g[c]  (t the ring's ticks at the step),   L_g[τ_g mod d_g] += x_k,
//! L_g(δ)[c] likewise for the offset counts,                  w = L / Σ L   (the transported mass)
//! ```
//!
//! so a datum `a` ticks old weighs `ρ^a / Σ_k ρ^(a_k)`, the transported weight, whatever the span:
//! the age is carried by the decay, not read from the phase, and nothing aliases past one turn.
//! The counts are carried on the lattice `2^(−L_ν−m)`, `m = ⌈log₂(1/(1 − ρ))⌉`, each product read at
//! the nearest point (ties up; Lean `HNN/IndexedOpen.leaky_tick_eq_nearest`). A count the ingest
//! carries (ticks and exact units) then stays within `2^(−L_ν−m−1)/(1 − ρ) ≤ 2^(−L_ν−1)` of the
//! exact decayed count over a passage of any length, half a population-chart unit
//! (`leaky_count_ingest`, `leaky_lattice_le_half_chart`). A section's datum enters
//! ([`SourceMoment::continued`]) at the nearest point to `ρ^a`, one rounding more, so each such
//! entry adds up to `2^(−L_ν−m−1)` to its count's bound (`leaky_count_error_le`). The read
//! `L[slot]/Σ L` carries every slot's error in its mass: with each count within `δ` over `N` slots
//! it is within `(δ + w N δ)/Σ L` of the transported weight `w` before the chart rounds it
//! (`leaky_read_error`), and not within one chart unit in general: at campaign 1's founding, 205
//! data entering one phase of ring 0 (a code its lock selects, then the 204 it does not), followed
//! by two of its ticks, put the newest datum's read more than eight chart units below its weight
//! (`leaky_read_exceeds_chart_unit`, read on this ingest by the test
//! `the_leaky_read_is_not_within_one_chart_unit_in_general`); one chart unit is an instance's
//! reading (the many-turn test's passage), not the law's. On campaign 1's own cut at the founding,
//! with up to 22 cells between ring 0's ticks and up to 40 counts held, the read stays within `3/2`
//! chart units of the transported weights, read at every seventh cell (the contact loop record §24).
//! A count that decays below half a lattice unit leaves the
//! record, so the record holds only what the transport still carries. It is a quotient of the
//! passage sufficient for the transported open, never a list of cells. The modulus is the one the
//! moment was opened at; a moment read at another modulus is refused ([`HnnError::Transport`]).
//!
//! [definition; agent-inferred, September 30] **Read from a station** (`hnn::prediction`, "A
//! candidate reads the span from its own station"; Lean `HNN/IndexedOpen.framedWeight`): a
//! candidate at station `j` weighs each datum by its two-sided transport distance,
//! `ρ^|τ_j − τ_k| / Σ_l ρ^|τ_j − τ_l|`, because the section is a joint field. [`SourceMoment::phase_weights`]
//! reads the span from its last datum, which is station `j`'s framed law exactly when no datum lies
//! after `j` (`framed_weight_one_sided`), and in every frame at modulus one; the bank reads each
//! candidate from its own station (`BankPlacement`).
//!
//! [definition; agent-inferred, U6] **The pair buffer is the offset moment's one-step state**
//! (Lean `Transport/SourceMoment.streamStep`'s previous value, `HNN/Moment.SourceDecl.StreamState`'s
//! held cells): the offset-`δ` pair of cell `k` needs cell `k − δ`, so a cell stays in the buffer
//! for `max Δ` ingests until every pair it joins is counted, and then leaves. No receiver reads the
//! buffer, and nothing of the source is discarded by length: every cell is counted once in every
//! source ring's phase counts, and every pair at every declared offset in its offset counts, over the
//! moment's whole passage (the tests in `hnn::tests::moment` that nothing is discarded by length).
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
//! | `HNN/IndexedOpen.{normalized_phase_counts_mass, normalized_open_population_invariant, normalized_zero_population}`; `HNN/Encoding.{whole_pair_read_counts, whole_pair_read_population_invariant, whole_pair_read_tape_free}` (the open reads no held cell) | [`PopulationChart`], [`SourceMoment::normalized_counts`], [`SourceMoment::offset_table`], [`SourceMoment::encode`] |
//! | `moment_capacity` | [`capacity`], [`Capacity`] |
//! | `HNN/Prediction.{placed_at_station, joint_residue_determines_position}` (a locked datum at its station's residue; a ring of period `∏ dᵢ`, pairwise coprime, places each datum at its joint residue class); `HNN/IndexedOpen.{passage_population, passage_read, passage_weight_one_population, separate_populations_ratio, transportedWeight, transported_weight_mass, transported_weight_frame_invariant, transported_weight_unitary, passage_weight_split_invariant, decayed_weight_antitone, decayed_weight_frame_free, decayed_weight_lossless, lossless_term_modulus, dissipative_term_modulus}` (the section continues the passage; each datum at its transported weight) | [`SourceMoment::continued`], [`SourceMoment::phase_weights`], [`SourceMoment::open_parts`] |
//! | `HNN/IndexedOpen.{framedWeight, framed_weight_mass, framed_weight_pos, framed_weight_one_sided, framed_weight_ratio, framed_weight_le_pow, oneway_later_weight_ratio, framed_weight_symmetric, framed_weight_translation, framed_weight_lossless}` (a candidate reads the span from its own station, each datum at its two-sided transport distance; the one-way law on data no later than the station) | `hnn::prediction::BankPlacement::{weights, storage, modulus_derivative}`; [`SourceMoment::phase_weights`] is the law read from the span's last datum |
//! | `HNN/IndexedOpen.{nearest_sub_le, leaky_tick_eq_nearest, leaky_count_error_le, leaky_count_ingest, leaky_lattice_le_half_chart, leaky_read_error, campaign_one_founding, leaky_read_exceeds_chart_unit}` (the leaky count: the ingest's counts within half a chart unit over any length, a section's rounded entry adding half a lattice unit, the read's error carried by the mass) | `Leaky::{decay, enter, normalized}`, [`SourceMoment::open_with`], [`SourceMoment::normalized_counts`] |

use std::collections::BTreeMap;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Signed, ToPrimitive, Zero};

use crate::hnn::HnnError;
use crate::hnn::field::{ConstitutionRead, Current, Field, FieldMaterial};
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
    #[cfg(test)]
    pub(crate) fn lossy_at(&self, n: u64) -> bool {
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
        for (slot, count) in table.normalized(phase, alphabet) {
            let (x, a) = (slot / alphabet, slot % alphabet);
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
    /// Below modulus one, the leaky count's normalized entries by slot (module header, "The leaky
    /// count"), which replace `counts · weight`.
    pub transported: Option<BTreeMap<usize, Rat>>,
}

impl OffsetTable {
    /// The phase's counts `C_g(δ)[c, ·, ·]`, row the current cell.
    pub fn phase(&self, phase: usize, alphabet: usize) -> &[u64] {
        let block = alphabet * alphabet;
        &self.counts[phase * block..(phase + 1) * block]
    }

    /// **The phase's normalized entries** `(slot, value)` within the phase (`slot = x|A| + a`),
    /// nonzero only: `C[c, x, a] ν̂` at modulus one, the leaky count's `L[c, x, a]/Σ L` below it.
    pub fn normalized(&self, phase: usize, alphabet: usize) -> Vec<(usize, Rat)> {
        let block = alphabet * alphabet;
        match &self.transported {
            Some(entries) => entries
                .range(phase * block..(phase + 1) * block)
                .map(|(&slot, value)| (slot - phase * block, value.clone()))
                .collect(),
            None => self
                .phase(phase, alphabet)
                .iter()
                .enumerate()
                .filter(|(_, count)| **count != 0)
                .map(|(slot, &count)| (slot, Rat::from_integer(BigInt::from(count)) * &self.weight))
                .collect(),
        }
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
    /// The counts decayed by the ring's transport (module header, "The leaky count"), when it was
    /// opened below modulus one.
    leaky: Option<Leaky>,
}

/// [definition; agent-inferred, October 2] **One ring's leaky count** (module header): the decayed
/// phase and offset counts as integer coordinates on `2^(−unit)`, nonzero entries only, at the
/// modulus `ρ = numerator · 2^(−shift)` they were opened at.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Leaky {
    modulus: Rat,
    numerator: BigInt,
    shift: u32,
    unit: u32,
    first: BTreeMap<usize, BigInt>,
    offset: Vec<BTreeMap<usize, BigInt>>,
}

impl Leaky {
    /// The leaky count of a ring whose transport has modulus `ρ < 1`, on `2^(−L_ν−m)`,
    /// `m = ⌈log₂(1/(1 − ρ))⌉`. Refused unless `0 < ρ < 1` is dyadic.
    fn open(ring: usize, modulus: &Rat, chart: u32, offsets: usize) -> Result<Self, HnnError> {
        let refused = || HnnError::Transport {
            ring,
            modulus: modulus.clone(),
        };
        if !modulus.is_positive() || *modulus >= Rat::one() {
            return Err(refused());
        }
        let denominator = modulus.denom();
        if denominator.magnitude().count_ones() != 1 {
            return Err(refused());
        }
        let shift = u32::try_from(denominator.trailing_zeros().ok_or_else(refused)?)
            .map_err(|_| refused())?;
        // m = ⌈log₂(1/(1 − ρ))⌉: the least m with 2^m (1 − ρ) ≥ 1.
        let gap = Rat::one() - modulus;
        let mut m = 0u32;
        while Rat::from_integer(BigInt::one() << m as usize) * &gap < Rat::one() {
            m += 1;
        }
        Ok(Self {
            modulus: modulus.clone(),
            numerator: modulus.numer().clone(),
            shift,
            unit: chart + m,
            first: BTreeMap::new(),
            offset: vec![BTreeMap::new(); offsets],
        })
    }

    /// One tick of the transport: every coordinate `v ← ⌊(2vk + 2^s)/2^(s+1)⌋` (`ρ = k 2^(−s)`, the
    /// nearest lattice point, ties up); a coordinate at zero leaves the record.
    fn decay(&mut self, ticks: u64) {
        let half = BigInt::one() << self.shift as usize;
        let twice = BigInt::one() << (self.shift as usize + 1);
        let numerator = &self.numerator;
        let tick = |map: &mut BTreeMap<usize, BigInt>| {
            map.retain(|_, v| {
                let product: BigInt = BigInt::from(2) * &*v * numerator + &half;
                // Counts are nonnegative, so truncation is the floor.
                *v = &product / &twice;
                !v.is_zero()
            });
        };
        for _ in 0..ticks {
            if self.first.is_empty() && self.offset.iter().all(BTreeMap::is_empty) {
                return;
            }
            tick(&mut self.first);
            for map in &mut self.offset {
                tick(map);
            }
        }
    }

    /// One datum entering at `slot` with weight `ρ^age`, read at the nearest lattice point.
    fn enter(map: &mut BTreeMap<usize, BigInt>, slot: usize, unit: u32, modulus: &Rat, age: u64) {
        let scale = Rat::from_integer(BigInt::one() << unit as usize);
        let half = Rat::new(BigInt::one(), BigInt::from(2));
        let value = (modulus_power(modulus, age) * scale + half).floor().to_integer();
        if value.is_zero() {
            return;
        }
        let entry = map.entry(slot).or_insert_with(BigInt::zero);
        *entry += value;
    }

    /// The normalized entries `L[slot]/Σ L` of one map, read on the population chart; empty at a
    /// zero mass.
    fn normalized(map: &BTreeMap<usize, BigInt>, chart: &PopulationChart) -> BTreeMap<usize, Rat> {
        let mass: BigInt = map.values().sum();
        if mass.is_zero() {
            return BTreeMap::new();
        }
        map.iter()
            .filter_map(|(&slot, v)| {
                let w = chart.chart(&Rat::new(v.clone(), mass.clone()));
                (!w.is_zero()).then_some((slot, w))
            })
            .collect()
    }
}

/// What one ingest did: the cells consumed, and whether it stopped at the joint clock's carry-out.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Ingested {
    pub cells: usize,
    pub carry_out: bool,
}

/// [definition] **The source moment on the closing source rings.** Sized once from the [`Field`]
/// (guard 1): every slot exists from the open, and ingest only adds to counts and overwrites the
/// held cells. It holds no cell list and no per-occurrence record.
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
    /// **Open a moment** at the current lift point: every count zero, no cell held.
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
                    leaky: None,
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

    /// [definition; agent-inferred, October 2] **Open a moment at the constitution's transports**:
    /// [`SourceMoment::open`], with a leaky count on every source ring whose transport has modulus
    /// below one (module header, "The leaky count").
    pub fn open_with(
        field: &Field,
        current: &Current,
        constitution: &impl ConstitutionRead,
    ) -> Result<Self, HnnError> {
        let mut moment = Self::open(field, current);
        let chart = PopulationChart::of(field).exponent();
        let offsets = moment.offsets.len();
        for counts in &mut moment.rings {
            let modulus = constitution.transport(counts.ring);
            if !modulus.is_one() {
                counts.leaky = Some(Leaky::open(counts.ring, &modulus, chart, offsets)?);
            }
        }
        Ok(moment)
    }

    /// **Ingest cells in order**: the lift point's selective step, then the phase-binned and offset
    /// counts on every source ring, then the held cells. Stops after the cell whose step carries
    /// the joint clock out, and reports it.
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
                if let Some(leaky) = &mut counts.leaky {
                    leaky.decay(u64::from(step.ticks[counts.ring]));
                    let one = BigInt::one() << leaky.unit as usize;
                    *leaky.first.entry(phase * a + code).or_insert_with(BigInt::zero) += &one;
                }
                for (index, &offset) in self.offsets.iter().enumerate() {
                    if let Some(earlier) = earlier(&self.window, self.cursor, offset) {
                        let slot = phase * a * a + code * a + earlier;
                        bump(&mut counts.offset[index][slot])?;
                        if let Some(leaky) = &mut counts.leaky {
                            let one = BigInt::one() << leaky.unit as usize;
                            *leaky.offset[index].entry(slot).or_insert_with(BigInt::zero) += one;
                        }
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
        let before = counts.extent;
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
        // The leaky count reads the span at its end: the request's counts decay over the section's
        // new extent, and station `j`'s datum enters `extent − 1 − j` ticks old.
        if let Some(leaky) = &mut counts.leaky {
            leaky.decay(counts.extent - before);
            let (unit, modulus) = (leaky.unit, leaky.modulus.clone());
            for (station, cell) in cells.iter().enumerate() {
                if let Some(code) = *cell {
                    let slot = ((phase + 1 + station) % period) * a + code;
                    Leaky::enter(&mut leaky.first, slot, unit, &modulus, counts.extent - 1 - station as u64);
                }
            }
        }
        passage.cells += placed;
        Ok(passage)
    }

    /// [definition; agent-inferred, October 4; the reception carry §10] **The moment's text**, a
    /// part of a continuing state: `moment n cursor rings` (the cells ingested, the held cells'
    /// cursor, the source rings counted), `window` (each held cell's code or `-`), `opening` (the
    /// lift point at the open), then per source ring `counts g d start end ticks extent leaky`, its
    /// phase counts `first`, one `offset` line per declared offset, and, where it counts leakily,
    /// `leaky ρ k s unit` with its maps (`map` lines of `slot value` pairs, the phase map first).
    /// The alphabet and offsets are the field's and are not written.
    pub fn write(&self, s: &mut String) {
        use crate::hnn::state_text::line;
        *s += &format!("moment {} {} {}\n", self.cells, self.cursor, self.rings.len());
        line(
            s,
            "window",
            self.window
                .iter()
                .map(|code| code.map_or("-".to_string(), |code| code.to_string())),
        );
        line(s, "opening", &self.opening);
        let map = |s: &mut String, map: &BTreeMap<usize, BigInt>| {
            line(
                s,
                "map",
                map.iter().flat_map(|(slot, value)| [slot.to_string(), value.to_string()]),
            );
        };
        for counts in &self.rings {
            *s += &format!(
                "counts {} {} {} {} {} {} {}\n",
                counts.ring,
                counts.period,
                counts.start,
                counts.end,
                counts.ticks,
                counts.extent,
                u8::from(counts.leaky.is_some())
            );
            line(s, "first", &counts.first);
            for offset in &counts.offset {
                line(s, "offset", offset);
            }
            if let Some(leaky) = &counts.leaky {
                *s += &format!(
                    "leaky {} {} {} {}\n",
                    leaky.modulus, leaky.numerator, leaky.shift, leaky.unit
                );
                map(s, &leaky.first);
                for offset in &leaky.offset {
                    map(s, offset);
                }
            }
        }
    }

    /// **The moment read back from its text** ([`SourceMoment::write`]) on a field: refused, typed,
    /// where a line is out of its form or a count has another shape than the field declares (its
    /// source rings, their periods, the alphabet and the offsets).
    pub fn read<'a>(
        field: &Field,
        head: &str,
        next: crate::hnn::state_text::Next<'_, 'a>,
    ) -> Result<Self, HnnError> {
        use crate::hnn::state_text::{counted, keyed, refused, value, values};
        let what = "the moment";
        let words = keyed(head, "moment", what)?;
        let [cells, cursor, count] = words[..] else {
            return refused(what);
        };
        let (cells, cursor, count): (u64, usize, usize) = (
            value(Some(&cells), what)?,
            value(Some(&cursor), what)?,
            value(Some(&count), what)?,
        );
        let alphabet = field.alphabet();
        let offsets = field.offsets().to_vec();
        let reach = offsets.iter().copied().max().unwrap_or(0);
        let window = keyed(next("the moment's window")?, "window", "the moment's window")?
            .into_iter()
            .map(|word| match word {
                "-" => Ok(None),
                code => value::<usize>(Some(&code), "the moment's window")
                    .and_then(|code| if code < alphabet { Ok(Some(code)) } else { refused("the moment's window") }),
            })
            .collect::<Result<Vec<_>, _>>()?;
        let opening: Vec<BigInt> = values(
            &keyed(next("the moment's opening")?, "opening", "the moment's opening")?,
            "the moment's opening",
        )?;
        // Ingest writes at the cursor before advancing it modulo a nonempty window.
        // Such a cursor is always strictly inside it. With no offsets, the window is empty
        // and ingest skips the write/modulo; its sole valid cursor is the founding zero.
        if window.len() != reach
            || (reach == 0 && cursor != 0)
            || (reach != 0 && cursor >= reach)
            || opening.len() != field.rings().len()
            || count != field.sources().len()
        {
            return refused("the moment against the field's declaration");
        }
        let read_map = |next: &mut dyn FnMut(&'static str) -> Result<&'a str, HnnError>| -> Result<BTreeMap<usize, BigInt>, HnnError> {
            let words = keyed(next("a leaky map")?, "map", "a leaky map")?;
            if words.len() % 2 != 0 {
                return refused("a leaky map");
            }
            words
                .chunks(2)
                .map(|pair| Ok((value(pair.first(), "a leaky map")?, value(pair.get(1), "a leaky map")?)))
                .collect()
        };
        let mut rings = Vec::with_capacity(count);
        for &ring in field.sources() {
            let head: Vec<u64> = counted(next("a ring's counts")?, "counts", 7, "a ring's counts")?;
            let period = field.ring(ring).placements().len();
            if head[0] != ring as u64 || head[1] != period as u64 || head[6] > 1 {
                return refused("a ring's counts against its declared ring and period");
            }
            let first: Vec<u64> =
                counted(next("a ring's phase counts")?, "first", period * alphabet, "a ring's phase counts")?;
            let offset = (0..offsets.len())
                .map(|_| {
                    counted(
                        next("a ring's offset counts")?,
                        "offset",
                        period * alphabet * alphabet,
                        "a ring's offset counts",
                    )
                })
                .collect::<Result<Vec<Vec<u64>>, _>>()?;
            let leaky = if head[6] == 1 {
                let words = keyed(next("a leaky count")?, "leaky", "a leaky count")?;
                let [modulus, numerator, shift, unit] = words[..] else {
                    return refused("a leaky count");
                };
                let mut leaky = Leaky {
                    modulus: value(Some(&modulus), "a leaky count")?,
                    numerator: value(Some(&numerator), "a leaky count")?,
                    shift: value(Some(&shift), "a leaky count")?,
                    unit: value(Some(&unit), "a leaky count")?,
                    first: read_map(next)?,
                    offset: Vec::with_capacity(offsets.len()),
                };
                for _ in 0..offsets.len() {
                    leaky.offset.push(read_map(next)?);
                }
                Some(leaky)
            } else {
                None
            };
            rings.push(RingCounts {
                ring,
                period,
                first,
                offset,
                start: head[2],
                end: head[3],
                ticks: head[4],
                extent: head[5],
                leaky,
            });
        }
        Ok(Self {
            alphabet,
            offsets,
            rings,
            window,
            cursor,
            cells,
            opening,
        })
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
        if let Some(leaky) = &counts.leaky {
            // The leaky count: the open reads `L[c]/Σ L`, so the weight of a decayed count is the
            // one inverse mass, at every phase the record still holds.
            if leaky.modulus != *modulus {
                return Err(HnnError::Transport {
                    ring,
                    modulus: modulus.clone(),
                });
            }
            let mass: BigInt = leaky.first.values().sum();
            let mut held = vec![false; d];
            for slot in leaky.first.keys() {
                held[slot / a] = true;
            }
            return Ok(held
                .into_iter()
                .map(|h| {
                    if h && !mass.is_zero() {
                        chart.chart(&Rat::new(BigInt::one() << leaky.unit as usize, mass.clone()))
                    } else {
                        Rat::zero()
                    }
                })
                .collect());
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
        let counts = self.counts(ring)?;
        if let Some(leaky) = &counts.leaky {
            if leaky.modulus != *modulus {
                return Err(HnnError::Transport {
                    ring,
                    modulus: modulus.clone(),
                });
            }
            let a = self.alphabet;
            let entries = Leaky::normalized(&leaky.first, &PopulationChart::of(field));
            let mut row = vec![Rat::zero(); a];
            for (slot, value) in entries.range(phase * a..(phase + 1) * a) {
                row[slot - phase * a] = value.clone();
            }
            return Ok(row);
        }
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
        let ring_counts = self.counts(ring)?;
        let counts = ring_counts.offset[index].clone();
        let population: u64 = counts.iter().sum();
        if population == 0 {
            return Ok(None);
        }
        let chart = PopulationChart::of(field);
        let transported = ring_counts
            .leaky
            .as_ref()
            .map(|leaky| Leaky::normalized(&leaky.offset[index], &chart));
        Ok(Some(OffsetTable {
            counts,
            population,
            weight: chart.value(population),
            transported,
        }))
    }

    /// **The source moment `m̃_g`** of one source ring at the constitution's ports, computed from
    /// the counts and never stored, on the normalized open that reads no held cell (module header):
    /// `Σ_c P_g^(−c)(E_g M_g[c] w(c) + Σ_δ Σ_(x,a) C_g(δ)[c, x, a] ν̂(n_(g,δ)) E_g^(δ)(e_x ⊗ e_a))`,
    /// `w(c)` the passage's transported weight ([`SourceMoment::phase_weights`]; `ν̂(n_g)` at a
    /// transport of modulus one).
    pub fn encode(
        &self,
        field: &Field,
        constitution: &dyn FieldMaterial,
        ring: usize,
    ) -> Result<Vec<Rat>, HnnError> {
        let modulus = constitution.transport(ring);
        if let Some(features) = self.transported_features(field, ring, &modulus)? {
            // The leaky count: each phase's normalized decayed counts through `E_g`, carried back
            // by `P_g^(−c)`, plus the pairs' (their tables read the leaky entries).
            let (_, mut moment) = self.moment_parts(field, constitution, ring)?;
            let geometry = field.ring(ring);
            let port = constitution
                .source_port(ring)
                .ok_or(HnnError::MissingSourcePort { ring })?;
            for (phase, feature) in features {
                let mut binned = vec![Rat::zero(); geometry.width()];
                for (code, value) in feature.iter().enumerate() {
                    if value.is_zero() {
                        continue;
                    }
                    for (row, entry) in binned.iter_mut().enumerate() {
                        *entry += value * port.get(row, code)?;
                    }
                }
                let carried = geometry.rotate(&binned, &-BigInt::from(phase));
                for (entry, add) in moment.iter_mut().zip(carried) {
                    *entry += add;
                }
            }
            return Ok(moment);
        }
        let weights = self.phase_weights(field, ring, &modulus)?;
        let (reads, pairs) = self.moment_parts(field, constitution, ring)?;
        let mut moment = pairs;
        for (phase, read) in reads {
            for (value, add) in moment.iter_mut().zip(read) {
                *value += add * &weights[phase];
            }
        }
        Ok(moment)
    }

    /// The leaky count's normalized phase rows `(c, L[c]/Σ L)`, occupied phases only; `None` on a
    /// ring opened at modulus one. Refused at a modulus other than the one it was opened at.
    #[allow(clippy::type_complexity)]
    fn transported_features(
        &self,
        field: &Field,
        ring: usize,
        modulus: &Rat,
    ) -> Result<Option<Vec<(usize, Vec<Rat>)>>, HnnError> {
        let counts = self.counts(ring)?;
        let Some(leaky) = &counts.leaky else {
            return Ok(None);
        };
        if leaky.modulus != *modulus {
            return Err(HnnError::Transport {
                ring,
                modulus: modulus.clone(),
            });
        }
        let a = self.alphabet;
        let mut rows: BTreeMap<usize, Vec<Rat>> = BTreeMap::new();
        for (slot, value) in Leaky::normalized(&leaky.first, &PopulationChart::of(field)) {
            rows.entry(slot / a).or_insert_with(|| vec![Rat::zero(); a])[slot % a] = value;
        }
        Ok(Some(rows.into_iter().collect()))
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
        constitution: &dyn FieldMaterial,
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
        constitution: &dyn FieldMaterial,
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
        constitution: &dyn FieldMaterial,
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
        if let Some(features) = self.transported_features(field, ring, modulus)? {
            // The leaky count: `Σ_c (P_g^(c−τ_g) g) ⊗ L[c]/Σ L`.
            let geometry = field.ring(ring);
            let width = geometry.width();
            if covector.len() != width {
                return Err(HnnError::Shape {
                    what: "open storage covector",
                    expected: width,
                    found: covector.len(),
                });
            }
            let mut rows = vec![vec![Rat::zero(); self.alphabet]; width];
            for (phase, feature) in features {
                let turned =
                    geometry.rotate(covector, &(BigInt::from(phase) - &current.lift()[ring]));
                for (row, value) in rows.iter_mut().zip(&turned) {
                    if value.is_zero() {
                        continue;
                    }
                    for (entry, f) in row.iter_mut().zip(&feature) {
                        if !f.is_zero() {
                            *entry += value * f;
                        }
                    }
                }
            }
            return Ok(ExactRatMatrix::shaped(width, self.alphabet, rows)?);
        }
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
    /// `max(1, bits) + 1`, plus the held raw cells at `⌈log₂|A|⌉ + 1` bits each.
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

/// The held cell `offset` cells before the next write.
fn earlier(window: &[Option<usize>], cursor: usize, offset: usize) -> Option<usize> {
    if offset == 0 || offset > window.len() {
        return None;
    }
    window[(cursor + window.len() - offset) % window.len()]
}
