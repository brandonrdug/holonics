//! **The source moment: phase-binned counts on closing source rings, and its capacity.**
//!
//! [definition] The source enters as phase-carried moments, never as a tape (design (a), "The law
//! of one passage", `ingest`). For each cell `x_k` (the exterior chart's one-hot vector `e_code`)
//! the lift point takes its selective step ([`crate::hnn::Field::selective_step`]), and on every
//! source ring `g ∈ 𝒮`, at its phase `c = τ_g mod d_g` after the step:
//!
//! ```text
//! M_g[c] += x_k                                      phase-binned counts           (d_g × |A|)
//! C_g(δ)[c] += x_k ⊗ win[δ],  δ ∈ Δ                    offset counts on the exterior (d_g × |A|²)
//! win ← shift(win, x_k)                               the window: the last max Δ cells, overwritten
//! m̃_g = Σ_c P_g^(−c) (E_g M_g[c] + Σ_δ E_g^(δ) C_g(δ)[c])       the source moment, never stored
//! s_g(0) = P_g^(τ_g) m̃_g                                          the word's open on g ∈ 𝒮
//! ```
//!
//! Every slot is sized once from the field; nothing grows with the cells but the counts'
//! `O(log n)` bits. The window is a shift register of raw cells, whose overwrite law is distinct
//! from the counts' accumulate law, and it enters the open only through `C_g(δ)`. Ingest stops at a
//! carry-out of the joint clock: the aeon boundary belongs to the winding, not to a caller counter.
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
//! | `exteriorOffset_independent_of_E` | [`SourceMoment::offset_counts`], [`PairPort::apply`] |
//! | `moment_capacity` | [`capacity`], [`Capacity`] |

use num_bigint::{BigInt, BigUint};
use num_traits::{One, ToPrimitive, Zero};

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

    /// **`E^(δ)` on one phase's offset counts** (`|A| × |A|`, row the current cell, column the
    /// earlier): `Σ_ρ e_ρ (a_ρᵀ C b_ρ)`, over the nonzero counts only.
    pub fn apply(&self, counts: &[u64], alphabet: usize, width: usize) -> Vec<Rat> {
        let mut weights = vec![Rat::zero(); self.rank()];
        for (slot, &count) in counts.iter().enumerate() {
            if count == 0 {
                continue;
            }
            let (x, y) = (slot / alphabet, slot % alphabet);
            let count = Rat::from_integer(BigInt::from(count));
            for (rho, weight) in weights.iter_mut().enumerate() {
                *weight += &count * &self.current[rho][x] * &self.earlier[rho][y];
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
                RingCounts {
                    ring,
                    period,
                    first: vec![0; period * alphabet],
                    offset: offsets
                        .iter()
                        .map(|_| vec![0; period * alphabet * alphabet])
                        .collect(),
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

    /// The window's cells, most recent first (`win[1], win[2], …`), `None` before enough cells.
    pub fn window(&self) -> Vec<Option<usize>> {
        (1..=self.window.len())
            .map(|offset| earlier(&self.window, self.cursor, offset))
            .collect()
    }

    /// **The source moment `m̃_g`** of one source ring at the constitution's ports, computed from
    /// the counts and never stored: `Σ_c P_g^(−c)(E_g M_g[c] + Σ_δ E_g^(δ) C_g(δ)[c])`.
    pub fn encode(
        &self,
        field: &Field,
        constitution: &impl ConstitutionRead,
        ring: usize,
    ) -> Result<Vec<Rat>, HnnError> {
        let counts = self.counts(ring)?;
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
        let mut moment = vec![Rat::zero(); width];
        for phase in 0..counts.period {
            let mut binned = vec![Rat::zero(); width];
            for (code, &count) in counts.first[phase * a..(phase + 1) * a].iter().enumerate() {
                if count == 0 {
                    continue;
                }
                let count = Rat::from_integer(BigInt::from(count));
                for (row, value) in binned.iter_mut().enumerate() {
                    *value += &count * port.get(row, code)?;
                }
            }
            for (index, &offset) in self.offsets.iter().enumerate() {
                let pair = constitution
                    .pair_port(ring, offset)
                    .ok_or(HnnError::MissingSourcePort { ring })?;
                let block = a * a;
                let driven = pair.apply(
                    &counts.offset[index][phase * block..(phase + 1) * block],
                    a,
                    width,
                );
                for (value, add) in binned.iter_mut().zip(driven) {
                    *value += add;
                }
            }
            let carried = geometry.rotate(&binned, &-BigInt::from(phase));
            for (value, add) in moment.iter_mut().zip(carried) {
                *value += add;
            }
        }
        Ok(moment)
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
    /// `Σ_c (P_g^(c−τ_g) g) ⊗ M_g[c]` (`2d_g × |A|`), read from the counts and `g` alone.
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
    ) -> Result<ExactRatMatrix, HnnError> {
        let counts = self.counts(ring)?;
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
                        *sum += value * count;
                    }
                }
            }
        }
        let rows = sums
            .into_iter()
            .map(|row| {
                row.into_iter()
                    .map(|sum| Rat::new(sum, denominator.clone()))
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
