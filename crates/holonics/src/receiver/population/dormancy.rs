//! **Dormancy: a key held through the aeon its layer is silent in** (campaign 3 at the population,
//! #73; Lean `Compression/Landmark/Context/Dormancy`).
//!
//! [definition; agent-inferred] **A layered key space.** A key family's emitters read through
//! declared layers (a moiré's rings): key `k` sounds a bit per layer at each tick (a ring's
//! half-turn sheet), and the emitted class is read from the sounding layers alone ([`Layered`]). A
//! layer is **active** or **dormant**: a dormant layer is silent (its sheet reads `0`, the terrain's
//! `Moire::emit_active`) while its ring's clock keeps winding, so when it returns it returns at its
//! continued phase. The emitters' clocks advance at every cell whatever the activity: the key is
//! retained, never restarted.
//!
//! [proved-derived; formal-checked] **The dormancy-aware survivor filter** ([`Dormancy`]; Lean
//! `Dormancy.dormant_survivor_code`). The hidden state is the key and the activity `a ∈ {0,1}^L`
//! (bit `ℓ` set: layer `ℓ` active). The prior is uniform over the keys and, per layer, the fixed
//! share at the declared rate `α = 2^(−j)`: the passage opens as a step from active
//! (`1 − α` active, `α` dormant), and each layer stays with `1 − α` and switches with `α` between
//! cells, independently (Lean `LocalWeighing.shareKernel`, the product kernel `Dormancy.productKernel`).
//! A state's face of a cell is `1` where its active layers emit the cell and `0` elsewhere. The
//! forward mixture over these states is exact Bayes, so:
//!
//! ```text
//! S_σ(n) = {k : e_k(t, σ_t) = x_t for every t < n}          keys filtered only where σ's layers sound
//! −log₂ ∏_(t<n) q_t ≤ log₂ |K| − log₂ #S_σ(n) + Σ_ℓ c_α(σ^ℓ)   every activity path σ with S_σ(n) ≠ ∅
//! c_α(σ^ℓ) = −log₂ π(σ^ℓ_0) + k_ℓ (−log₂ α) + (n − 1 − k_ℓ)(−log₂(1 − α))     k_ℓ the switches of layer ℓ
//! α = 2^(−j):  −log₂(1 − α) < 3·2^(−j),  so c_α(σ^ℓ) < (k_ℓ + [σ^ℓ_0 dormant]) j + 3 when n ≤ 2^j
//! ```
//!
//! Over `n` cells the path pays `n − 1` transitions: the step after the last cell sums out (Lean
//! states `dormant_survivor_code` over `n + 1` cells and `n` transitions).
//!
//! A key dies only when every activity contradicts the cell: a cell that a dormant layer's silence
//! cannot explain and the key's active layers do not emit. Death is reserved for keys contradicted
//! while active; a dormant key's weight only moves by the switch it pays.
//!
//! [definition; agent-inferred] **The declared rate: a switch pays for its position.** A receiver
//! that expects at most a few switches in its passage of `n` cells declares `j = ⌈log₂ n⌉`: each
//! switch then costs `j` bits, the `log₂` of the positions it could take, and the stays cost less
//! than `3` bits a layer over the whole passage. The rate is declared from the passage the receiver
//! admits, never tuned on its cells.
//!
//! [definition; agent-inferred] **The executed chart.** The ideal forward weights are dyadic with
//! denominators `2^(jLt)`, so an exact carrier grows by `jL` bits a cell. The filter carries each
//! state's weight as a 64-bit mantissa and a binary exponent ([`Weight`]), rounded **down** after
//! every kernel step and every accumulation: a positive weight stays positive and a zero weight
//! stays zero, so the survivors (the zero pattern, and so death) are exactly the ideal's. The
//! executed face `q̂(c) = S̃_c/Σ_c′ S̃_c′`, `S̃_c` the rounded sum of the weights emitting `c`, is exact
//! and normalized, and it is what the family is scored by (its likelihood is the product of its
//! executed faces, enclosed by `PassageCode`). [proved-derived; formal-checked] Each rounding
//! multiplies a weight or a sum by a factor in `(1 − 2^(−62), 1]`. A rounding after the kernel lowers
//! the next weights by at most its factor, and a rounded sum lowers the scored face by at most its
//! factor, so the executed code exceeds the ideal bound above by at most the certified drift
//! `3 · r · 2^(−62)` bits, `r` the roundings counted ([`Dormancy::drift`]; Lean
//! `Dormancy.{forward_executed_nonneg, dormant_survivor_executed, dormant_executed_code}`, the
//! nonnegative-face form of `LocalWeighing.forward_executed` with the rounding on the weight after
//! the kernel). [established-bounded; source-inspected, computational-witness] That `r` bounds
//! every factor the Lean takes is read from this code (the counter adds every share, opening,
//! accumulation and join rounding, more than any one chain needs) and checked on the chart by the
//! test `the_roundings_counted_cover_every_factor_the_lean_takes`: against the exact step from the
//! executed weights, the opening is within `1 − L·2^(−62)` of its prior, each weight after the
//! kernel within `1 − L·2^(−62)` of the exact kernel and never above it, the scored class sum
//! within `1 − m·2^(−62)` of its exact sum, `m` the weights and chunk pieces it adds, and each cell
//! counts at least `m + L`. The test `the_dormant_filter_executes_the_exact_forward_mixture` checks
//! the executed faces against the exact mixture stepped in ℚ.
//!
//! [definition] Of the winding guide's six objects this owner touches the **helix** (a ring's clock
//! keeps winding while its layer is silent, and its key is read at its continued phase), the
//! **tube** (the aeon's span, a run of cells at one activity) and **faces and placement** (the
//! executed face on the cell alphabet); the pair, cell holonomy and tower thread stay attached.

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use rayon::prelude::*;

use super::{
    Act, Declaration, Emitters, Family, KeyReadout, Likelihood, PopulationError, Readout, Work,
    mixed_radix, refuse,
};
use crate::compression::landmark::context::PassageCode;
use crate::ratio::Rat;

/// [definition] **A layered key space** (module header): each key sounds one bit a layer at the
/// current tick, and its class is read from the sounding bits of its active layers.
pub trait Layered: Emitters + Sync {
    /// The layers `L` a key reads through.
    fn layers(&self) -> usize;
    /// **Key `k`'s sounding bits** at the current tick, bit `ℓ` its layer `ℓ`'s.
    fn sounding(&self, key: u64) -> usize;
    /// **The class emitted** by the sounding bits `sounding` with the layers in `active` sounding
    /// and the rest silent.
    fn class(&self, sounding: usize, active: usize) -> usize;
    /// **Wind every key's clock** `ticks` ticks without a reading: a ring's clock keeps winding.
    fn wind(&mut self, ticks: u64);
}

// -------------------------------------------------------------------------------------------
// the executed chart

/// **The executed weight** `m · 2^e` (module header, "The executed chart"): a 64-bit mantissa whose
/// top bit is set, or zero.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Weight {
    pub(crate) mantissa: u64,
    pub(crate) exponent: i64,
}

impl Weight {
    /// Zero.
    pub const ZERO: Self = Self {
        mantissa: 0,
        exponent: 0,
    };

    /// `m · 2^e` from a wide mantissa, rounded down to 64 bits.
    fn of(mantissa: u128, exponent: i64) -> Self {
        if mantissa == 0 {
            return Self::ZERO;
        }
        let bits = 128 - mantissa.leading_zeros() as i64;
        let shift = bits - 64;
        if shift >= 0 {
            Self {
                mantissa: (mantissa >> shift) as u64,
                exponent: exponent + shift,
            }
        } else {
            Self {
                mantissa: (mantissa << -shift) as u64,
                exponent: exponent + shift,
            }
        }
    }

    /// Whether the weight is zero.
    pub fn is_zero(&self) -> bool {
        self.mantissa == 0
    }

    /// `a · 2^e` normalized so its top bit lies at bit 125.
    fn wide(mantissa: u128, exponent: i64) -> (u128, i64) {
        let bits = 128 - mantissa.leading_zeros() as i64;
        let shift = 126 - bits;
        (mantissa << shift, exponent - shift)
    }

    /// **`x + y`, rounded down**: each term normalized to 126 bits, the smaller aligned down to the
    /// larger's exponent, the sum rounded down to 64 bits (a factor in `(1 − 2^(−62), 1]`).
    fn sum(x: (u128, i64), y: (u128, i64)) -> Self {
        match (x.0 == 0, y.0 == 0) {
            (true, true) => return Self::ZERO,
            (true, false) => return Self::of(y.0, y.1),
            (false, true) => return Self::of(x.0, x.1),
            _ => {}
        }
        let (mut a, mut b) = (Self::wide(x.0, x.1), Self::wide(y.0, y.1));
        if a.1 < b.1 {
            std::mem::swap(&mut a, &mut b);
        }
        let gap = a.1 - b.1;
        let aligned = if gap >= 128 { 0 } else { b.0 >> gap };
        Self::of(a.0 + aligned, a.1)
    }

    /// `self + other`, rounded down.
    pub fn plus(self, other: Weight) -> Self {
        Self::sum(
            (u128::from(self.mantissa), self.exponent),
            (u128::from(other.mantissa), other.exponent),
        )
    }

    /// **One layer's share** `((2^j − 1) keep + other)/2^j`, rounded down.
    fn share(keep: Weight, other: Weight, rung: u32) -> Self {
        let stay = (1u128 << rung) - 1;
        let mut shared = Self::sum(
            (u128::from(keep.mantissa) * stay, keep.exponent),
            (u128::from(other.mantissa), other.exponent),
        );
        if !shared.is_zero() {
            shared.exponent -= i64::from(rung);
        }
        shared
    }

    /// The exact value `m · 2^e`, in lowest terms (its twos cancelled by hand: no gcd).
    pub fn value(&self) -> Rat {
        if self.is_zero() {
            return Rat::zero();
        }
        let mantissa = BigInt::from(self.mantissa);
        if self.exponent >= 0 {
            return Rat::from_integer(mantissa << self.exponent as usize);
        }
        let twos = u64::from(self.mantissa.trailing_zeros()).min(self.exponent.unsigned_abs());
        Rat::new_raw(
            mantissa >> twos as usize,
            BigInt::one() << (self.exponent.unsigned_abs() - twos) as usize,
        )
    }
}

/// `x/y` of two weights (`y > 0`), exact: each mantissa is 64 bits, so the reduction's gcd reads
/// odd parts of at most 64 bits once the twos are stripped.
fn weight_ratio(numerator: Weight, denominator: Weight) -> Rat {
    if numerator.is_zero() || denominator.is_zero() {
        return Rat::zero();
    }
    let gap = numerator.exponent - denominator.exponent;
    let (n, d) = (
        BigInt::from(numerator.mantissa),
        BigInt::from(denominator.mantissa),
    );
    if gap >= 0 {
        Rat::new(n << gap as usize, d)
    } else {
        Rat::new(n, d << gap.unsigned_abs() as usize)
    }
}

/// `n/Σ d` of weights on one scale (`Σ d > 0`), exact: the classes' sums of a face, whose
/// normalization `Σ_c n_c/Σ d = 1` holds exactly.
fn ratio_of(numerator: Weight, denominator: &[Weight]) -> Rat {
    let live = denominator.iter().filter(|w| !w.is_zero());
    let Some(least) = live.map(|w| w.exponent).min() else {
        return Rat::zero();
    };
    if numerator.is_zero() {
        return Rat::zero();
    }
    let on_scale = |w: &Weight| -> BigUint {
        if w.is_zero() {
            BigUint::zero()
        } else {
            BigUint::from(w.mantissa) << (w.exponent - least) as usize
        }
    };
    let whole: BigUint = denominator.iter().map(on_scale).sum();
    Rat::new(BigInt::from(on_scale(&numerator)), BigInt::from(whole))
}

// -------------------------------------------------------------------------------------------
// the filter

/// The live keys a core reads at once.
const CHUNK: usize = 1 << 12;

/// A reading of one cell by one factor, before it commits: its classes' rounded sums, and, when the
/// cell is emitted, the survivors and their weights after the kernel.
struct Pending {
    sums: Vec<Weight>,
    kept: Vec<u64>,
    weights: Vec<Weight>,
    roundings: u128,
}

/// [definition; agent-inferred] **The dormancy-aware survivor filter** (module header): a layered
/// key space under the uniform key prior and the per-layer fixed share at `α = 2^(−j)`, each live
/// key carrying its weight per activity `a ∈ {0,1}^L` on the executed chart.
pub struct Dormancy {
    emitters: Box<dyn Layered>,
    rung: u32,
    masks: usize,
    held: Option<Vec<u64>>,
    weights: Vec<Weight>,
    opening: Vec<Weight>,
    roundings: u128,
    /// The states (a key and one activity) read against received cells.
    states: u64,
    /// The kernel's shares executed: a layer's stay or switch on one key's activity.
    shares: u64,
}

impl Dormancy {
    /// **Declare the filter** over the layered emitters at rung `j` (`α = 2^(−j)`, `1 ≤ j ≤ 32`);
    /// refused at an empty key space or past the declared enumeration of `|K| · 2^L` key states,
    /// naming the Bombe that owns the larger space.
    pub fn new(
        emitters: Box<dyn Layered>,
        rung: u32,
        admitted: u64,
        bombe: &'static str,
    ) -> Result<Self, PopulationError> {
        let (keys, layers) = (emitters.keys(), emitters.layers());
        if keys == 0 || emitters.alphabet() == 0 || layers == 0 || layers > 8 {
            return Err(refuse(
                "a dormancy filter",
                "its key space and alphabet hold a member, and it reads one to eight layers",
            ));
        }
        if rung == 0 || rung > 32 {
            return Err(refuse(
                "a dormancy filter",
                "its switch rate 2^(−j) has 1 ≤ j ≤ 32",
            ));
        }
        let masks = 1usize << layers;
        let states = BigUint::from(keys) * BigUint::from(masks);
        if states > BigUint::from(admitted) {
            return Err(PopulationError::Bombe {
                key_space: states,
                admitted: BigUint::from(admitted),
                bombe,
            });
        }
        // The opening: a step from every layer active, (1 − α) stays and α switches, on the chart
        // (each factor `2^j − 1` rounded down, counted).
        let stay = u128::from((1u64 << rung) - 1);
        let mut roundings = 0u128;
        let opening = (0..masks)
            .map(|mask| {
                let mut weight = Weight::of(1, -(i64::from(rung) * layers as i64));
                for _ in 0..mask.count_ones() {
                    weight = Weight::of(u128::from(weight.mantissa) * stay, weight.exponent);
                    roundings += 1;
                }
                weight
            })
            .collect();
        Ok(Self {
            emitters,
            rung,
            masks,
            held: None,
            weights: Vec::new(),
            opening,
            roundings,
            states: 0,
            shares: 0,
        })
    }

    /// The live keys' count `#S`.
    pub fn count(&self) -> u64 {
        match &self.held {
            Some(held) => held.len() as u64,
            None => self.emitters.keys(),
        }
    }

    /// `|K|`.
    pub fn keys(&self) -> u64 {
        self.emitters.keys()
    }

    /// The layers `L`.
    pub fn layers(&self) -> usize {
        self.emitters.layers()
    }

    /// The emitters.
    pub fn emitters(&self) -> &dyn Layered {
        self.emitters.as_ref()
    }

    /// The live keys, ascending.
    pub fn survivors(&self) -> Vec<u64> {
        match &self.held {
            Some(held) => held.clone(),
            None => (0..self.emitters.keys()).collect(),
        }
    }

    /// Live key `index`'s weights over the activities.
    fn row(&self, index: usize) -> &[Weight] {
        match &self.held {
            Some(_) => &self.weights[index * self.masks..(index + 1) * self.masks],
            None => &self.opening,
        }
    }

    /// Every live key with its weights over the activities.
    fn rows(&self) -> impl Iterator<Item = (u64, &[Weight])> {
        (0..self.count() as usize).map(move |index| (self.key(index), self.row(index)))
    }

    /// **The certified drift** in bits between the executed code and the ideal bound (module
    /// header): `3 · r · 2^(−62)`.
    pub fn drift(&self) -> Rat {
        Rat::new(
            BigInt::from(3u32) * BigInt::from(self.roundings),
            BigInt::one() << 62usize,
        )
    }

    /// Live key `index`'s key.
    fn key(&self, index: usize) -> u64 {
        match &self.held {
            Some(held) => held[index],
            None => index as u64,
        }
    }

    /// The live keys' index ranges the host's cores read, in order: each chunk's rounded partial
    /// sums are joined in chunk order, so the executed faces do not depend on the cores.
    fn chunks(&self) -> Vec<std::ops::Range<usize>> {
        let count = self.count() as usize;
        (0..count.div_ceil(CHUNK))
            .map(|chunk| chunk * CHUNK..((chunk + 1) * CHUNK).min(count))
            .collect()
    }

    /// Each class's rounded sum `S̃_c` of the live weights emitting it, and the roundings: each
    /// chunk's partial sums in key and activity order, joined in chunk order.
    fn sums(&self) -> (Vec<Weight>, u128) {
        let alphabet = self.emitters.alphabet();
        let partial: Vec<(Vec<Weight>, u128)> = self
            .chunks()
            .into_par_iter()
            .map(|range| {
                let mut sums = vec![Weight::ZERO; alphabet];
                let mut roundings = 0u128;
                for index in range {
                    self.accumulate(index, &mut sums, &mut roundings);
                }
                (sums, roundings)
            })
            .collect();
        Self::join(alphabet, partial.into_iter())
    }

    /// Live key `index`'s weights added to their classes' sums.
    fn accumulate(&self, index: usize, sums: &mut [Weight], roundings: &mut u128) {
        let sounding = self.emitters.sounding(self.key(index));
        for (mask, weight) in self.row(index).iter().enumerate() {
            if weight.is_zero() {
                continue;
            }
            let class = self.emitters.class(sounding, mask);
            sums[class] = sums[class].plus(*weight);
            *roundings += 1;
        }
    }

    /// The chunks' partial sums joined in chunk order.
    fn join(
        alphabet: usize,
        parts: impl Iterator<Item = (Vec<Weight>, u128)>,
    ) -> (Vec<Weight>, u128) {
        parts.fold(
            (vec![Weight::ZERO; alphabet], 0u128),
            |(mut sums, roundings), (part, counted)| {
                let mut joined = 0u128;
                for (sum, piece) in sums.iter_mut().zip(part) {
                    if !piece.is_zero() {
                        *sum = sum.plus(piece);
                        joined += 1;
                    }
                }
                (sums, roundings + counted + joined)
            },
        )
    }

    /// **The executed face** `q̂(c) = S̃_c/Σ S̃` (module header), exact.
    pub fn face(&self) -> Vec<Rat> {
        let (sums, _) = self.sums();
        sums.iter().map(|&sum| ratio_of(sum, &sums)).collect()
    }

    /// **The executed posterior of each layer's dormancy** `Σ_(k, a: ℓ ∉ a) w/Σ w`, each sum rounded
    /// down on the chart, their ratio exact.
    pub fn dormant(&self) -> Vec<Rat> {
        (0..self.layers())
            .map(|layer| {
                let (mut dormant, mut whole) = (Weight::ZERO, Weight::ZERO);
                for (_, row) in self.rows() {
                    for (mask, weight) in row.iter().enumerate() {
                        whole = whole.plus(*weight);
                        if mask & (1 << layer) == 0 {
                            dormant = dormant.plus(*weight);
                        }
                    }
                }
                weight_ratio(dormant, whole)
            })
            .collect()
    }

    /// **Each live key's executed posterior** `Σ_a w(k, a)/Σ w`, in the survivors' order: each key's
    /// total and the whole rounded down on the chart, their ratio exact.
    pub fn masses(&self) -> Vec<Rat> {
        let totals: Vec<Weight> = self
            .rows()
            .map(|(_, row)| row.iter().fold(Weight::ZERO, |sum, &w| sum.plus(w)))
            .collect();
        let whole = totals.iter().fold(Weight::ZERO, |sum, &w| sum.plus(w));
        totals
            .into_iter()
            .map(|total| weight_ratio(total, whole))
            .collect()
    }

    /// **Read one cell** without moving anything, in one pass over the live keys: the classes'
    /// sums (as [`Dormancy::sums`] reads them), and, when some live state emits the cell, the
    /// survivors and their weights after the kernel.
    fn read(&self, cell: usize) -> Pending {
        let (alphabet, layers, masks) = (self.emitters.alphabet(), self.layers(), self.masks);
        let parts: Vec<(Vec<Weight>, u128, Vec<u64>, Vec<Weight>, u128)> = self
            .chunks()
            .into_par_iter()
            .map(|range| {
                let mut sums = vec![Weight::ZERO; alphabet];
                let (mut summed, mut moved_roundings) = (0u128, 0u128);
                let (mut kept, mut weights) = (Vec::new(), Vec::new());
                let mut moved = [Weight::ZERO; 1 << 8];
                for index in range {
                    self.accumulate(index, &mut sums, &mut summed);
                    let key = self.key(index);
                    let sounding = self.emitters.sounding(key);
                    let mut any = false;
                    for (mask, &weight) in self.row(index).iter().enumerate() {
                        moved[mask] = if self.emitters.class(sounding, mask) == cell {
                            any |= !weight.is_zero();
                            weight
                        } else {
                            Weight::ZERO
                        };
                    }
                    if !any {
                        continue;
                    }
                    // The kernel, one layer at a time: stay (1 − α), switch α.
                    for layer in 0..layers {
                        let bit = 1 << layer;
                        for mask in 0..masks {
                            if mask & bit == 0 {
                                let (dormant, active) = (moved[mask], moved[mask | bit]);
                                moved[mask] = Weight::share(dormant, active, self.rung);
                                moved[mask | bit] = Weight::share(active, dormant, self.rung);
                                moved_roundings += 2;
                            }
                        }
                    }
                    kept.push(key);
                    weights.extend_from_slice(&moved[..masks]);
                }
                (sums, summed, kept, weights, moved_roundings)
            })
            .collect();
        let (mut kept, mut weights, mut moved) = (Vec::new(), Vec::new(), 0u128);
        let mut partial = Vec::with_capacity(parts.len());
        for (sums, summed, keys, rows, counted) in parts {
            partial.push((sums, summed));
            kept.extend(keys);
            weights.extend(rows);
            moved += counted;
        }
        let (sums, summed) = Self::join(alphabet, partial.into_iter());
        if sums[cell].is_zero() {
            return Pending {
                sums,
                kept: Vec::new(),
                weights: Vec::new(),
                roundings: summed,
            };
        }
        Pending {
            sums,
            kept,
            weights,
            roundings: summed + moved,
        }
    }

    /// Commit a read of `cell`: the survivors and weights move, and every clock winds one tick.
    fn commit(&mut self, pending: Pending, cell: usize) -> Result<(), PopulationError> {
        self.shares += pending.kept.len() as u64 * (self.layers() * self.masks) as u64;
        self.held = Some(pending.kept);
        self.weights = pending.weights;
        self.roundings += pending.roundings;
        self.emitters.advance(cell)
    }

    /// **Wind every clock** `ticks` ticks before the first cell (a newborn founded at a later cell).
    pub fn wind(&mut self, ticks: u64) {
        self.emitters.wind(ticks);
    }
}

/// [definition; agent-inferred] **A dormant key family** (module header): dormancy-aware survivor
/// filters over one factor or over a factorized key space whose cell is the mixed-radix tuple of
/// its factors' classes (the first least significant). The factors' hidden states are independent
/// a priori and each reads its own digit, so the family's face is the product of theirs.
pub struct DormantFamily {
    label: String,
    description: u64,
    factors: Vec<Dormancy>,
    passage: PassageCode,
    exhausted: Option<usize>,
}

impl DormantFamily {
    /// The family of the declared factors; refused without a factor.
    pub fn new(
        label: String,
        description: u64,
        factors: Vec<Dormancy>,
    ) -> Result<Self, PopulationError> {
        if factors.is_empty() {
            return Err(refuse(
                "a dormant key family",
                "it holds at least one factor",
            ));
        }
        Ok(Self {
            label,
            description,
            factors,
            passage: PassageCode::new(),
            exhausted: None,
        })
    }

    /// The factors.
    pub fn factors(&self) -> &[Dormancy] {
        &self.factors
    }

    /// **The certified drift** of the family's executed code, the factors' summed.
    pub fn drift(&self) -> Rat {
        self.factors.iter().map(Dormancy::drift).sum()
    }

    /// **Wind every factor's clocks** `ticks` ticks (a newborn founded at a later cell).
    pub fn wind(mut self, ticks: u64) -> Self {
        for factor in &mut self.factors {
            factor.wind(ticks);
        }
        self
    }

    fn digits(&self, cell: usize) -> Vec<usize> {
        mixed_radix(
            self.factors.iter().map(|factor| factor.emitters.alphabet()),
            cell,
        )
    }
}

impl Family for DormantFamily {
    fn label(&self) -> String {
        self.label.clone()
    }

    fn alphabet(&self) -> usize {
        self.factors
            .iter()
            .map(|factor| factor.emitters.alphabet())
            .product()
    }

    fn description(&self) -> u64 {
        self.description
    }

    fn face(&self) -> Result<Vec<Rat>, PopulationError> {
        let faces: Vec<Vec<Rat>> = self.factors.iter().map(Dormancy::face).collect();
        Ok((0..self.alphabet())
            .map(|cell| {
                self.digits(cell)
                    .iter()
                    .zip(&faces)
                    .map(|(&digit, face)| face[digit].clone())
                    .product()
            })
            .collect())
    }

    fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError> {
        let alphabet = self.alphabet();
        if cell >= alphabet {
            return Err(PopulationError::CellOutside { cell, alphabet });
        }
        // Every factor reads before any commits: a death moves no factor, though its reads were
        // spent.
        let digits = self.digits(cell);
        for factor in &mut self.factors {
            factor.states += factor.count() * factor.masks as u64;
        }
        let pending: Vec<Pending> = self
            .factors
            .iter()
            .zip(&digits)
            .map(|(factor, &digit)| factor.read(digit))
            .collect();
        if let Some(factor) = pending.iter().position(|read| read.kept.is_empty()) {
            self.exhausted = Some(factor);
            return Ok(Rat::zero());
        }
        let mut face = Rat::one();
        for ((factor, read), digit) in self.factors.iter_mut().zip(pending).zip(digits) {
            face *= ratio_of(read.sums[digit], &read.sums);
            factor.commit(read, digit)?;
        }
        self.passage.face(&face)?;
        Ok(face)
    }

    fn likelihood(&self) -> Likelihood {
        Likelihood::Enclosed(self.passage)
    }

    fn readout(&self) -> Readout {
        Readout::Keys(KeyReadout {
            spaces: self.factors.iter().map(Dormancy::keys).collect(),
            survivors: self
                .factors
                .iter()
                .map(|factor| {
                    factor
                        .survivors()
                        .into_iter()
                        .map(|key| factor.emitters.coordinates(key))
                        .collect()
                })
                .collect(),
            masses: self.factors.iter().map(Dormancy::masses).collect(),
            dormant: self.factors.iter().map(Dormancy::dormant).collect(),
        })
    }

    fn exhausted(&self) -> Option<usize> {
        self.exhausted
    }

    fn drift(&self) -> Rat {
        DormantFamily::drift(self)
    }

    fn declaration(&self) -> Declaration {
        Declaration::new(
            "dormant key family",
            self.factors
                .iter()
                .map(|factor| u64::from(factor.rung))
                .collect(),
        )
        .with(
            self.factors
                .iter()
                .map(|factor| factor.emitters.declaration())
                .collect(),
        )
    }

    /// The states read and the kernel's shares executed: the work of holding every key through
    /// its layers' silence.
    fn work(&self) -> Work {
        let mut work = Work::default();
        for factor in &self.factors {
            work.add(Act::State, factor.states);
            work.add(Act::Share, factor.shares);
        }
        work
    }
}

#[cfg(test)]
#[path = "dormancy_tests.rs"]
mod tests;
