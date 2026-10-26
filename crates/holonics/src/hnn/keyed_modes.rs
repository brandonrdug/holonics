//! **Keyed modes: parametron modes whose move the arriving class selects, located from the
//! comparison's covector through their forward jets** (#405, #73).
//!
//! [definition; agent-inferred, October 23] Why the class must select the move: a field whose moves
//! share one linear part is a function of its (class, lag mod period) counts
//! (`HolonicsResearch/Geometry/ScrewTorsion.lean`, `laggedRun_lag_residue` and
//! `laggedRun_eq_of_counts`; record `2026-10-22_ORDER_IS_TORSION_AND_SUBGRAIN_INFORMATION_DISSOLVES_INTO_THE_CARRIED_RESIDUE`).
//! Measured on GSM8K the same day, the native route's linear field and its pumped receiving ring
//! both coded within a thousandth of a bit of the receiving tree's counts alone. Order enters as
//! the torsion of non-commuting moves, so each class (the key) selects its own move of every mode,
//! and the moves are located from the comparison, not drawn: unlearned keyed moves add nothing.
//!
//! A bank of `K` complex parametron modes. Each arriving class `s` is a key: it selects every
//! mode's swing (a turn and a boost, `λ`) and its push (`β`).
//!
//! ```text
//! move        z_k' = λ_(k,s) z_k + β_(k,s)                 |λ_(k,s)| ≤ 1 − 2^(−m)
//! exponent    w_c = Σ_k Re(conj(R_(c,k)) z_k) + zᴴ H_c z   in bits, at the receiver's face
//!             H_c Hermitian (the square law)
//! joined      p̂(c) = q(c) 2^(w_c) / Σ_d q(d) 2^(w_d)        q the receiving tree's face
//! covector    δ_c = p̂(c) − [c = t],   g_k = Σ_c δ_c (R_(c,k) + 2 (H_c z)_k)   (−log₂ p̂(t) descends along −δ)
//! jets        J'_(k,a) = λ_(k,s) J_(k,a) + [s = a] z_k       J = ∂z_k/∂λ_(k,a)
//!             H'_(k,a) = λ_(k,s) H_(k,a) + [s = a]           H = ∂z_k/∂β_(k,a)
//! section     G_λ = Σ_t conj(J) g,  G_β = Σ_t conj(H) g,  G_R = Σ_t δ_c z_k,  G_H = Σ_t δ_c z zᴴ
//! deposit     θ ← θ − 2^(−e) G_θ / ‖G_θ‖_∞ for each family θ ∈ {λ, β, R, H}, then λ projected into its disk
//! certificate the section reread from its opening state under the deposit codes strictly fewer
//!             bits than it did (an exact comparison of the products of its faces); else e + 1
//! ```
//!
//! The jets are the adjoint carried forward: a mode's move is diagonal, so the derivative of its
//! state by each of its own keyed moves is one complex number that moves with it. No passage is
//! kept for a backward sweep. What a section holds is its opening state and its own cells' faces,
//! for the reread that certifies its deposit, and it is released when the section closes.
//!
//! **Exact integers; widths declared.** Every quantity is a Gaussian-integer numerator on a
//! declared dyadic grain ([`Grains`]). A mode's state is carried on `2^(−(L+P))`: its face on
//! `2^(−L)` and its carried residue below it, which the next move transports with the face
//! (`e' = λ e + Δ − q`); each product's second-order remainder is released at `2^(−(L+P))`. The
//! exponential `2^(w)` is the dyadic square-root navigator's face: the product of the factors
//! `2^(2^(−i))` its exponent's binary digits select, each the exact integer square root at
//! `2^(−62)` ([`Exponential`]).
//!
//! **Modality.** The bank reads classes of a declared alphabet and nothing else; a text, image,
//! acoustic or motor boundary chart supplies the classes and the tree's address.
use num_bigint::BigUint;

/// A Gaussian-integer numerator on a declared grain.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Gaussian {
    pub re: i128,
    pub im: i128,
}

impl Gaussian {
    pub const ZERO: Self = Self { re: 0, im: 0 };
    pub fn new(re: i128, im: i128) -> Self {
        Self { re, im }
    }
    fn add(self, o: Self) -> Self {
        Self::new(self.re + o.re, self.im + o.im)
    }
    fn sub(self, o: Self) -> Self {
        Self::new(self.re - o.re, self.im - o.im)
    }
    /// The product, on the sum of the two grains.
    fn mul(self, o: Self) -> Self {
        Self::new(
            self.re * o.re - self.im * o.im,
            self.re * o.im + self.im * o.re,
        )
    }
    /// `conj(self) · o`, on the sum of the two grains.
    fn conj_mul(self, o: Self) -> Self {
        Self::new(
            self.re * o.re + self.im * o.im,
            self.re * o.im - self.im * o.re,
        )
    }
    /// `Re(conj(self) · o)`, on the sum of the two grains.
    fn re_conj_mul(self, o: Self) -> i128 {
        self.re * o.re + self.im * o.im
    }
    fn scale(self, k: i128) -> Self {
        Self::new(self.re * k, self.im * k)
    }
    /// Released `bits` coarser, to the nearest numerator (half away from zero).
    fn release(self, bits: u32) -> Self {
        Self::new(release(self.re, bits), release(self.im, bits))
    }
    fn norm_sq(self) -> i128 {
        self.re * self.re + self.im * self.im
    }
    fn max_abs(self) -> i128 {
        self.re.abs().max(self.im.abs())
    }
}

/// `x` released `bits` coarser, to the nearest numerator, half away from zero.
pub(crate) fn release(x: i128, bits: u32) -> i128 {
    if bits == 0 {
        return x;
    }
    let half = 1i128 << (bits - 1);
    if x >= 0 { (x + half) >> bits } else { -((-x + half) >> bits) }
}

/// [definition; agent-inferred] **The declared grains.** `P`: moves, pushes and the readout on
/// `2^(−P)`; `L`: a state's face on `2^(−L)` (its residue below it, to `2^(−(L+P))`); `S`: the
/// covector on `2^(−S)`; `X`: the readout exponent released to `2^(−X)` before the navigator reads
/// it; `m`: the moves' margin inside the unit disk, `|λ| ≤ 1 − 2^(−m)`. Chosen so every product
/// stays inside `i128` for `|z| ≤ 2^(m+2)`, the bound a margin-`m` mode keeps under pushes of
/// modulus at most `2^2` (checked in [`KeyedModes::new`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Grains {
    pub moves: u32,
    pub face: u32,
    pub covector: u32,
    pub exponent: u32,
    pub margin: u32,
    /// `Q`: a mode's face as the square law reads it, on `2^(−Q)`.
    pub square: u32,
}

impl Grains {
    /// The prototype's grains (agent-inferred): `P = 30`, `L = 32`, `S = 30`, `X = 24`, `m = 8`,
    /// `Q = 16` (so a pair's product `conj(z_j) z_k` lands on `2^(−2Q) = 2^(−L)`, the linear
    /// read's grain).
    pub const DECLARED: Self = Self { moves: 30, face: 32, covector: 30, exponent: 24, margin: 8, square: 16 };
}

/// [definition; agent-inferred] **The exponential's navigator face at `2^(−62)`**: `2^(2^(−i))`
/// for `i = 1..=X`, each the floor of the exact integer square root of its predecessor's square
/// re-based, from `2^1`. A value `2^(n + f)` with `f` on `2^(−X)` is `2^n` times the product of the
/// factors the binary digits of `f` select, each product released at `2^(−62)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Exponential {
    roots: Vec<u128>,
    digits: u32,
}

const UNIT_BITS: u32 = 62;
/// The pushes' declared reach, `|β| ≤ 2^2` (the carrier's headroom, [`Grains`]).
const PUSH_BITS: u32 = 2;
/// The square law's declared reach, `|h| ≤ 2^8` for every entry of a class's form (the carrier's
/// headroom, checked in [`KeyedModes::new`]).
const SQUARE_BITS: u32 = 8;
/// The grain of `ln 2`'s face, `2^(−30)`.
const LN2_BITS: u32 = 30;

/// [definition; agent-inferred] **`ln 2` as its navigator's face** on `2^(−30)`: the series
/// `Σ_(k≥1) 1/(k 2^k)`, its terms to `k = 60` read at `2^(−60)` and the sum released to `2^(−30)`
/// (the tail past `k = 60` and the terms' floors stay below `2^(−50)`).
pub(crate) fn ln2_face() -> i128 {
    let sum: i128 = (1..=60).map(|k: i128| (1i128 << (60 - k)) / k).sum();
    release(sum, 60 - LN2_BITS)
}

/// [definition; agent-inferred] **`log₂ p` on `2^(−X)`** for `p` on `2^(−62)`, `0 < p ≤ 2^62`: the
/// inverse face of the `ln 2`/exponential navigator (`log₂` undoes [`Exponential`]). The whole part
/// comes from the numerator's width, then `X` binary digits of the mantissa's logarithm, each read
/// by squaring the mantissa (released at `2^(−62)`) and halving it when it passes two.
pub fn log2_face(p: u128, digits: u32) -> i128 {
    debug_assert!(p > 0 && p <= 1u128 << UNIT_BITS);
    let width = 128 - p.leading_zeros(); // p in [2^(width−1), 2^width)
    let whole = width as i128 - 1 - UNIT_BITS as i128; // ≤ 0
    let mut mantissa = p << (UNIT_BITS + 1 - width); // in [2^62, 2^63)
    let mut fraction = 0i128;
    for _ in 0..digits {
        mantissa = (mantissa * mantissa) >> UNIT_BITS;
        fraction <<= 1;
        if mantissa >= 2u128 << UNIT_BITS {
            fraction |= 1;
            mantissa >>= 1;
        }
    }
    (whole << digits) + fraction
}

impl Exponential {
    pub fn new(digits: u32) -> Self {
        let mut roots = Vec::with_capacity(digits as usize);
        let mut previous: u128 = 2u128 << UNIT_BITS;
        for _ in 0..digits {
            previous = (previous << UNIT_BITS).isqrt();
            roots.push(previous);
        }
        Self { roots, digits }
    }
    /// The navigator's resident face, `2^(2^(−i))` on `2^(−62)` for `i = 1..=X`.
    pub fn roots(&self) -> &[u128] {
        &self.roots
    }

    /// `2^(x / 2^X)` for `x ≤ 0` on `2^(−62)`, at least one grain (a class is never released to
    /// zero mass by its exponent).
    pub fn below_one(&self, x: i128) -> u128 {
        debug_assert!(x <= 0);
        let whole = (-x) >> self.digits; // floor of the magnitude's whole part
        let frac = (-x) & ((1i128 << self.digits) - 1);
        // 2^(−whole − frac) = 2^(−whole − 1) · 2^(1 − frac) when frac > 0.
        let (shift, rest) = if frac == 0 { (whole, 0i128) } else { (whole + 1, (1i128 << self.digits) - frac) };
        let mut value: u128 = 1u128 << UNIT_BITS;
        for i in 0..self.digits {
            if rest & (1i128 << (self.digits - 1 - i)) != 0 {
                value = (value * self.roots[i as usize]) >> UNIT_BITS;
            }
        }
        let shifted = if shift >= 128 { 0 } else { value >> shift };
        shifted.max(1)
    }
}

/// [definition; agent-inferred] **The bank's declared law**: `K` modes, an alphabet of `A` classes
/// (the keys and the faces' classes) and its grains.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Declaration {
    pub modes: usize,
    pub alphabet: usize,
    pub grains: Grains,
}

/// Refusals of the bank's law.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub enum KeyedModesError {
    #[error("keyed modes refused: {0}")]
    Refused(&'static str),
}

/// [definition; agent-inferred] **The located material**: each mode's keyed moves and pushes, the
/// linear readout and each class's square law.
/// `lambda[k·A + a]`, `beta[k·A + a]`, `readout[c·K + k]` and `square[c·K·K + j·K + k]` (the upper
/// triangle `j ≤ k` of a Hermitian form; a diagonal entry is real), all on `2^(−P)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KeyedModes {
    pub declaration: Declaration,
    pub lambda: Vec<Gaussian>,
    pub beta: Vec<Gaussian>,
    pub readout: Vec<Gaussian>,
    pub square: Vec<Gaussian>,
    exponential: Exponential,
}

/// [definition; agent-inferred] **The bank's continuing state**: each mode's state on `2^(−(L+P))`
/// and its forward jets on `2^(−L)`, `jet_lambda[k·A + a]`, `jet_beta[k·A + a]`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModeState {
    pub z: Vec<Gaussian>,
    pub jet_lambda: Vec<Gaussian>,
    pub jet_beta: Vec<Gaussian>,
}

/// [definition; agent-inferred] **One joined face**: each class's mass `u_c = q_c 2^(w_c − w_max)`
/// on a common grain, and their sum; `p̂(c) = u_c / U` exactly.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JoinedFace {
    pub masses: Vec<u128>,
    pub total: u128,
}

impl JoinedFace {
    /// `p̂(c)` as an exact ratio.
    pub fn probability(&self, class: usize) -> (u128, u128) {
        (self.masses[class], self.total)
    }
}

/// The turn split dyadically: `(cos, sin)` of `j·π/2^n` on `2^(−P)`, by half-angle square roots
/// from the half turn (`cos(θ/2) = √((1 + cos θ)/2)`, `sin(θ/2) = √((1 − cos θ)/2)`) and exact
/// products of the half-angle rotations.
pub(crate) fn dyadic_turn(j: u64, n: u32, bits: u32) -> Gaussian {
    let one = 1i128 << bits;
    // Rotation by π/2^i for i = 0..n.
    let mut rotations = Vec::with_capacity(n as usize + 1);
    let mut cos = -one; // cos π
    rotations.push(Gaussian::new(-one, 0));
    for _ in 0..n {
        let c = (((one + cos) as u128) << bits >> 1).isqrt() as i128;
        let s = (((one - cos) as u128) << bits >> 1).isqrt() as i128;
        cos = c;
        rotations.push(Gaussian::new(c, s));
    }
    let mut value = Gaussian::new(one, 0);
    for i in 0..=n {
        // bit i of j (most significant first over n + 1 bits) selects rotation by π/2^i.
        if j & (1u64 << (n - i)) != 0 {
            value = value.mul(rotations[i as usize]).release(bits);
        }
    }
    value
}

impl KeyedModes {
    /// **The founding configuration** (agent-inferred, October 23): the navigators' initial keys
    /// cover a scale ladder and a turn ladder. Mode `k` turns by `j·π/J` and keeps `ρ = 1 − 2^(−d)`
    /// for `(d, j)` running over `d = 1..=D`, `j = 0..J` with `J = 4` and `D = K/J`; every class
    /// shares the move (the founding field is the linear one, so it codes the counts), and class `a`
    /// pushes by `(1 − ρ) e^(2πi a/A)`, so a mode's state is the normalized phase-carried moment
    /// `Σ ρ^τ e^(iθτ) e^(2πi u/A)` of the passage. The readout is zero: the joined face opens on the
    /// tree's face exactly. `A` is a power of two and `K` a multiple of `J`.
    pub fn new(declaration: Declaration) -> Result<Self, KeyedModesError> {
        const TURNS: usize = 4;
        let Declaration { modes, alphabet, grains } = declaration;
        if alphabet < 2 || !alphabet.is_power_of_two() {
            return Err(KeyedModesError::Refused("an alphabet that is a power of two, at least two"));
        }
        // No modes is lawful: the joined face is then the tree's alone.
        if modes % TURNS != 0 {
            return Err(KeyedModesError::Refused("a multiple of four modes"));
        }
        // ρ = 1 − 2^(−d) for d ≤ D sits inside the declared margin.
        if modes / TURNS > grains.margin as usize {
            return Err(KeyedModesError::Refused("the scale ladder stays inside the declared margin"));
        }
        // i128 headroom: |z| ≤ 2^(m+2) on 2^(−(L+P)) times a move on 2^(−P).
        if grains.margin + 2 + grains.face + 2 * grains.moves + 2 > 126 {
            return Err(KeyedModesError::Refused("declared grains overflow the 128-bit carrier"));
        }
        // The square law's pairs land on the linear read's grain, and its sum over a class's
        // K(K+1)/2 pairs fits: |z|² on 2^(−2Q) times |h| ≤ 2^8 on 2^(−P), and its covector's
        // reach Σ_c δ_c (H_c z)_k on 2^(−(S+P+Q)).
        if 2 * grains.square != grains.face || grains.square > grains.face {
            return Err(KeyedModesError::Refused("the square law's pairs land on the face's grain"));
        }
        let span = usize::BITS - (modes * modes).leading_zeros() + usize::BITS - alphabet.leading_zeros();
        if 2 * (grains.margin + 2 + grains.square) + 1 + grains.moves + SQUARE_BITS + span + 2 > 126
            || grains.covector + grains.moves + SQUARE_BITS + grains.margin + 2 + grains.square + span + 2 > 126
        {
            return Err(KeyedModesError::Refused("the square law overflows the 128-bit carrier"));
        }
        // The readout exponent on 2^(−(L+P)) is released to 2^(−X): X is no finer than that grain.
        if grains.exponent > grains.face + grains.moves {
            return Err(KeyedModesError::Refused("the exponent is released from the readout's grain"));
        }
        let p = grains.moves;
        let one = 1i128 << p;
        let classes_turn = alphabet.trailing_zeros(); // e^(2πi a/A) = e^(iπ·2a/A)
        let mut lambda = Vec::with_capacity(modes * alphabet);
        let mut beta = Vec::with_capacity(modes * alphabet);
        for k in 0..modes {
            let d = (k / TURNS + 1) as u32;
            let j = (k % TURNS) as u64;
            let rho = one - (one >> d);
            let turn = dyadic_turn(j, 2, p); // j·π/4
            let move_k = turn.scale(rho).release(p);
            let push = one >> d;
            for a in 0..alphabet {
                lambda.push(move_k);
                let phase = dyadic_turn(2 * a as u64, classes_turn, p);
                beta.push(phase.scale(push).release(p));
            }
        }
        Ok(Self {
            declaration,
            lambda,
            beta,
            readout: vec![Gaussian::ZERO; alphabet * modes],
            square: vec![Gaussian::ZERO; alphabet * modes * modes],
            exponential: Exponential::new(grains.exponent),
        })
    }

    /// The opening state: every mode at rest, every jet zero.
    pub fn rest(&self) -> ModeState {
        let Declaration { modes, alphabet, .. } = self.declaration;
        ModeState {
            z: vec![Gaussian::ZERO; modes],
            jet_lambda: vec![Gaussian::ZERO; modes * alphabet],
            jet_beta: vec![Gaussian::ZERO; modes * alphabet],
        }
    }

    /// A mode's face `z_k` on `2^(−L)`.
    fn face_of(&self, state: &ModeState, k: usize) -> Gaussian {
        state.z[k].release(self.declaration.grains.moves)
    }

    /// Each mode's face as the square law reads it, on `2^(−Q)`.
    fn coarse_faces(&self, state: &ModeState) -> Vec<Gaussian> {
        let g = self.declaration.grains;
        state.z.iter().map(|z| z.release(g.moves + g.face - g.square)).collect()
    }

    /// The pairs `u_(j,k) = conj(z_j) z_k` for `j ≤ k`, at `j·K + k`, on `2^(−2Q)`.
    fn pairs(&self, coarse: &[Gaussian]) -> Vec<Gaussian> {
        let modes = self.declaration.modes;
        let mut pairs = vec![Gaussian::ZERO; modes * modes];
        for j in 0..modes {
            for k in j..modes {
                pairs[j * modes + k] = coarse[j].conj_mul(coarse[k]);
            }
        }
        pairs
    }

    /// The readout exponents `w_c = Σ_k Re(conj(R_(c,k)) z_k) + zᴴ H_c z` on `2^(−(L+P))`.
    fn exponents(&self, state: &ModeState) -> Vec<i128> {
        let Declaration { modes, alphabet, .. } = self.declaration;
        let faces: Vec<Gaussian> = (0..modes).map(|k| self.face_of(state, k)).collect();
        let pairs = self.pairs(&self.coarse_faces(state));
        (0..alphabet)
            .map(|c| {
                let linear: i128 = (0..modes).map(|k| self.readout[c * modes + k].re_conj_mul(faces[k])).sum();
                let form = &self.square[c * modes * modes..(c + 1) * modes * modes];
                let mut square = 0i128;
                for j in 0..modes {
                    square += form[j * modes + j].re * pairs[j * modes + j].re;
                    for k in j + 1..modes {
                        // 2 Re(h_(j,k) conj(z_j) z_k)
                        let (h, u) = (form[j * modes + k], pairs[j * modes + k]);
                        square += 2 * (h.re * u.re - h.im * u.im);
                    }
                }
                linear + square
            })
            .collect()
    }

    /// **The joined face** at one cell: the tree's face numerators `q` on a common dyadic grain,
    /// times the navigator's `2^(w_c − w_max)`.
    pub fn joined(&self, state: &ModeState, q: &[u128]) -> Result<JoinedFace, KeyedModesError> {
        let alphabet = self.declaration.alphabet;
        if q.len() != alphabet {
            return Err(KeyedModesError::Refused("one tree mass per class"));
        }
        let g = self.declaration.grains;
        let release_bits = g.face + g.moves - g.exponent;
        let w: Vec<i128> = self.exponents(state).into_iter().map(|w| release(w, release_bits)).collect();
        let top = *w.iter().max().expect("an alphabet of at least two");
        let masses: Vec<u128> = q
            .iter()
            .zip(&w)
            .map(|(&q, &w)| {
                let e = self.exponential.below_one(w - top);
                // q ≤ 2^62 (re-based by the caller), e ≤ 2^62: the product fits.
                (q * e) >> UNIT_BITS
            })
            .collect();
        let total = masses.iter().sum();
        if total == 0 {
            return Err(KeyedModesError::Refused("a joined face with mass"));
        }
        Ok(JoinedFace { masses, total })
    }

    /// The covector `δ_c = p̂(c) − [c = t]` on `2^(−S)`.
    fn covector(&self, face: &JoinedFace, actual: usize) -> Vec<i128> {
        let s = self.declaration.grains.covector;
        let shift = (128 - face.total.leading_zeros()).saturating_sub(96);
        let total = face.total >> shift;
        face.masses
            .iter()
            .enumerate()
            .map(|(c, &u)| {
                let p = (((u >> shift) << s) + total / 2) / total;
                p as i128 - if c == actual { 1i128 << s } else { 0 }
            })
            .collect()
    }

    /// **The move**: every mode takes its class-`s` swing and push; with `jets`, the forward jets
    /// move with it.
    pub fn advance(&self, state: &mut ModeState, s: usize, jets: bool) {
        let Declaration { modes, alphabet, grains, .. } = self.declaration;
        let p = grains.moves;
        let lifted = grains.face; // a push on 2^(−P) re-based to the state's 2^(−(L+P))
        for k in 0..modes {
            let lam = self.lambda[k * alphabet + s];
            if jets {
                let face = self.face_of(state, k);
                let unit = Gaussian::new(1i128 << grains.face, 0);
                for a in 0..alphabet {
                    let i = k * alphabet + a;
                    let mut jl = lam.mul(state.jet_lambda[i]).release(p);
                    let mut jb = lam.mul(state.jet_beta[i]).release(p);
                    if a == s {
                        jl = jl.add(face);
                        jb = jb.add(unit);
                    }
                    state.jet_lambda[i] = jl;
                    state.jet_beta[i] = jb;
                }
            }
            let push = self.beta[k * alphabet + s];
            state.z[k] = lam
                .mul(state.z[k])
                .release(p)
                .add(Gaussian::new(push.re << lifted, push.im << lifted));
        }
    }

    /// The covector reached at each mode's face: `g_k = Σ_c δ_c (R_(c,k) + 2 (H_c z)_k)`, the
    /// complex gradient `∂/∂Re z_k + i ∂/∂Im z_k` of `Σ_c δ_c w_c`, on `2^(−S)`.
    fn reach(&self, coarse: &[Gaussian], delta: &[i128]) -> Vec<Gaussian> {
        let Declaration { modes, grains, .. } = self.declaration;
        (0..modes)
            .map(|k| {
                // Σ_c δ_c R_(c,k) on 2^(−(S+P)).
                let mut linear = Gaussian::ZERO;
                // Σ_c δ_c (H_c z)_k on 2^(−(S+P+Q)).
                let mut square = Gaussian::ZERO;
                for (c, &d) in delta.iter().enumerate() {
                    linear = linear.add(self.readout[c * modes + k].scale(d));
                    let form = &self.square[c * modes * modes..(c + 1) * modes * modes];
                    let mut row = Gaussian::new(form[k * modes + k].re * coarse[k].re, form[k * modes + k].re * coarse[k].im);
                    for j in 0..modes {
                        if j < k {
                            // H_(k,j) = conj(h_(j,k))
                            row = row.add(form[j * modes + k].conj_mul(coarse[j]));
                        } else if j > k {
                            row = row.add(form[k * modes + j].mul(coarse[j]));
                        }
                    }
                    square = square.add(row.scale(d));
                }
                linear
                    .release(grains.moves)
                    .add(square.scale(2).release(grains.moves + grains.square))
            })
            .collect()
    }

    /// The section's gradient contribution of one cell, added into `gradient`.
    fn accumulate(&self, state: &ModeState, face: &JoinedFace, actual: usize, gradient: &mut Gradient) {
        let Declaration { modes, alphabet, .. } = self.declaration;
        let delta = self.covector(face, actual);
        let coarse = self.coarse_faces(state);
        let reached = self.reach(&coarse, &delta);
        let pairs = self.pairs(&coarse);
        for (c, &d) in delta.iter().enumerate() {
            let at = c * modes * modes;
            for j in 0..modes {
                // ∂/∂d_j of δ_c |z_j|², and ∂/∂h_(j,k) of 2 Re(h conj(z_j) z_k) = 2 conj(u_(j,k)).
                let diagonal = gradient.square[at + j * modes + j];
                gradient.square[at + j * modes + j] = Gaussian::new(diagonal.re + d * pairs[j * modes + j].re, 0);
                for k in j + 1..modes {
                    let u = pairs[j * modes + k];
                    let i = at + j * modes + k;
                    gradient.square[i] = gradient.square[i].add(Gaussian::new(u.re, -u.im).scale(2 * d));
                }
            }
        }
        for k in 0..modes {
            let g = reached[k];
            for a in 0..alphabet {
                let i = k * alphabet + a;
                gradient.lambda[i] = gradient.lambda[i].add(state.jet_lambda[i].conj_mul(g));
                gradient.beta[i] = gradient.beta[i].add(state.jet_beta[i].conj_mul(g));
            }
            let z = self.face_of(state, k);
            for (c, &d) in delta.iter().enumerate() {
                gradient.readout[c * modes + k] = gradient.readout[c * modes + k].add(z.scale(d));
            }
        }
    }

    /// The bank moved by `−2^(−e)` of each family's gradient, normalized to its largest coordinate,
    /// with every move projected into the disk `|λ| ≤ 1 − 2^(−m)`.
    fn deposited(&self, gradient: &Gradient, e: u32) -> Self {
        let g = self.declaration.grains;
        let step = |theta: &[Gaussian], grad: &[Gaussian]| -> Vec<Gaussian> {
            let top = grad.iter().map(|x| x.max_abs()).max().unwrap_or(0);
            if top == 0 {
                return theta.to_vec();
            }
            theta
                .iter()
                .zip(grad)
                .map(|(t, x)| {
                    // x/top · 2^(P − e), the nearest numerator.
                    let scaled = |v: i128| {
                        let num = v << (g.moves - e.min(g.moves));
                        let q = num / top;
                        let r = num % top;
                        q + if 2 * r.abs() >= top { r.signum() } else { 0 }
                    };
                    t.sub(Gaussian::new(scaled(x.re), scaled(x.im)))
                })
                .collect()
        };
        let mut lambda = step(&self.lambda, &gradient.lambda);
        let radius = (1i128 << g.moves) - (1i128 << (g.moves - g.margin));
        for l in &mut lambda {
            let n = l.norm_sq();
            if n > radius * radius {
                let modulus = (n as u128).isqrt() as i128 + 1;
                *l = Gaussian::new(l.re * radius / modulus, l.im * radius / modulus);
            }
        }
        // A push keeps |β| ≤ 2^2, the bound the carrier's headroom is declared for.
        let mut beta = step(&self.beta, &gradient.beta);
        let reach = 1i128 << (g.moves + PUSH_BITS);
        for b in &mut beta {
            let n = b.norm_sq();
            if n > reach * reach {
                let modulus = (n as u128).isqrt() as i128 + 1;
                *b = Gaussian::new(b.re * reach / modulus, b.im * reach / modulus);
            }
        }
        // A form keeps |h| ≤ 2^8 and a real diagonal; its lower triangle stays empty.
        let mut square = step(&self.square, &gradient.square);
        let modes = self.declaration.modes;
        let bound = 1i128 << (g.moves + SQUARE_BITS);
        for (i, h) in square.iter_mut().enumerate() {
            let (j, k) = ((i / modes) % modes, i % modes);
            if j > k {
                *h = Gaussian::ZERO;
                continue;
            }
            if j == k {
                h.im = 0;
            }
            let n = h.norm_sq();
            if n > bound * bound {
                let modulus = (n as u128).isqrt() as i128 + 1;
                *h = Gaussian::new(h.re * bound / modulus, h.im * bound / modulus);
            }
        }
        Self {
            declaration: self.declaration,
            lambda,
            beta,
            readout: step(&self.readout, &gradient.readout),
            square,
            exponential: self.exponential.clone(),
        }
    }
}

/// [definition; agent-inferred] **A section's covector reached at each keyed move and at the
/// readout**, on `2^(−(L+S))`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Gradient {
    pub lambda: Vec<Gaussian>,
    pub beta: Vec<Gaussian>,
    pub readout: Vec<Gaussian>,
    pub square: Vec<Gaussian>,
}

impl Gradient {
    fn zero(d: &Declaration) -> Self {
        Self {
            lambda: vec![Gaussian::ZERO; d.modes * d.alphabet],
            beta: vec![Gaussian::ZERO; d.modes * d.alphabet],
            readout: vec![Gaussian::ZERO; d.alphabet * d.modes],
            square: vec![Gaussian::ZERO; d.alphabet * d.modes * d.modes],
        }
    }
}

/// [definition; agent-inferred] **The section's own cells**: each cell's tree face and actual class,
/// and the state it opened on. Released when the section closes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Section {
    pub opening: ModeState,
    pub cells: Vec<(Vec<u128>, usize)>,
    /// `Π_t u_t(actual)` and `Π_t U_t` of the faces the passage met.
    met: (BigUint, BigUint),
    gradient: Gradient,
}

/// [definition; agent-inferred] **One section's deposit receipt**: the step exponent `e` the reread
/// certified (`None`: no rung improved and the material is unchanged), and the rungs read.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DepositReceipt {
    pub certified: Option<u32>,
    pub rungs: u32,
}

/// [definition; agent-inferred] **The learner**: the bank, its continuing state, the open section
/// and the step ladder's next opening rung.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KeyedLearner {
    pub modes: KeyedModes,
    pub state: ModeState,
    pub section: Section,
    pub rung: u32,
    /// The covector of the section before, whose deposit the open section certifies.
    pub pending: Option<Gradient>,
}

/// The ladder: rungs `e = FIRST..=LAST`, opened one rung coarser than the last certified step.
const FIRST_RUNG: u32 = 2;
const LAST_RUNG: u32 = 24;

impl KeyedLearner {
    pub fn new(modes: KeyedModes) -> Self {
        let state = modes.rest();
        let section = Section::open(&modes, &state);
        Self { modes, state, section, rung: 8, pending: None }
    }

    /// The joined face the next cell meets.
    pub fn face(&self, q: &[u128]) -> Result<JoinedFace, KeyedModesError> {
        self.modes.joined(&self.state, q)
    }

    /// **Receive one cell** after its face was read: the covector reaches the section's gradient
    /// through the jets, then the class keys the move.
    pub fn receive(&mut self, q: Vec<u128>, face: &JoinedFace, actual: usize) {
        self.modes.accumulate(&self.state, face, actual, &mut self.section.gradient);
        self.section.met.0 *= face.masses[actual];
        self.section.met.1 *= face.total;
        self.section.cells.push((q, actual));
        self.modes.advance(&mut self.state, actual, true);
    }

    /// **Close the section.** The modes' families: the previous section's covector is deposited
    /// only if the deposit codes THIS section, which it never read, in strictly fewer bits than the
    /// passage met it (reread from this section's opening state); this section's covector then
    /// waits for the next. A deposit certified on the cells that produced it is seen material graded
    /// as unseen: measured October 23 on four GSM8K problems, it certified every section at the
    /// largest step and coded 1.068 bits a digit against the tree's 1.003.
    pub fn close(&mut self) -> Result<DepositReceipt, KeyedModesError> {
        let mut rungs = 0;
        let mut certified = None;
        if let Some(gradient) = self.pending.take().filter(|_| self.modes.declaration.modes > 0) {
            let start = self.rung.saturating_sub(1).max(FIRST_RUNG);
            for e in start..=LAST_RUNG {
                rungs += 1;
                let candidate = self.modes.deposited(&gradient, e);
                if self.section.improves(&candidate)? {
                    self.modes = candidate;
                    certified = Some(e);
                    self.rung = e;
                    break;
                }
            }
            if certified.is_none() {
                self.rung = LAST_RUNG.min(self.rung + 1);
            }
        }
        let closed = std::mem::replace(&mut self.section, Section::open(&self.modes, &self.state));
        self.section = Section::open(&self.modes, &self.state);
        self.pending = Some(closed.gradient);
        Ok(DepositReceipt { certified, rungs })
    }
}

const LEARNER_MAGIC: &str = "keyed-modes-learner-v4";

fn write_line(out: &mut String, values: &[Gaussian]) {
    let words: Vec<String> = values.iter().flat_map(|g| [g.re.to_string(), g.im.to_string()]).collect();
    out.push_str(&words.join(" "));
    out.push('\n');
}

fn read_line(line: Option<&str>, count: usize) -> Result<Vec<Gaussian>, KeyedModesError> {
    let words: Vec<i128> = line
        .ok_or(KeyedModesError::Refused("a saved learner's line"))?
        .split_whitespace()
        .map(str::parse)
        .collect::<Result<_, _>>()
        .map_err(|_| KeyedModesError::Refused("a saved learner's integers"))?;
    if words.len() != 2 * count {
        return Err(KeyedModesError::Refused("a saved learner's line width"));
    }
    Ok(words.chunks(2).map(|w| Gaussian::new(w[0], w[1])).collect())
}

impl KeyedLearner {
    /// **The learner at rest, as text**, at a closed section only: its declaration, the step
    /// ladder's rung, the located material and the continuing state with its jets.
    pub fn to_text(&self) -> Result<String, KeyedModesError> {
        if !self.section.cells.is_empty() {
            return Err(KeyedModesError::Refused("a learner rests only at a closed section"));
        }
        let d = self.modes.declaration;
        let g = d.grains;
        let mut out = format!(
            "{LEARNER_MAGIC}\n{} {} {} {} {} {} {} {} {}\n",
            d.modes, d.alphabet, g.moves, g.face, g.covector, g.exponent, g.margin, g.square, self.rung
        );
        for values in [
            &self.modes.lambda,
            &self.modes.beta,
            &self.modes.readout,
            &self.modes.square,
            &self.state.z,
            &self.state.jet_lambda,
            &self.state.jet_beta,
        ] {
            write_line(&mut out, values);
        }
        match &self.pending {
            None => out.push_str("none\n"),
            Some(g) => {
                out.push_str("pending\n");
                for values in [&g.lambda, &g.beta, &g.readout, &g.square] {
                    write_line(&mut out, values);
                }
            }
        }
        Ok(out)
    }

    /// The learner restored from [`KeyedLearner::to_text`].
    pub fn from_text(text: &str) -> Result<Self, KeyedModesError> {
        let mut lines = text.lines();
        if lines.next() != Some(LEARNER_MAGIC) {
            return Err(KeyedModesError::Refused("a keyed-modes learner's text"));
        }
        let head: Vec<u64> = lines
            .next()
            .ok_or(KeyedModesError::Refused("a saved learner's declaration"))?
            .split_whitespace()
            .map(str::parse)
            .collect::<Result<_, _>>()
            .map_err(|_| KeyedModesError::Refused("a saved learner's declaration"))?;
        let [modes, alphabet, moves, face, covector, exponent, margin, square, rung] = head[..] else {
            return Err(KeyedModesError::Refused("a saved learner's declaration width"));
        };
        let to = |v: u64| u32::try_from(v).map_err(|_| KeyedModesError::Refused("a declared grain"));
        let declaration = Declaration {
            modes: modes as usize,
            alphabet: alphabet as usize,
            grains: Grains {
                moves: to(moves)?,
                face: to(face)?,
                covector: to(covector)?,
                exponent: to(exponent)?,
                margin: to(margin)?,
                square: to(square)?,
            },
        };
        let mut bank = KeyedModes::new(declaration)?;
        let (m, a) = (declaration.modes, declaration.alphabet);
        bank.lambda = read_line(lines.next(), m * a)?;
        bank.beta = read_line(lines.next(), m * a)?;
        bank.readout = read_line(lines.next(), a * m)?;
        bank.square = read_line(lines.next(), a * m * m)?;
        let state = ModeState {
            z: read_line(lines.next(), m)?,
            jet_lambda: read_line(lines.next(), m * a)?,
            jet_beta: read_line(lines.next(), m * a)?,
        };
        let pending = match lines.next() {
            Some("none") => None,
            Some("pending") => Some(Gradient {
                lambda: read_line(lines.next(), m * a)?,
                beta: read_line(lines.next(), m * a)?,
                readout: read_line(lines.next(), a * m)?,
                square: read_line(lines.next(), a * m * m)?,
            }),
            _ => return Err(KeyedModesError::Refused("a saved learner's pending covector")),
        };
        if lines.next().is_some() {
            return Err(KeyedModesError::Refused("a saved learner ends after its state"));
        }
        let section = Section::open(&bank, &state);
        Ok(Self { modes: bank, state, section, rung: to(rung)?, pending })
    }

    /// **Advance without learning** (a frozen fork: a prompt, or a released cell): the class keys
    /// the move; nothing is deposited and no jet moves.
    pub fn follow(&mut self, class: usize) {
        self.modes.advance(&mut self.state, class, false);
    }
}

impl Section {
    fn open(modes: &KeyedModes, state: &ModeState) -> Self {
        Self {
            opening: ModeState {
                z: state.z.clone(),
                jet_lambda: Vec::new(),
                jet_beta: Vec::new(),
            },
            cells: Vec::new(),
            met: (BigUint::from(1u8), BigUint::from(1u8)),
            gradient: Gradient::zero(&modes.declaration),
        }
    }

    /// Whether `candidate` codes this section's cells, from its opening state, in strictly fewer
    /// bits than the faces the passage met: `Π u'(t)/U' > Π u(t)/U`, compared exactly.
    fn improves(&self, candidate: &KeyedModes) -> Result<bool, KeyedModesError> {
        let mut state = self.opening.clone();
        let mut mass = BigUint::from(1u8);
        let mut total = BigUint::from(1u8);
        for (q, actual) in &self.cells {
            let face = candidate.joined(&state, q)?;
            mass *= face.masses[*actual];
            total *= face.total;
            candidate.advance(&mut state, *actual, false);
        }
        Ok(mass * &self.met.1 > total * &self.met.0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn bank() -> KeyedModes {
        KeyedModes::new(Declaration { modes: 8, alphabet: 4, grains: Grains::DECLARED }).unwrap()
    }

    #[test]
    fn exponential_navigator_reads_dyadic_powers() {
        let x = Exponential::new(24);
        let one = 1u128 << UNIT_BITS;
        assert_eq!(x.below_one(0), one);
        assert_eq!(x.below_one(-(1 << 24)), one >> 1);
        // 2^(−1/2) within two grains of 2^62/√2.
        let half = x.below_one(-(1 << 23));
        let exact = ((one * one) >> 1).isqrt();
        assert!(half.abs_diff(exact) <= 2, "{half} {exact}");
    }

    #[test]
    fn log2_face_reads_dyadic_and_halves() {
        let one = 1u128 << 62;
        assert_eq!(log2_face(one, 24), 0);
        assert_eq!(log2_face(one >> 3, 24), -3 << 24);
        // log₂(3/4) = −0.415037499…: within one digit.
        let x = log2_face(3 * (one >> 2), 24);
        let exact = -6_963_174i128; // floor(−0.415037499… · 2^24)
        assert!((x - exact).abs() <= 1, "{x}");
    }

    #[test]
    fn dyadic_turn_is_unit_and_quarter() {
        let p = 30;
        let quarter = dyadic_turn(2, 2, p); // 2·π/4
        assert!(quarter.re.abs() <= 1 && quarter.im == 1i128 << p, "{quarter:?}");
        let eighth = dyadic_turn(1, 2, p);
        let n = eighth.norm_sq();
        assert!((n - (1i128 << (2 * p))).abs() < 1i128 << (p + 2));
    }

    #[test]
    fn founding_face_is_the_tree_face() {
        let b = bank();
        let s = b.rest();
        let q = [1u128 << 60, 1u128 << 61, 1u128 << 60, 0];
        let f = b.joined(&s, &q).unwrap();
        assert_eq!(f.masses, q.to_vec());
    }

    #[test]
    fn jets_match_finite_differences() {
        // ∂z_k/∂λ_(k,a): perturb one move by 2^(−20) and compare the change of z with the jet.
        let mut b = bank();
        b.readout = vec![Gaussian::new(1 << 28, -(1 << 27)); 4 * 8];
        let passage = [0usize, 2, 1, 3, 3, 0, 1, 2, 2, 1, 0, 3];
        let mut s = b.rest();
        for &c in &passage {
            b.advance(&mut s, c, true);
        }
        let (k, a) = (3usize, 2usize);
        let mut moved = b.clone();
        let h = 1i128 << 10; // 2^(−20) on 2^(−30)
        moved.lambda[k * 4 + a].re += h;
        let mut s2 = moved.rest();
        for &c in &passage {
            moved.advance(&mut s2, c, false);
        }
        let dz = s2.z[k].sub(s.z[k]).release(b.declaration.grains.moves); // on 2^(−L)
        let jet = s.jet_lambda[k * 4 + a]; // on 2^(−L), per unit move
        // dz ≈ jet · h·2^(−30)
        let predicted = jet.scale(h).release(30);
        let err = dz.sub(predicted).max_abs();
        assert!(err <= (predicted.max_abs() >> 6).max(1 << 12), "{dz:?} {predicted:?}");
    }

    /// A bank with a nonzero readout and square law, and a state with every mode inside `|z| ≤ 2`.
    fn shaped() -> (KeyedModes, ModeState) {
        let mut b = bank();
        let (k_count, a_count) = (8usize, 4usize);
        for c in 0..a_count {
            for j in 0..k_count {
                for k in j..k_count {
                    let v = ((c * 7 + j * 3 + k * 5) % 11) as i128 - 5;
                    b.square[c * 64 + j * 8 + k] =
                        if j == k { Gaussian::new(v << 26, 0) } else { Gaussian::new(v << 26, (v + 2) << 25) };
                }
            }
        }
        b.readout = (0..32).map(|i| Gaussian::new(((i % 7) as i128 - 3) << 27, ((i % 5) as i128 - 2) << 27)).collect();
        let mut s = b.rest();
        for (k, z) in s.z.iter_mut().enumerate() {
            *z = Gaussian::new(((k % 5) as i128 - 2) << 60, ((k % 3) as i128 - 1) << 59);
        }
        (b, s)
    }

    #[test]
    fn square_law_reach_matches_finite_differences() {
        // Σ_c δ_c w_c moved by 2^(−8) along Re z_k and Im z_k against g_k = ∂/∂Re z_k + i ∂/∂Im z_k.
        let (b, s) = shaped();
        let delta: Vec<i128> = vec![3 << 27, -(1 << 28), 1 << 26, -(5 << 26)];
        let g = b.reach(&b.coarse_faces(&s), &delta);
        let w = b.exponents(&s);
        for k in [0usize, 3, 7] {
            for (along, read) in [(Gaussian::new(1 << 54, 0), g[k].re), (Gaussian::new(0, 1 << 54), g[k].im)] {
                let mut moved = s.clone();
                moved.z[k] = moved.z[k].add(along);
                let w2 = b.exponents(&moved);
                // δ on 2^(−30) times w on 2^(−62): 2^(−92); g on 2^(−30) times 2^(−8).
                let change: i128 = (0..4).map(|c| delta[c] * (w2[c] - w[c])).sum();
                let predicted = read << 54;
                let err = (change - predicted).abs();
                assert!(err <= (predicted.abs() >> 5).max(1 << 70), "k={k} {change} {predicted}");
            }
        }
    }

    #[test]
    fn square_law_gradient_is_exact_in_its_entries() {
        // w_c is linear in each entry of its form: the accumulated gradient is the exact change.
        let (b, s) = shaped();
        let face = b.joined(&s, &[1u128 << 60; 4]).unwrap();
        let actual = 2usize;
        let mut gradient = Gradient::zero(&b.declaration);
        b.accumulate(&s, &face, actual, &mut gradient);
        let delta = b.covector(&face, actual);
        let w = b.exponents(&s);
        for (c, j, k) in [(0usize, 1usize, 4usize), (2, 3, 3), (3, 0, 7)] {
            let i = c * 64 + j * 8 + k;
            for along in [Gaussian::new(1 << 20, 0), Gaussian::new(0, 1 << 20)] {
                if j == k && along.im != 0 {
                    continue;
                }
                let mut moved = b.clone();
                moved.square[i] = moved.square[i].add(along);
                let w2 = moved.exponents(&s);
                let change = delta[c] * (w2[c] - w[c]);
                let predicted = gradient.square[i].re * along.re + gradient.square[i].im * along.im;
                assert_eq!(change, predicted, "entry ({c},{j},{k})");
            }
        }
    }

    #[test]
    fn learner_text_restores_exactly() {
        let mut learner = KeyedLearner::new(bank());
        let flat = vec![1u128 << 60; 4];
        for &c in &[0usize, 1, 2, 3, 1, 0, 2, 2, 3, 1] {
            let face = learner.face(&flat).unwrap();
            learner.receive(flat.clone(), &face, c);
        }
        learner.close().unwrap();
        let text = learner.to_text().unwrap();
        assert_eq!(KeyedLearner::from_text(&text).unwrap(), learner);
    }

    #[test]
    fn deposit_is_certified_on_the_next_section() {
        // A passage that alternates two classes: the first section's covector, deposited, codes
        // the second section (which it never read) in fewer bits.
        let mut learner = KeyedLearner::new(bank());
        let passage: Vec<usize> = (0..40).map(|t| t % 2).collect();
        let flat = vec![1u128 << 60; 4];
        let mut certified = 0;
        for chunk in passage.chunks(10) {
            for &c in chunk {
                let face = learner.face(&flat).unwrap();
                learner.receive(flat.clone(), &face, c);
            }
            let receipt = learner.close().unwrap();
            if receipt.certified.is_some() {
                certified += 1;
            }
        }
        assert!(certified > 0);
        assert!(learner.modes.readout.iter().any(|r| *r != Gaussian::ZERO));
    }
}
