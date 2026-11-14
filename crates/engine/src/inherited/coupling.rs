//! The receiver's coupling at temperature one (`receiver/coupling.rs` until C3): moved whole into the engine (C3 of the consolidation, #603), each item's
//! text as it stood but for its visibility; C5 cuts them by object (THE_CONSOLIDATION §5).

use thiserror::Error;

/// Which of the two participating strands supplied a refused face.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Strand {
    H,
    T,
}

/// A receiving chart is refused rather than truncated, repaired or guessed.
#[derive(Clone, Debug, Eq, PartialEq, Error)]
pub enum CouplingRefusal {
    #[error("coupling shape is outside the address carrier")]
    Shape,
    #[error("coupling workspace allocation refused")]
    Workspace,
    #[error("{strand:?} class {class} at {index} is outside the declared 32-class face")]
    Class {
        strand: Strand,
        index: usize,
        class: usize,
    },
    #[error("{strand:?} framing end at {index} is internal")]
    InternalEnd { strand: Strand, index: usize },
    #[error("lock radix at {level} is zero")]
    ZeroRadix { level: usize },
    #[error("{strand:?} phase path has {actual} sections, expected {expected}")]
    PhaseShape {
        strand: Strand,
        expected: usize,
        actual: usize,
    },
    #[error("{strand:?} phase at {index} does not satisfy its declared lock chart: {reason}")]
    Phase {
        strand: Strand,
        index: usize,
        reason: PhaseDefect,
    },
    #[error("coupling contact or plateau shape is inconsistent")]
    ContactShape,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Error)]
pub enum PhaseDefect {
    #[error("digit arity")]
    DigitArity,
    #[error("digit outside its radix")]
    DigitRange,
    #[error("digits do not reconstruct the finite phase")]
    DigitValue,
    #[error("finite phase outside the lock modulus")]
    ValueRange,
    #[error("lift does not equal finite phase plus modulus times winding")]
    Lift,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OptimalContact {
    pub h_index: usize,
    pub t_index: usize,
    /// One-based rank, the same on every optimum containing this contact.
    pub rank_on_any_optimal_coupling: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Plateau {
    pub h_start: usize,
    pub t_start: usize,
    pub length: usize,
    pub first_rank: usize,
}

/// Complete plural reading. Index sets are ascending; no unmatched alternative is chosen.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Coupling {
    pub h_cells: usize,
    pub t_cells: usize,
    pub lambda: usize,
    pub least_friction: usize,
    pub unresolved_h_per_optimum: usize,
    pub unresolved_t_per_optimum: usize,
    pub plural_optimal_contacts: Vec<OptimalContact>,
    pub maximal_contiguous_plateaus: Vec<Plateau>,
    pub never_held_h_indices: Vec<usize>,
    pub never_held_t_indices: Vec<usize>,
    pub may_be_unresolved_h_indices: Vec<usize>,
    pub may_be_unresolved_t_indices: Vec<usize>,
    pub always_held_h_indices: Vec<usize>,
    pub always_held_t_indices: Vec<usize>,
    pub nonempty_zero_friction: bool,
}

pub fn workspace<T: Clone>(size: usize, value: T) -> Result<Vec<T>, CouplingRefusal> {
    let mut result = Vec::new();
    result
        .try_reserve_exact(size)
        .map_err(|_| CouplingRefusal::Workspace)?;
    result.resize(size, value);
    Ok(result)
}

/// Read every longest order-consistent equal-cell coupling without selecting a tie.
/// Work and temporary space are `O((|H|+1)(|T|+1))`; no workload cap is invented here.
pub fn coupling<C: Eq>(h: &[C], t: &[C]) -> Result<Coupling, CouplingRefusal> {
    let (n, m) = (h.len(), t.len());
    let rows = n.checked_add(1).ok_or(CouplingRefusal::Shape)?;
    let cols = m.checked_add(1).ok_or(CouplingRefusal::Shape)?;
    let size = rows.checked_mul(cols).ok_or(CouplingRefusal::Shape)?;
    let total = n.checked_add(m).ok_or(CouplingRefusal::Shape)?;
    let at = |i: usize, j: usize| i * cols + j;
    let mut p = workspace(size, 0usize)?;
    let mut s = workspace(size, 0usize)?;
    for i in 0..n {
        for j in 0..m {
            p[at(i + 1, j + 1)] = if h[i] == t[j] {
                p[at(i, j)] + 1
            } else {
                p[at(i, j + 1)].max(p[at(i + 1, j)])
            };
        }
    }
    for i in (0..n).rev() {
        for j in (0..m).rev() {
            s[at(i, j)] = if h[i] == t[j] {
                s[at(i + 1, j + 1)] + 1
            } else {
                s[at(i + 1, j)].max(s[at(i, j + 1)])
            };
        }
    }
    let lambda = p[at(n, m)];
    let mut contacts = Vec::new();
    let mut held = workspace(size, false)?;
    let mut can_h = workspace(n, false)?;
    let mut can_t = workspace(m, false)?;
    for i in 0..n {
        for j in 0..m {
            if h[i] == t[j] && p[at(i, j)] + 1 + s[at(i + 1, j + 1)] == lambda {
                held[at(i, j)] = true;
                can_h[i] = true;
                can_t[j] = true;
                contacts.push(OptimalContact {
                    h_index: i,
                    t_index: j,
                    rank_on_any_optimal_coupling: p[at(i, j)] + 1,
                });
            }
        }
    }
    let mut plateaus = Vec::new();
    for contact in &contacts {
        let (i, j) = (contact.h_index, contact.t_index);
        if i > 0 && j > 0 && held[at(i - 1, j - 1)] {
            continue;
        }
        let mut length = 1;
        while length < n - i && length < m - j && held[at(i + length, j + length)] {
            length += 1;
        }
        debug_assert_eq!(p[at(i, j)] + length + s[at(i + length, j + length)], lambda);
        plateaus.push(Plateau {
            h_start: i,
            t_start: j,
            length,
            first_rank: p[at(i, j)] + 1,
        });
    }
    // An index may slip on some optimum iff deleting it preserves lambda.
    let may_h: Vec<_> = (0..n)
        .filter(|&i| (0..=m).any(|j| p[at(i, j)] + s[at(i + 1, j)] == lambda))
        .collect();
    let may_t: Vec<_> = (0..m)
        .filter(|&j| (0..=n).any(|i| p[at(i, j)] + s[at(i, j + 1)] == lambda))
        .collect();
    let least_friction = total - 2 * lambda;
    Ok(Coupling {
        h_cells: n,
        t_cells: m,
        lambda,
        least_friction,
        unresolved_h_per_optimum: n - lambda,
        unresolved_t_per_optimum: m - lambda,
        never_held_h_indices: (0..n).filter(|&i| !can_h[i]).collect(),
        never_held_t_indices: (0..m).filter(|&j| !can_t[j]).collect(),
        always_held_h_indices: (0..n).filter(|i| may_h.binary_search(i).is_err()).collect(),
        always_held_t_indices: (0..m).filter(|i| may_t.binary_search(i).is_err()).collect(),
        may_be_unresolved_h_indices: may_h,
        may_be_unresolved_t_indices: may_t,
        plural_optimal_contacts: contacts,
        maximal_contiguous_plateaus: plateaus,
        nonempty_zero_friction: lambda > 0 && least_friction == 0,
    })
}

/// [definition; agent-inferred, November 3, the comparison record §3.1 (#601)] **The coupling at temperature one**: the
/// comparison of a released strand `H` (its faces at `n` places, a class `void` among their classes) with a target
/// strand `T` of `m` cells, as the free energy of every order-keeping coupling. A coupling `c` places each of `T`'s cells
/// at one place, in order; a place it does not use writes the void. Optionally (`omit`) a cell may be left unplaced at
/// the declared cost `2^(−ℓ)` (the second slip, read by the lock face; the learning comparison omits nothing, so its
/// sum over every `T` of `2^(−L)` is one: a code).
///
/// ```text
/// Z(T | H) = Σ_c Π_((i,j)∈c) p̂_i(t_j) · Π_(i∉c) p̂_i(void) · Π_(j omitted) 2^(−ℓ),      L = −log₂ Z
/// α(i, j) = α(i−1, j) p̂_i(void) + α(i−1, j−1) p̂_i(t_j) + α(i, j−1) 2^(−ℓ)               (prefix sweep)
/// β(i, j) = β(i+1, j) p̂_(i+1)(void) + β(i+1, j+1) p̂_(i+1)(t_(j+1)) + β(i, j+1) 2^(−ℓ)     (suffix sweep)
/// γ_ij = α(i−1, j−1) p̂_i(t_j) β(i, j) / Σ_(paths through place i)                       (posterior contact)
/// r_i = Σ_j γ_ij e_(t_j) + (1 − Σ_j γ_ij) e_void,   ∂L/∂(logits at i) = p̂_i − r_i
/// ```
///
/// Every path passes each place once, by a contact or by the void, so the posterior is normalized place by place. The
/// diagonal coupling is one term, so `L ≤` the place-wise code; with `n = m` and nothing omitted it is the place-wise
/// code and `r_i = e_(t_i)`.
///
/// **Exact arithmetic.** A face enters as its masses and total; each `p̂_i(c)`, each cell of the sweeps and each
/// contact is a mass carried with its own exponent (a 63-bit mantissa, each product and sum released to the nearest at
/// its last bit), so a product of hundreds of probabilities keeps its scale. The code is `L = −log₂ α(n, m)`, read on
/// `2^(−20)` bits; a contact's share is its mass over its place's whole, on `2^(−24)`. Every operation is an integer with a
/// declared release, in the sweeps' fixed order, so any realization that forms the same cells gives the same bits. A
/// coupling whose whole releases to zero is refused, never repaired.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CouplingCode {
    /// The coupling's code `L(T | H)` on `2^(−20)` bits.
    pub code: i64,
    /// Each place's placed target `r_i` on `2^(−24)`: its cells' classes with their shares (each class once, ascending),
    /// the void's share last, the remainder of `2^24` (zero where the contacts' rounding passes it).
    pub placed: Vec<Vec<(usize, u64)>>,
    /// Each place's contact mass `Σ_j γ_ij` and expected lag `Σ_j γ_ij (i − j)` (places and cells counted from one), on
    /// `2^(−24)`: the lag field, the coupling's phase part.
    pub lag: Vec<(u64, i64)>,
}

/// Why a temperature-one coupling is refused.
#[derive(Clone, Debug, Eq, PartialEq, Error)]
pub enum TemperatureRefusal {
    #[error("the target has more cells ({cells}) than the release has places ({places}) and nothing may be omitted")]
    Short { cells: usize, places: usize },
    #[error("a target cell is the void class, which a coupling writes only by not placing a cell")]
    VoidCell,
    #[error("a face is empty, or a class lies outside it")]
    Face,
    #[error("the coupling's mass released to zero at row {row}")]
    Released { row: usize },
}

/// The grain of a placed share and a lag (the learner's covector grain, `hnn::tower::COVECTOR_BITS`).
pub const SHARE_BITS_T: u32 = 24;

/// The grain of a code (`hnn::tower::READ_BITS`).
pub const CODE_BITS: u32 = 20;

/// A mass's mantissa lies in `[2^62, 2^63)`.
pub const MANTISSA_BITS: u32 = 62;

/// [definition; agent-inferred, November 3] **A mass carried with its own exponent**: `m · 2^e` with the mantissa `m` in
/// `[2^62, 2^63)` (zero is `m = 0`), each product and sum released to the nearest at the mantissa's last bit. The
/// sweeps' products of hundreds of probabilities keep their scale in the exponent, so no cell releases to zero beside
/// a larger one, the way a row normalized as a whole on one grain did (§16.24's first build refused a GSM8K port so).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Mass {
    m: u128,
    e: i64,
}

impl Mass {
    const ZERO: Mass = Mass { m: 0, e: 0 };
    const ONE: Mass = Mass { m: 1 << MANTISSA_BITS, e: -(MANTISSA_BITS as i64) };

    /// `x · 2^e` for a whole `x`, its mantissa released to the nearest.
    pub fn of(x: u128, e: i64) -> Mass {
        if x == 0 {
            return Mass::ZERO;
        }
        let width = 128 - x.leading_zeros() as i64;
        let shift = width - 1 - MANTISSA_BITS as i64;
        let (mut m, mut e) = if shift > 0 {
            let half = 1u128 << (shift - 1);
            ((x >> shift) + u128::from(x & ((1u128 << shift) - 1) >= half), e + shift)
        } else {
            (x << (-shift), e + shift)
        };
        if m >> (MANTISSA_BITS + 1) != 0 {
            m >>= 1;
            e += 1;
        }
        Mass { m, e }
    }

    /// `mass / total`.
    fn ratio(mass: u128, total: u128) -> Mass {
        let (a, b) = (Mass::of(mass, 0), Mass::of(total, 0));
        if a.m == 0 {
            return Mass::ZERO;
        }
        // a.m / b.m in [2^(−1), 2), read on 2^(−63) to the nearest.
        let q = ((a.m << 63) + b.m / 2) / b.m;
        Mass::of(q, a.e - b.e - 63)
    }

    fn mul(self, other: Mass) -> Mass {
        if self.m == 0 || other.m == 0 {
            return Mass::ZERO;
        }
        Mass::of(self.m * other.m, self.e + other.e)
    }

    fn add(self, other: Mass) -> Mass {
        if self.m == 0 {
            return other;
        }
        if other.m == 0 {
            return self;
        }
        let (hi, lo) = if self.e >= other.e { (self, other) } else { (other, self) };
        let d = hi.e - lo.e;
        // Both mantissas on the larger's exponent less one bit of room; a term past 2^(−64) of the other releases to
        // zero, as its own release would.
        let lo_m = if d >= 64 { 0 } else if d == 0 { lo.m } else { (lo.m >> d) + u128::from(lo.m >> (d - 1) & 1 == 1) };
        Mass::of(hi.m + lo_m, hi.e)
    }

    /// `self / other` on `2^(−bits)`, to the nearest (`other` nonzero, the quotient at most one).
    fn share(self, other: Mass, bits: u32) -> u64 {
        if self.m == 0 {
            return 0;
        }
        let shift = self.e - other.e + bits as i64;
        // (self.m / other.m) · 2^shift: self.m · 2^shift / other.m.
        if shift <= -64 {
            return 0;
        }
        let num = if shift >= 0 { self.m << shift.min(64) } else { self.m >> (-shift) };
        ((num + other.m / 2) / other.m) as u64
    }

    /// `log₂` of the mass on `2^(−20)`: the exponent and the mantissa's digits read by squaring, as
    /// `hnn::keyed_modes::log2_face` reads them.
    pub fn log2(self) -> i128 {
        let mut mantissa = self.m;
        let mut fraction = 0i128;
        for _ in 0..CODE_BITS {
            mantissa = (mantissa * mantissa) >> MANTISSA_BITS;
            fraction <<= 1;
            if mantissa >= 2u128 << MANTISSA_BITS {
                fraction |= 1;
                mantissa >>= 1;
            }
        }
        ((self.e as i128 + MANTISSA_BITS as i128) << CODE_BITS) + fraction
    }
}

/// [`CouplingCode`] of `target` given the release's faces (each `(masses, total)`), the void class, and an omission
/// cost `ℓ` on `2^(−20)` bits where a cell may be left unplaced (the lock face's second slip).
pub fn coupling_code(faces: &[(&[u128], u128)], void: usize, target: &[usize], omit: Option<i64>) -> Result<CouplingCode, TemperatureRefusal> {
    let (n, m) = (faces.len(), target.len());
    if omit.is_none() && m > n {
        return Err(TemperatureRefusal::Short { cells: m, places: n });
    }
    if target.contains(&void) {
        return Err(TemperatureRefusal::VoidCell);
    }
    for (masses, total) in faces {
        if *total == 0 || void >= masses.len() || target.iter().any(|&c| c >= masses.len()) {
            return Err(TemperatureRefusal::Face);
        }
    }
    let p = |i: usize, c: usize| -> Mass { Mass::ratio(faces[i].0[c], faces[i].1) };
    // The omission's weight 2^(−ℓ): the whole bits in the exponent, the fraction's binary digits as the square roots
    // 2^(−2^(−k)), each the square root of the one before (on 2^(−62), released).
    let w: Mass = match omit {
        None => Mass::ZERO,
        Some(l) => {
            let l = l.max(0) as u128;
            let (whole, frac) = ((l >> CODE_BITS) as i64, l & ((1 << CODE_BITS) - 1));
            let (mut v, mut root) = (1u128 << MANTISSA_BITS, 1u128 << (MANTISSA_BITS - 1));
            for k in 1..=CODE_BITS {
                root = (root << MANTISSA_BITS).isqrt();
                if frac >> (CODE_BITS - k) & 1 == 1 {
                    v = (v * root + (1u128 << (MANTISSA_BITS - 1))) >> MANTISSA_BITS;
                }
            }
            Mass::of(v, -(MANTISSA_BITS as i64) - whole)
        }
    };
    // The feasible cells of row i: with nothing omitted, m − j ≤ n − i and j ≤ i.
    let lo = |i: usize| if omit.is_some() { 0 } else { m.saturating_sub(n - i) };
    let hi = |i: usize| if omit.is_some() { m } else { i.min(m) };
    // The prefix sweep.
    let mut alpha = vec![vec![Mass::ZERO; m + 1]; n + 1];
    alpha[0][0] = Mass::ONE;
    for j in 1..=hi(0) {
        alpha[0][j] = alpha[0][j - 1].mul(w);
    }
    for i in 1..=n {
        let pv = p(i - 1, void);
        for j in lo(i)..=hi(i) {
            let mut a = alpha[i - 1][j].mul(pv);
            if j > 0 {
                a = a.add(alpha[i - 1][j - 1].mul(p(i - 1, target[j - 1])));
                if omit.is_some() {
                    a = a.add(alpha[i][j - 1].mul(w));
                }
            }
            alpha[i][j] = a;
        }
    }
    let z = alpha[n][m];
    if z.m == 0 {
        return Err(TemperatureRefusal::Released { row: n });
    }
    let code = -z.log2();
    // The suffix sweep.
    let mut beta = vec![vec![Mass::ZERO; m + 1]; n + 1];
    beta[n][m] = Mass::ONE;
    if omit.is_some() {
        for j in (0..m).rev() {
            beta[n][j] = beta[n][j + 1].mul(w);
        }
    }
    for i in (0..n).rev() {
        let pv = p(i, void);
        for j in (lo(i)..=hi(i)).rev() {
            let mut b = beta[i + 1][j].mul(pv);
            if j < m {
                b = b.add(beta[i + 1][j + 1].mul(p(i, target[j])));
                if omit.is_some() {
                    b = b.add(beta[i][j + 1].mul(w));
                }
            }
            beta[i][j] = b;
        }
    }
    // The posterior, place by place: contact (i, j) is α(i−1, j−1) p̂_i(t_j) β(i, j), the void α(i−1, j) p̂_i(void) β(i, j);
    // every path passes the place by one of them, so their sum is the place's whole.
    let mut placed = Vec::with_capacity(n);
    let mut lag = Vec::with_capacity(n);
    for i in 1..=n {
        let pv = p(i - 1, void);
        let mut contact = vec![Mass::ZERO; m + 1];
        let mut total = Mass::ZERO;
        for j in 0..=m {
            total = total.add(alpha[i - 1][j].mul(pv).mul(beta[i][j]));
            if j > 0 {
                let c = alpha[i - 1][j - 1].mul(p(i - 1, target[j - 1])).mul(beta[i][j]);
                contact[j] = c;
                total = total.add(c);
            }
        }
        if total.m == 0 {
            return Err(TemperatureRefusal::Released { row: i });
        }
        let mut by_class: Vec<(usize, u64)> = Vec::new();
        let (mut mass, mut moment) = (0u64, 0i64);
        for j in 1..=m {
            let g = contact[j].share(total, SHARE_BITS_T);
            if g == 0 {
                continue;
            }
            mass += g;
            moment += g as i64 * (i as i64 - j as i64);
            match by_class.iter_mut().find(|(c, _)| *c == target[j - 1]) {
                Some(entry) => entry.1 += g,
                None => by_class.push((target[j - 1], g)),
            }
        }
        by_class.sort_unstable();
        by_class.push((void, (1u64 << SHARE_BITS_T).saturating_sub(mass)));
        placed.push(by_class);
        lag.push((mass, moment));
    }
    Ok(CouplingCode { code: code as i64, placed, lag })
}
