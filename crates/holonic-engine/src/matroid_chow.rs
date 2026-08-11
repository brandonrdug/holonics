//! The Chow ring of a matroid, and the Hodge–Riemann form on it.
//!
//! ## Why this exists: this is the positive form, on the object where it is finite and proved
//!
//! [`crate::inertia`] supplies the instrument — Sylvester's law over exact rationals — and records
//! in its own opening why the thing it replaced carried no evidence: `M^T M` is positive for every
//! integer matrix `M`, so its positivity is a property of the expression and never of the material.
//! What that module did not have is **material**. This one is the material.
//!
//! Adiprasito, Huh and Katz, *Hodge theory for combinatorial geometries*, Annals of Mathematics
//! **188** (2018), prove that the Chow ring of an **arbitrary** matroid — one that need not be
//! representable over any field, so there is no variety underneath it — satisfies Poincaré duality,
//! the hard Lefschetz theorem, and the Hodge–Riemann bilinear relations. The Hodge–Riemann relation
//! in degree one gives log-concavity of the coefficients of the characteristic polynomial, which was
//! the Heron–Rota–Welsh conjecture.
//!
//! That is the shape this project has been asking for. A **supported realizer population** — the
//! ground set and its lattice of flats. An **exactly computed positive form** — an integral,
//! finite-rank quadratic form whose split is decided by elimination and can come out wrong. A
//! **reopening rule keyed to the receiver family** — the primitive part `P^k` is the kernel of a
//! power of the chosen class `ω`, so *which* subspace the form is definite on is a function of which
//! realizer was declared, and moving `ω` moves it. Positivity here is *supplied by supportedness*:
//! `ω` must come from a strictly submodular function, and outside that cone the theorem is false.
//!
//! ## The construction
//!
//! For a simple matroid `M` of rank `r+1` on ground set `E`, with `L` the proper nonempty flats:
//!
//! ```text
//! A*(M) = Z[x_F : F in L] / (I + J)
//!   I : x_F · x_G          for F, G incomparable
//!   J : sum_{F ∋ i} x_F − sum_{F ∋ j} x_F      for each i, j in E
//! ```
//!
//! `I` is a **monomial** ideal — a monomial lies in it exactly when its support is not a chain — so
//! the degree-`k` part of `Z[x]/I` is spanned by the monomials whose support is a flag of flats. No
//! Gröbner basis is computed anywhere in this module; the Stanley–Reisner combinatorics gives the
//! spanning set outright, and `J` is then one exact rational row reduction per grade. `J` is
//! generated in degree one, so its degree-`k` part is `(chain monomials of degree k−1) · J_1`, and
//! the reduction is a rank computation over [`Rat`], never a float.
//!
//! [`ChowRing`] carries, per grade, the chain monomials, the subset of them chosen as a basis, and
//! the exact expression of every other monomial in that basis. [`ChowRing::monomial_basis_is_integral`]
//! reports whether those expressions came out over `Z`, which is the certificate that the chosen
//! monomials are a **`Z`-basis** and not merely a `Q`-basis.
//!
//! ## The forms, and the hand
//!
//! Fix `ω` in degree one. For `2k ≤ r`:
//!
//! - **Hard Lefschetz**: `ω^{r−2k} : A^k → A^{r−k}` is an isomorphism.
//! - **Hodge–Riemann**: on `P^k = ker(ω^{r−2k+1} : A^k → A^{r−k+1})` the form
//!   `(a,b) ↦ (−1)^k deg(ω^{r−2k} · a · b)` is positive definite.
//!
//! Following `CLAUDE.md` §2b, this module never says a form *is* positive. It returns the **split**
//! — [`Inertia`], which no change of basis moves — and separately the **hand**, the declared
//! `(−1)^k` twist that decides which of the two cones is being called the returning one. A
//! [`LefschetzReport`] carries both, and `hodge_riemann_holds` is the composite claim about the pair,
//! not a property of the matrix alone.
//!
//! The Lefschetz decomposition `A^k = ⊕_{j≤k} ω^{k−j} P^j` then **predicts** the split of the form
//! on all of `A^k`, sign alternating with `j`. That prediction is computed from the primitive
//! dimensions and compared against what [`inertia`] returns from the full matrix by elimination.
//! Two frames, one construction, and the comparison can fail.
//!
//! ## What can fail, and does
//!
//! [`ChowRing::submodularity_verdict`] certifies whether a declared coefficient family is strictly
//! submodular *before* it is used, so a falsifier is known to be outside the ample cone rather than
//! asserted to be. A strictly **super**modular family is outside it, and on every rank-three fixture
//! here it drives `deg(ω²)` negative, which puts a returning direction inside `ω^⊥` and breaks
//! Hodge–Riemann. The `−ω` of an ample `ω` breaks the top grade whenever `r` is odd. The **modular**
//! family sits exactly on the boundary of the cone and — this is a measured finding, not an
//! assumption — does *not* break Hodge–Riemann at these degrees; the tests record that rather than
//! hide it.
//!
//! ## Aperture
//!
//! Declared and enforced: ground set at most [`GROUND_APERTURE`], rank at most [`RANK_APERTURE`].
//! The rank table is dense over `2^|E|` subsets and the matroid axioms are checked over all pairs of
//! subsets, which is `4^|E|`; the grade-`k` row reduction is cubic in the number of chain monomials,
//! which grows fast in the rank. The Vámos matroid (rank 4 on 8 elements, representable over no
//! division ring) is **inside** the aperture as a matroid and **outside** it as a ring: its top grade
//! carries 997 chain monomials against 2 793 relation rows, and that elimination was not run.
//! [`Matroid::vamos`] and [`chain_monomial_census`] exist so the wall can be stated with counts
//! rather than adjectives.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::inertia::{Inertia, InertiaError, SymmetricForm, inertia};
use crate::rebase_invariants::{IntegerMatrix, PivotRule, smith_normal_form};
use crate::winding_inertia::{CyclicReceiver, WindingError, cyclic_receiver_of_form};

/// A subset of the ground set, as a bitmask. The ground set is bounded by [`GROUND_APERTURE`], so
/// one machine word holds every subset and the empty set is `0`.
pub type Subset = u32;

/// The declared ground-set aperture. The rank table is `2^|E|` entries and the matroid-axiom audit
/// is `4^|E|` comparisons; nine elements is 512 and 262 144, which is a fixture and not a run.
pub const GROUND_APERTURE: usize = 9;

/// The declared rank aperture. Rank five would put four-fold flags in the top grade and the row
/// reduction there is cubic in a monomial count that grows with the flag length.
pub const RANK_APERTURE: usize = 4;

fn rational(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

// -------------------------------------------------------------------------------------------
// the matroid

/// A simple matroid, carried as its complete rank function.
///
/// The rank function is stored densely and **audited** at construction against the three matroid
/// axioms plus simplicity. A fixture that is not a matroid is refused by name, which matters because
/// every theorem below is false for a general set function and a wrong fixture would otherwise
/// present as a wrong theorem.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Matroid {
    name: String,
    ground: usize,
    ranks: Vec<u32>,
}

impl Matroid {
    /// Build from a complete rank table, auditing every axiom.
    ///
    /// The audit is the point. `r(∅) = 0`, unit increase, submodularity, no loop, no parallel pair —
    /// each has a named refusal, and `a_set_function_that_is_not_submodular_is_refused` shows the
    /// submodularity branch fires rather than assuming a fixture reached it.
    pub fn from_rank_table(
        name: &str,
        ground: usize,
        ranks: Vec<u32>,
    ) -> Result<Self, MatroidError> {
        if ground == 0 || ground > GROUND_APERTURE {
            return Err(MatroidError::GroundSetOutsideAperture {
                ground,
                aperture: GROUND_APERTURE,
            });
        }
        let extent = 1usize << ground;
        if ranks.len() != extent {
            return Err(MatroidError::RankTableShape {
                found: ranks.len(),
                expected: extent,
            });
        }
        if ranks[0] != 0 {
            return Err(MatroidError::EmptySetHasRank { rank: ranks[0] });
        }
        for subset in 0..extent {
            for element in 0..ground {
                let bit = 1usize << element;
                if subset & bit != 0 {
                    continue;
                }
                let grown = subset | bit;
                if ranks[grown] < ranks[subset] || ranks[grown] > ranks[subset] + 1 {
                    return Err(MatroidError::NotUnitIncrease {
                        subset: subset as Subset,
                        element,
                        rank: ranks[subset],
                        grown: ranks[grown],
                    });
                }
            }
        }
        for left in 0..extent {
            for right in left..extent {
                if ranks[left] + ranks[right] < ranks[left | right] + ranks[left & right] {
                    return Err(MatroidError::NotSubmodular {
                        left: left as Subset,
                        right: right as Subset,
                    });
                }
            }
        }
        if ranks[extent - 1] == 0 {
            return Err(MatroidError::RankZero);
        }
        for element in 0..ground {
            if ranks[1usize << element] == 0 {
                return Err(MatroidError::Loop { element });
            }
        }
        for left in 0..ground {
            for right in (left + 1)..ground {
                if ranks[(1usize << left) | (1usize << right)] < 2 {
                    return Err(MatroidError::ParallelPair { left, right });
                }
            }
        }
        Ok(Self {
            name: name.to_owned(),
            ground,
            ranks,
        })
    }

    /// `U_{k,n}`: every subset has rank `min(|S|, k)`.
    pub fn uniform(rank: usize, ground: usize) -> Result<Self, MatroidError> {
        if ground == 0 || ground > GROUND_APERTURE {
            return Err(MatroidError::GroundSetOutsideAperture {
                ground,
                aperture: GROUND_APERTURE,
            });
        }
        let ranks = (0..1usize << ground)
            .map(|subset| (subset.count_ones() as usize).min(rank) as u32)
            .collect();
        Self::from_rank_table(&format!("U({rank},{ground})"), ground, ranks)
    }

    /// The cycle matroid of a graph: `r(S) = |V| − (components of the subgraph on S)`.
    pub fn graphic(
        name: &str,
        vertices: usize,
        edges: &[(usize, usize)],
    ) -> Result<Self, MatroidError> {
        let ground = edges.len();
        if ground == 0 || ground > GROUND_APERTURE {
            return Err(MatroidError::GroundSetOutsideAperture {
                ground,
                aperture: GROUND_APERTURE,
            });
        }
        let ranks = (0..1usize << ground)
            .map(|subset| {
                let mut parent: Vec<usize> = (0..vertices).collect();
                for (index, (left, right)) in edges.iter().enumerate() {
                    if subset & (1usize << index) == 0 {
                        continue;
                    }
                    let (mut a, mut b) = (*left, *right);
                    while parent[a] != a {
                        a = parent[a];
                    }
                    while parent[b] != b {
                        b = parent[b];
                    }
                    if a != b {
                        parent[b] = a;
                    }
                }
                let components = (0..vertices).filter(|node| parent[*node] == *node).count();
                (vertices - components) as u32
            })
            .collect();
        Self::from_rank_table(name, ground, ranks)
    }

    /// A rank-three simple matroid presented by its lines of three or more points.
    ///
    /// Every other pair spans a two-point line. This is how `F_7` and the non-Pappus matroid are
    /// written; a line set that is not a linear space (two lines meeting twice, say) fails the
    /// submodularity audit rather than producing a plausible ring.
    pub fn rank_three_from_lines(
        name: &str,
        ground: usize,
        lines: &[&[usize]],
    ) -> Result<Self, MatroidError> {
        if ground == 0 || ground > GROUND_APERTURE {
            return Err(MatroidError::GroundSetOutsideAperture {
                ground,
                aperture: GROUND_APERTURE,
            });
        }
        let masks: Vec<Subset> = lines
            .iter()
            .map(|line| line.iter().fold(0 as Subset, |mask, e| mask | (1 << e)))
            .collect();
        let ranks = (0..1usize << ground)
            .map(|subset| {
                let subset = subset as Subset;
                match subset.count_ones() {
                    0 => 0,
                    1 => 1,
                    2 => 2,
                    _ => {
                        if masks.iter().any(|mask| subset & !mask == 0) {
                            2
                        } else {
                            3
                        }
                    }
                }
            })
            .collect();
        Self::from_rank_table(name, ground, ranks)
    }

    /// A paving matroid of the declared rank, presented by its circuit-hyperplanes.
    ///
    /// Every set of fewer than `rank` elements is independent; a set of exactly `rank` elements is
    /// dependent exactly when it is one of the declared circuits.
    pub fn paving(
        name: &str,
        ground: usize,
        rank: usize,
        circuit_hyperplanes: &[&[usize]],
    ) -> Result<Self, MatroidError> {
        if ground == 0 || ground > GROUND_APERTURE {
            return Err(MatroidError::GroundSetOutsideAperture {
                ground,
                aperture: GROUND_APERTURE,
            });
        }
        let masks: Vec<Subset> = circuit_hyperplanes
            .iter()
            .map(|circuit| circuit.iter().fold(0 as Subset, |mask, e| mask | (1 << e)))
            .collect();
        let ranks = (0..1usize << ground)
            .map(|subset| {
                let subset = subset as Subset;
                let size = subset.count_ones() as usize;
                if size == rank && masks.contains(&subset) {
                    (rank - 1) as u32
                } else {
                    size.min(rank) as u32
                }
            })
            .collect();
        Self::from_rank_table(name, ground, ranks)
    }

    /// The Vámos matroid: rank four on eight elements, representable over no division ring.
    ///
    /// Present here for its combinatorics. Its Chow ring is outside this module's declared aperture
    /// and [`chain_monomial_census`] says by how much.
    pub fn vamos() -> Result<Self, MatroidError> {
        Self::paving(
            "Vamos V8",
            8,
            4,
            &[
                &[0, 1, 2, 3],
                &[0, 1, 4, 5],
                &[0, 1, 6, 7],
                &[2, 3, 4, 5],
                &[2, 3, 6, 7],
            ],
        )
    }

    pub fn name(&self) -> &str {
        &self.name
    }

    pub const fn ground(&self) -> usize {
        self.ground
    }

    pub fn rank_of(&self, subset: Subset) -> usize {
        self.ranks[subset as usize] as usize
    }

    /// The rank of the matroid itself. The Chow ring's top grade is one less.
    pub fn rank(&self) -> usize {
        self.ranks[self.ranks.len() - 1] as usize
    }

    pub fn closure(&self, subset: Subset) -> Subset {
        let mut closed = subset;
        for element in 0..self.ground {
            let bit = 1 << element;
            if closed & bit != 0 {
                continue;
            }
            if self.rank_of(closed | bit) == self.rank_of(closed) {
                closed |= bit;
            }
        }
        closed
    }

    pub fn is_flat(&self, subset: Subset) -> bool {
        (0..self.ground).all(|element| {
            let bit = 1 << element;
            subset & bit != 0 || self.rank_of(subset | bit) > self.rank_of(subset)
        })
    }

    /// Every flat, including `∅` and `E`, ordered by rank and then by mask.
    pub fn flats(&self) -> Vec<Subset> {
        let mut flats: Vec<Subset> = (0..(1 as Subset) << self.ground)
            .filter(|subset| self.is_flat(*subset))
            .collect();
        flats.sort_by_key(|flat| (self.rank_of(*flat), *flat));
        flats
    }

    /// The proper nonempty flats — one generator of the Chow ring each, one ray of the Bergman fan
    /// each. Ordered by rank then mask, so a chain is increasing in index.
    pub fn proper_flats(&self) -> Vec<Subset> {
        let full = ((1 as Subset) << self.ground) - 1;
        self.flats()
            .into_iter()
            .filter(|flat| *flat != 0 && *flat != full)
            .collect()
    }

    /// `μ(∅, F)` over the lattice of flats, indexed in the order [`Matroid::flats`] returns.
    pub fn moebius(&self) -> Vec<BigInt> {
        let flats = self.flats();
        let mut values: Vec<BigInt> = Vec::with_capacity(flats.len());
        for (index, flat) in flats.iter().enumerate() {
            if *flat == 0 {
                values.push(BigInt::one());
                continue;
            }
            let mut total = BigInt::zero();
            for (below, lower) in flats.iter().enumerate().take(index) {
                if lower & !flat == 0 {
                    total += &values[below];
                }
            }
            values.push(-total);
        }
        values
    }

    /// The characteristic polynomial `χ_M(t)`, coefficients descending from `t^{rank}`.
    pub fn characteristic_polynomial(&self) -> Vec<BigInt> {
        let flats = self.flats();
        let moebius = self.moebius();
        let rank = self.rank();
        let mut coefficients = vec![BigInt::zero(); rank + 1];
        for (index, flat) in flats.iter().enumerate() {
            let power = rank - self.rank_of(*flat);
            coefficients[rank - power] += &moebius[index];
        }
        coefficients
    }

    /// `χ_M(t) / (t − 1)`, coefficients descending from `t^{rank−1}`.
    ///
    /// `(t − 1)` always divides `χ_M`, and the remainder is returned as a refusal rather than
    /// discarded: a nonzero remainder would mean the lattice audit above had let a non-matroid
    /// through.
    pub fn reduced_characteristic_polynomial(&self) -> Result<Vec<BigInt>, MatroidError> {
        let coefficients = self.characteristic_polynomial();
        let mut quotient: Vec<BigInt> = Vec::with_capacity(coefficients.len() - 1);
        let mut carry = BigInt::zero();
        for (index, coefficient) in coefficients.iter().enumerate() {
            carry = coefficient + &carry;
            if index + 1 == coefficients.len() {
                break;
            }
            quotient.push(carry.clone());
        }
        if !carry.is_zero() {
            return Err(MatroidError::CharacteristicRemainder {
                remainder: carry.to_string(),
            });
        }
        Ok(quotient)
    }

    /// `|μ^k|`, the unsigned coefficients of the reduced characteristic polynomial. These are the
    /// numbers Heron–Rota–Welsh says are log-concave.
    pub fn reduced_characteristic_magnitudes(&self) -> Result<Vec<BigInt>, MatroidError> {
        Ok(self
            .reduced_characteristic_polynomial()?
            .into_iter()
            .map(|coefficient| coefficient.abs())
            .collect())
    }
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum MatroidError {
    #[error("ground set of {ground} elements is outside the declared aperture of {aperture}")]
    GroundSetOutsideAperture { ground: usize, aperture: usize },
    #[error("a rank table over {expected} subsets was expected; {found} were supplied")]
    RankTableShape { found: usize, expected: usize },
    #[error("the empty set must have rank zero; this table gives it {rank}")]
    EmptySetHasRank { rank: u32 },
    #[error(
        "rank must grow by zero or one: subset {subset:#b} has rank {rank}, adding element \
         {element} gives {grown}"
    )]
    NotUnitIncrease {
        subset: Subset,
        element: usize,
        rank: u32,
        grown: u32,
    },
    #[error("the rank function is not submodular at the pair ({left:#b}, {right:#b})")]
    NotSubmodular { left: Subset, right: Subset },
    #[error("a matroid of rank zero carries no realizer population")]
    RankZero,
    #[error("element {element} is a loop; this construction is stated for simple matroids")]
    Loop { element: usize },
    #[error("elements {left} and {right} are parallel; this construction is stated for simple matroids")]
    ParallelPair { left: usize, right: usize },
    #[error("(t − 1) failed to divide the characteristic polynomial; remainder {remainder}")]
    CharacteristicRemainder { remainder: String },
}

// -------------------------------------------------------------------------------------------
// monomials over a flag of flats

/// A monomial `x_{F_1}^{m_1} ··· x_{F_p}^{m_p}` whose support is a **flag** — a chain of flats.
///
/// Every monomial outside `I` has this shape, and every monomial of this shape is outside `I`, so
/// this type is exactly the spanning set of `(Z[x]/I)_k`. Factors are stored ascending in flat
/// index, and flats are ordered by rank, so the stored order is the order of the flag.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct FlagMonomial {
    factors: Vec<(usize, usize)>,
}

impl FlagMonomial {
    pub fn unit() -> Self {
        Self {
            factors: Vec::new(),
        }
    }

    pub fn single(flat: usize, exponent: usize) -> Self {
        Self {
            factors: vec![(flat, exponent)],
        }
    }

    pub fn factors(&self) -> &[(usize, usize)] {
        &self.factors
    }

    pub fn degree(&self) -> usize {
        self.factors.iter().map(|(_, exponent)| exponent).sum()
    }

    pub fn flag_length(&self) -> usize {
        self.factors.len()
    }

    /// `self · other`, or `None` when the joined support is not a chain — which is exactly the
    /// statement that the product lies in `I` and is therefore zero.
    fn times(&self, other: &Self, comparable: &[Vec<bool>]) -> Option<Self> {
        let mut factors = self.factors.clone();
        for (flat, exponent) in &other.factors {
            match factors.binary_search_by_key(flat, |(index, _)| *index) {
                Ok(position) => factors[position].1 += exponent,
                Err(position) => {
                    for (index, _) in &factors {
                        if !comparable[*index][*flat] {
                            return None;
                        }
                    }
                    factors.insert(position, (*flat, *exponent));
                }
            }
        }
        Some(Self { factors })
    }

    fn times_generator(&self, flat: usize, comparable: &[Vec<bool>]) -> Option<Self> {
        self.times(&Self::single(flat, 1), comparable)
    }
}

/// How many chain monomials and relation rows a grade would carry, without building it.
///
/// This is the instrument that lets an aperture wall be stated with counts. `Vámos` is refused as a
/// ring by [`ChowRing::new`] only because this census says what it would cost.
pub fn chain_monomial_census(matroid: &Matroid, degree: usize) -> Result<(usize, usize), ChowError> {
    let flats = matroid.proper_flats();
    let containment = strict_containment(&flats);
    let top = matroid.rank().saturating_sub(1);
    let chains = enumerate_chains(&containment, top.max(1));
    let count = |wanted: usize| -> usize {
        if wanted == 0 {
            return 1;
        }
        chains
            .iter()
            .filter(|chain| chain.len() <= wanted)
            .map(|chain| composition_count(wanted, chain.len()))
            .sum()
    };
    let monomials = count(degree);
    let previous = if degree == 0 { 0 } else { count(degree - 1) };
    Ok((monomials, previous * matroid.ground().saturating_sub(1)))
}

fn composition_count(total: usize, parts: usize) -> usize {
    if parts == 0 {
        return usize::from(total == 0);
    }
    if total < parts {
        return 0;
    }
    // Compositions of `total` into `parts` positive parts: C(total − 1, parts − 1).
    let mut value = 1usize;
    for step in 0..(parts - 1) {
        value = value * (total - 1 - step) / (step + 1);
    }
    value
}

fn compositions(total: usize, parts: usize) -> Vec<Vec<usize>> {
    if parts == 0 {
        return if total == 0 { vec![Vec::new()] } else { Vec::new() };
    }
    let mut out = Vec::new();
    let ceiling = total.saturating_sub(parts - 1);
    for first in 1..=ceiling {
        for rest in compositions(total - first, parts - 1) {
            let mut one = Vec::with_capacity(parts);
            one.push(first);
            one.extend(rest);
            out.push(one);
        }
    }
    out
}

fn strict_containment(flats: &[Subset]) -> Vec<Vec<bool>> {
    (0..flats.len())
        .map(|low| {
            (0..flats.len())
                .map(|high| flats[low] != flats[high] && flats[low] & !flats[high] == 0)
                .collect()
        })
        .collect()
}

fn comparability(flats: &[Subset]) -> Vec<Vec<bool>> {
    (0..flats.len())
        .map(|left| {
            (0..flats.len())
                .map(|right| {
                    flats[left] & !flats[right] == 0 || flats[right] & !flats[left] == 0
                })
                .collect()
        })
        .collect()
}

fn enumerate_chains(containment: &[Vec<bool>], max_length: usize) -> Vec<Vec<usize>> {
    let mut out = Vec::new();
    let mut current = Vec::new();
    extend_chains(containment, &mut current, max_length, &mut out);
    out
}

fn extend_chains(
    containment: &[Vec<bool>],
    current: &mut Vec<usize>,
    max_length: usize,
    out: &mut Vec<Vec<usize>>,
) {
    let start = current.last().map_or(0, |last| last + 1);
    for next in start..containment.len() {
        if let Some(last) = current.last()
            && !containment[*last][next] {
                continue;
            }
        current.push(next);
        out.push(current.clone());
        if current.len() < max_length {
            extend_chains(containment, current, max_length, out);
        }
        current.pop();
    }
}

// -------------------------------------------------------------------------------------------
// exact rational row reduction

/// The order in which the row reduction visits columns when it chooses pivots.
///
/// A pivot column is a **solver coordinate**, exactly as [`crate::inertia::PivotOrder`] is. The
/// dimension of the quotient cannot depend on it — that is linear algebra, and
/// `the_dimension_does_not_depend_on_the_basis_order` holds this module to it by recording the
/// dimension every order returned rather than the one it kept.
///
/// What the order **does** decide is *which* monomials come out as the basis, and therefore whether
/// the rest reduce over `Z` or only over `Q`. A maximal independent set of monomials is not
/// automatically a `Z`-basis: `L = Z·(2,3)` in `Z²` is saturated with free quotient and neither
/// coordinate generates it. So the orders are tried in sequence and the first that certifies an
/// integral reduction is kept; if none does, that is reported rather than hidden.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum BasisOrder {
    /// Storage order. Low-rank flats and short flags first, so the reduction spends its pivots
    /// eliminating them and keeps deep flags as the basis.
    Ascending,
    /// Storage order reversed.
    Descending,
    /// Shortest flags first, ties in storage order.
    ShortFlagsFirst,
    /// Longest flags first, ties in storage order.
    LongFlagsFirst,
}

impl BasisOrder {
    pub const ALL: [Self; 4] = [
        Self::Ascending,
        Self::Descending,
        Self::ShortFlagsFirst,
        Self::LongFlagsFirst,
    ];

    fn sequence(self, monomials: &[FlagMonomial]) -> Vec<usize> {
        let mut order: Vec<usize> = (0..monomials.len()).collect();
        match self {
            Self::Ascending => {}
            Self::Descending => order.reverse(),
            Self::ShortFlagsFirst => {
                order.sort_by_key(|index| (monomials[*index].flag_length(), *index));
            }
            Self::LongFlagsFirst => {
                order.sort_by_key(|index| {
                    (std::cmp::Reverse(monomials[*index].flag_length()), *index)
                });
            }
        }
        order
    }
}

/// Reduced row echelon form over [`Rat`] in storage column order.
fn row_reduce(rows: &mut Vec<Vec<Rat>>, columns: usize) -> Vec<usize> {
    let sequence: Vec<usize> = (0..columns).collect();
    row_reduce_ordered(rows, columns, &sequence)
}

/// Reduced row echelon form over [`Rat`], visiting columns in a declared order and returning the
/// pivot columns in the order they were taken.
///
/// Exact throughout. The zero-skip in the inner loop is a cost decision and can never change what is
/// returned: skipping a multiplication by zero is skipping a subtraction of zero.
fn row_reduce_ordered(
    rows: &mut Vec<Vec<Rat>>,
    columns: usize,
    sequence: &[usize],
) -> Vec<usize> {
    let mut pivots = Vec::new();
    let mut cursor = 0usize;
    for column in sequence.iter().copied() {
        if cursor == rows.len() {
            break;
        }
        let Some(found) = (cursor..rows.len()).find(|row| !rows[*row][column].is_zero()) else {
            continue;
        };
        rows.swap(cursor, found);
        let inverse = Rat::one() / rows[cursor][column].clone();
        for entry in rows[cursor].iter_mut() {
            if !entry.is_zero() {
                *entry *= inverse.clone();
            }
        }
        let pivot_row = rows[cursor].clone();
        for (index, row) in rows.iter_mut().enumerate() {
            if index == cursor {
                continue;
            }
            let factor = row[column].clone();
            if factor.is_zero() {
                continue;
            }
            // Every column, not a suffix: under a permuted visiting order an already-cleared column
            // can sit anywhere in storage.
            for target in 0..columns {
                if pivot_row[target].is_zero() {
                    continue;
                }
                row[target] -= pivot_row[target].clone() * factor.clone();
            }
        }
        pivots.push(column);
        cursor += 1;
    }
    pivots
}

/// A basis of `ker(matrix)`, exactly, one vector per free column.
fn null_space(matrix: &[Vec<Rat>], columns: usize) -> Vec<Vec<Rat>> {
    let mut rows: Vec<Vec<Rat>> = matrix.to_vec();
    let pivots = row_reduce(&mut rows, columns);
    let free: Vec<usize> = (0..columns)
        .filter(|column| !pivots.contains(column))
        .collect();
    free.iter()
        .map(|column| {
            let mut vector = vec![Rat::zero(); columns];
            vector[*column] = Rat::one();
            for (index, pivot) in pivots.iter().enumerate() {
                vector[*pivot] = -rows[index][*column].clone();
            }
            vector
        })
        .collect()
}

fn rational_rank(matrix: &[Vec<Rat>], columns: usize) -> usize {
    let mut rows: Vec<Vec<Rat>> = matrix.to_vec();
    row_reduce(&mut rows, columns).len()
}

// -------------------------------------------------------------------------------------------
// the graded ring

#[derive(Clone, Debug)]
struct Grade {
    monomials: Vec<FlagMonomial>,
    lookup: BTreeMap<FlagMonomial, usize>,
    basis: Vec<usize>,
    reduction: Vec<Vec<Rat>>,
    integral: bool,
    order: BasisOrder,
    dimension_by_order: Vec<(BasisOrder, usize)>,
    relation_rows: usize,
}

impl Grade {
    fn dimension(&self) -> usize {
        self.basis.len()
    }
}

/// An element of the Chow ring, in the chosen monomial basis of its grade.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Element {
    degree: usize,
    coordinates: Vec<Rat>,
}

impl Element {
    pub const fn degree(&self) -> usize {
        self.degree
    }

    pub fn coordinates(&self) -> &[Rat] {
        &self.coordinates
    }

    pub fn is_zero(&self) -> bool {
        self.coordinates.iter().all(Zero::is_zero)
    }
}

/// The Chow ring `A*(M)`, graded, with an exact reduction to a monomial basis in every grade.
#[derive(Clone, Debug)]
pub struct ChowRing {
    matroid: Matroid,
    flats: Vec<Subset>,
    comparable: Vec<Vec<bool>>,
    top: usize,
    grades: Vec<Grade>,
    top_basis_degree: Rat,
    complete_flags: usize,
}

impl ChowRing {
    /// Build the whole ring, grade by grade, and fix the degree map.
    ///
    /// Refuses a matroid of rank below two by name: with no proper nonempty flat there is no
    /// generator, no ample class, and nothing for a form to be computed on. That is the "degenerate
    /// matroid" refusal, and it is a type-level refusal rather than a silently trivial answer.
    pub fn new(matroid: Matroid) -> Result<Self, ChowError> {
        if matroid.rank() > RANK_APERTURE {
            return Err(ChowError::RankOutsideAperture {
                rank: matroid.rank(),
                aperture: RANK_APERTURE,
            });
        }
        if matroid.rank() < 2 {
            return Err(ChowError::NoProperFlats {
                rank: matroid.rank(),
            });
        }
        let top = matroid.rank() - 1;
        let flats = matroid.proper_flats();
        if flats.is_empty() {
            return Err(ChowError::NoProperFlats {
                rank: matroid.rank(),
            });
        }
        let comparable = comparability(&flats);
        let containment = strict_containment(&flats);
        let chains = enumerate_chains(&containment, top);

        let mut grades: Vec<Grade> = Vec::with_capacity(top + 1);
        for degree in 0..=top {
            let previous = if degree == 0 {
                None
            } else {
                Some(&grades[degree - 1])
            };
            grades.push(build_grade(
                &flats,
                &comparable,
                &chains,
                matroid.ground(),
                degree,
                previous,
            ));
        }

        if grades[top].dimension() != 1 {
            return Err(ChowError::TopGradeNotOneDimensional {
                dimension: grades[top].dimension(),
            });
        }

        // The degree map: every complete flag of proper flats normalises to one. That every flag
        // agrees is a control, not an assumption.
        let mut flag_value: Option<Rat> = None;
        let mut complete_flags = 0usize;
        for chain in &chains {
            if chain.len() != top {
                continue;
            }
            if chain
                .iter()
                .enumerate()
                .any(|(step, flat)| matroid.rank_of(flats[*flat]) != step + 1)
            {
                continue;
            }
            complete_flags += 1;
            let monomial = FlagMonomial {
                factors: chain.iter().map(|flat| (*flat, 1)).collect(),
            };
            let column = *grades[top]
                .lookup
                .get(&monomial)
                .ok_or(ChowError::FlagMonomialMissing)?;
            let coefficient = grades[top].reduction[column][0].clone();
            match &flag_value {
                None => flag_value = Some(coefficient),
                Some(known) => {
                    if *known != coefficient {
                        return Err(ChowError::DegreeMapInconsistent {
                            first: known.to_string(),
                            second: coefficient.to_string(),
                        });
                    }
                }
            }
        }
        let Some(flag_value) = flag_value else {
            return Err(ChowError::NoCompleteFlag);
        };
        if flag_value.is_zero() {
            return Err(ChowError::DegenerateDegreeMap);
        }
        let top_basis_degree = Rat::one() / flag_value;

        Ok(Self {
            matroid,
            flats,
            comparable,
            top,
            grades,
            top_basis_degree,
            complete_flags,
        })
    }

    pub fn matroid(&self) -> &Matroid {
        &self.matroid
    }

    /// The top grade `r`, one less than the rank of the matroid.
    pub const fn top(&self) -> usize {
        self.top
    }

    pub fn flats(&self) -> &[Subset] {
        &self.flats
    }

    pub fn complete_flag_count(&self) -> usize {
        self.complete_flags
    }

    pub fn dimension(&self, degree: usize) -> usize {
        if degree > self.top {
            0
        } else {
            self.grades[degree].dimension()
        }
    }

    pub fn dimensions(&self) -> Vec<usize> {
        (0..=self.top).map(|degree| self.dimension(degree)).collect()
    }

    pub fn chain_monomial_count(&self, degree: usize) -> usize {
        if degree > self.top {
            0
        } else {
            self.grades[degree].monomials.len()
        }
    }

    pub fn relation_row_count(&self, degree: usize) -> usize {
        if degree > self.top {
            0
        } else {
            self.grades[degree].relation_rows
        }
    }

    /// The monomials chosen as the basis of a grade.
    pub fn monomial_basis(&self, degree: usize) -> Vec<FlagMonomial> {
        if degree > self.top {
            return Vec::new();
        }
        self.grades[degree]
            .basis
            .iter()
            .map(|column| self.grades[degree].monomials[*column].clone())
            .collect()
    }

    /// Whether every non-basis monomial of a grade reduces to the basis over `Z`.
    ///
    /// This is the certificate that the chosen monomials are a `Z`-basis and not merely a `Q`-basis.
    /// It is reported rather than assumed because the row reduction that produces the expressions is
    /// rational and would happily return halves.
    pub fn monomial_basis_is_integral(&self, degree: usize) -> bool {
        degree <= self.top && self.grades[degree].integral
    }

    /// Which declared column order produced the basis actually kept for a grade.
    pub fn basis_order(&self, degree: usize) -> Option<BasisOrder> {
        (degree <= self.top).then(|| self.grades[degree].order)
    }

    /// The dimension each column order the build actually walked returned for a grade.
    ///
    /// The search stops at the first order that certifies an integral reduction, so this is not an
    /// exhaustive sweep and must not be read as one. Every entry must still agree with
    /// [`ChowRing::dimension`]: the dimension of a quotient is not a property of the elimination
    /// that found it.
    pub fn dimension_by_basis_order(&self, degree: usize) -> Vec<(BasisOrder, usize)> {
        if degree > self.top {
            return Vec::new();
        }
        self.grades[degree].dimension_by_order.clone()
    }

    /// `deg(ω^r)` — the self-intersection of a declared class at the top grade.
    ///
    /// Reported because it explains, as a number, why a coefficient family certified outside the
    /// submodular cone can still fail to be a falsifier: the map `c ↦ Σ c_F x_F` is not injective,
    /// so a family outside the cone may still land on a class inside it.
    pub fn top_self_intersection(&self, class: &Element) -> Result<Rat, ChowError> {
        self.degree_map(&self.power(class, self.top)?)
    }

    pub fn zero(&self, degree: usize) -> Element {
        Element {
            degree,
            coordinates: vec![Rat::zero(); self.dimension(degree)],
        }
    }

    pub fn one(&self) -> Element {
        let mut element = self.zero(0);
        element.coordinates[0] = Rat::one();
        element
    }

    /// `x_F` for the flat at the given index, as a degree-one element.
    pub fn generator(&self, flat: usize) -> Result<Element, ChowError> {
        if flat >= self.flats.len() {
            return Err(ChowError::NoSuchFlat { index: flat });
        }
        let monomial = FlagMonomial::single(flat, 1);
        let column = *self.grades[1]
            .lookup
            .get(&monomial)
            .ok_or(ChowError::FlagMonomialMissing)?;
        Ok(Element {
            degree: 1,
            coordinates: self.grades[1].reduction[column].clone(),
        })
    }

    /// `Σ_F c_F x_F` over the proper flats, in the order [`ChowRing::flats`] returns them.
    pub fn class_from_coefficients(&self, coefficients: &[Rat]) -> Result<Element, ChowError> {
        if coefficients.len() != self.flats.len() {
            return Err(ChowError::CoefficientShape {
                found: coefficients.len(),
                expected: self.flats.len(),
            });
        }
        let mut element = self.zero(1);
        for (flat, coefficient) in coefficients.iter().enumerate() {
            if coefficient.is_zero() {
                continue;
            }
            let generator = self.generator(flat)?;
            for (slot, entry) in generator.coordinates.iter().enumerate() {
                element.coordinates[slot] += coefficient.clone() * entry.clone();
            }
        }
        Ok(element)
    }

    /// The coefficients a set function assigns to the proper flats.
    pub fn coefficients_from_set_function(&self, value: impl Fn(Subset) -> i64) -> Vec<Rat> {
        self.flats.iter().map(|flat| rational(value(*flat))).collect()
    }

    /// `c(S) = |S| · (|E| − |S|)`, strictly submodular, hence an ample class.
    ///
    /// `|S|(n−|S|)` is `h(|S|)` for a strictly concave `h` with `h(0) = h(n) = 0`, and a strictly
    /// concave function of cardinality is strictly submodular on incomparable pairs.
    pub fn ample_coefficients(&self) -> Vec<Rat> {
        let ground = self.matroid.ground() as i64;
        self.coefficients_from_set_function(|flat| {
            let size = flat.count_ones() as i64;
            size * (ground - size)
        })
    }

    /// Where a declared coefficient family sits relative to the ample cone.
    ///
    /// Strict submodularity over **all** subsets of the ground set is the sufficient condition AHK
    /// give for `Σ c_F x_F` to be ample. The verdict is computed over every incomparable pair, so a
    /// falsifier is *certified* to be outside the cone before it is used as one.
    pub fn submodularity_verdict(&self, value: impl Fn(Subset) -> i64) -> SubmodularVerdict {
        let extent = (1 as Subset) << self.matroid.ground();
        let mut modular_witness: Option<(Subset, Subset)> = None;
        for left in 0..extent {
            for right in left..extent {
                if left & !right == 0 || right & !left == 0 {
                    continue;
                }
                let slack =
                    value(left) + value(right) - value(left | right) - value(left & right);
                if slack < 0 {
                    return SubmodularVerdict::Violated {
                        left,
                        right,
                        deficit: slack,
                    };
                }
                if slack == 0 && modular_witness.is_none() {
                    modular_witness = Some((left, right));
                }
            }
        }
        match modular_witness {
            None => SubmodularVerdict::StrictlySubmodular,
            Some((left, right)) => SubmodularVerdict::ModularSomewhere { left, right },
        }
    }

    fn reduce(&self, degree: usize, column: usize) -> &[Rat] {
        &self.grades[degree].reduction[column]
    }

    /// The ring product. A product whose grade exceeds the top is the zero element of a zero space,
    /// which is `A^k(M) = 0` for `k > r` and is checked by
    /// [`ChowRing::dimension_above_the_top`] rather than assumed.
    pub fn multiply(&self, left: &Element, right: &Element) -> Result<Element, ChowError> {
        let degree = left.degree + right.degree;
        if degree > self.top {
            return Ok(Element {
                degree,
                coordinates: Vec::new(),
            });
        }
        let mut coordinates = vec![Rat::zero(); self.dimension(degree)];
        for (position, coefficient) in left.coordinates.iter().enumerate() {
            if coefficient.is_zero() {
                continue;
            }
            let left_monomial =
                &self.grades[left.degree].monomials[self.grades[left.degree].basis[position]];
            for (other, factor) in right.coordinates.iter().enumerate() {
                if factor.is_zero() {
                    continue;
                }
                let right_monomial =
                    &self.grades[right.degree].monomials[self.grades[right.degree].basis[other]];
                let Some(product) = left_monomial.times(right_monomial, &self.comparable) else {
                    continue;
                };
                let column = *self.grades[degree]
                    .lookup
                    .get(&product)
                    .ok_or(ChowError::FlagMonomialMissing)?;
                let scale = coefficient.clone() * factor.clone();
                for (slot, entry) in self.reduce(degree, column).iter().enumerate() {
                    if entry.is_zero() {
                        continue;
                    }
                    coordinates[slot] += scale.clone() * entry.clone();
                }
            }
        }
        Ok(Element {
            degree,
            coordinates,
        })
    }

    pub fn power(&self, element: &Element, exponent: usize) -> Result<Element, ChowError> {
        let mut accumulated = self.one();
        for _ in 0..exponent {
            accumulated = self.multiply(&accumulated, element)?;
        }
        Ok(accumulated)
    }

    /// `deg : A^r(M) → Q`, normalised so that every complete flag of flats has degree one.
    pub fn degree_map(&self, element: &Element) -> Result<Rat, ChowError> {
        if element.degree != self.top {
            return Err(ChowError::DegreeMismatch {
                expected: self.top,
                found: element.degree,
            });
        }
        Ok(element.coordinates[0].clone() * self.top_basis_degree.clone())
    }

    /// Rebuild one grade from nothing, through the same builder the ring was constructed with, and
    /// return what went in and what came out.
    ///
    /// **This exists so that "the ring stops at its top grade" is a claim rather than a tautology.**
    /// `rebuild_grade(r+1).dimension == 0` asserted alone could not have come out otherwise — a
    /// mutation replacing the routine's returned dimension with a literal `0` survived the suite,
    /// twice, until this became general. The same routine is therefore required to return `1` at
    /// the top grade and the ray count at degree one, on the same fixtures, in the same test. A law
    /// that returns zero proves nothing about itself; this one is made to return non-zero on
    /// declared material before its zero is believed.
    ///
    /// The census fields are the second half of the same discipline: the material must be shown to
    /// have existed before it can be said to have vanished, and they must match
    /// [`chain_monomial_census`], which counts by a different route.
    pub fn rebuild_grade(&self, degree: usize) -> GradeCensus {
        let containment = strict_containment(&self.flats);
        let chains = enumerate_chains(&containment, self.top);
        let mut previous: Option<Grade> = None;
        for step in 0..=degree {
            let grade = build_grade(
                &self.flats,
                &self.comparable,
                &chains,
                self.matroid.ground(),
                step,
                previous.as_ref(),
            );
            previous = Some(grade);
        }
        let grade = previous.expect("grade zero is always built");
        GradeCensus {
            degree,
            monomials: grade.monomials.len(),
            relation_rows: grade.relation_rows,
            dimension: grade.dimension(),
        }
    }

    /// The grade one above the top. Its dimension must be zero — see [`ChowRing::rebuild_grade`]
    /// for why that alone is not evidence and what is asserted alongside it.
    pub fn grade_above_the_top(&self) -> GradeCensus {
        self.rebuild_grade(self.top + 1)
    }

    /// The matrix of `ω^power : A^source → A^{source+power}` in the chosen monomial bases.
    pub fn multiplication_matrix(
        &self,
        class: &Element,
        power: usize,
        source: usize,
    ) -> Result<Vec<Vec<Rat>>, ChowError> {
        let raised = self.power(class, power)?;
        let target = source + power;
        let rows = self.dimension(target);
        let mut matrix = vec![vec![Rat::zero(); self.dimension(source)]; rows];
        for column in 0..self.dimension(source) {
            let mut probe = self.zero(source);
            probe.coordinates[column] = Rat::one();
            let image = self.multiply(&raised, &probe)?;
            for row in 0..rows {
                matrix[row][column] = image.coordinates[row].clone();
            }
        }
        Ok(matrix)
    }

    /// `deg(ω^{r−2k} · a · b)` on all of `A^k`, as a symmetric form.
    pub fn ambient_form(&self, class: &Element, degree: usize) -> Result<SymmetricForm, ChowError> {
        let extent = self.dimension(degree);
        let power = self
            .top
            .checked_sub(2 * degree)
            .ok_or(ChowError::DegreeAboveTheMiddle { degree, top: self.top })?;
        let raised = self.power(class, power)?;
        let mut carried: Vec<Element> = Vec::with_capacity(extent);
        for column in 0..extent {
            let mut probe = self.zero(degree);
            probe.coordinates[column] = Rat::one();
            carried.push(self.multiply(&raised, &probe)?);
        }
        let mut rows = vec![vec![Rat::zero(); extent]; extent];
        for (row, left) in carried.iter().enumerate() {
            for column in row..extent {
                let mut probe = self.zero(degree);
                probe.coordinates[column] = Rat::one();
                let value = self.degree_map(&self.multiply(left, &probe)?)?;
                rows[row][column] = value.clone();
                rows[column][row] = value;
            }
        }
        Ok(SymmetricForm::from_rows(rows)?)
    }

    /// The Poincaré pairing `deg(x_F · x_G)` on the **generators**, not on a basis.
    ///
    /// A spanning set rather than a basis is deliberate: comparing the full generator Gram matrix
    /// against an independent model is a stronger check than comparing it on a basis, because a
    /// wrong choice of basis cannot hide in it.
    pub fn generator_pairing(&self) -> Result<SymmetricForm, ChowError> {
        if self.top != 2 {
            return Err(ChowError::TopIsNotTwo { top: self.top });
        }
        let extent = self.flats.len();
        let mut rows = vec![vec![Rat::zero(); extent]; extent];
        for left in 0..extent {
            let a = self.generator(left)?;
            for right in left..extent {
                let b = self.generator(right)?;
                let value = self.degree_map(&self.multiply(&a, &b)?)?;
                rows[left][right] = value.clone();
                rows[right][left] = value;
            }
        }
        Ok(SymmetricForm::from_rows(rows)?)
    }

    /// Hand this ring's generator pairing to the organ that names windings, and return what it says.
    ///
    /// [`crate::winding_inertia`] declines to count signs: where a form's inertia factors through a
    /// character group, every direction has a **name** — how far it winds — and the lawful return is
    /// the windings rather than a tally of negatives. The condition for that is a cyclic group acting
    /// on the generators and preserving the pairing, and this asks the material whether one does.
    ///
    /// **The flat order is a receiver coordinate, not a property of the matroid.**
    /// [`Matroid::flats`] sorts by rank and then by bitmask, which is a reading convention; the
    /// pairing is refused as non-circulant in that order for every fixture measured, including the
    /// one for which a cyclic reading exists. Both returns are carried, on
    /// [`crate::winding_inertia::CyclicReceiver::native_refusal`].
    ///
    /// **What refuses, and why it is a theorem rather than a limit of this code.** A circulant
    /// carries `c_0` at every diagonal entry, so a cyclic reading needs `deg(x_F²)` constant over the
    /// flats. On a simple rank-three matroid `deg(x_L²) = −1` for a rank-two flat `L`, and
    /// `deg(x_p²) = 1 − |{lines through p}|` for a point, so a constant diagonal forces every point
    /// onto exactly two lines. Fix such a point `p` with lines `L₁, L₂`; the lines through `p`
    /// partition `E ∖ {p}`, and a point `q ∈ L₁ ∖ {p}` then lies on `L₁` together with one line to
    /// each point of `L₂ ∖ {p}`, so `q` is on `|L₂|` lines. Constancy forces `|L₂| = 2`, symmetrically
    /// `|L₁| = 2`, and `|E| = |L₁ ∪ L₂| = 3`. **`U(3,3)` is the only simple rank-three matroid whose
    /// generator pairing a character group can see**, and every other one is refused at the diagonal
    /// with [`crate::winding_inertia::WindingError::DiagonalIsNotConstant`] naming the flat.
    ///
    /// `walk_aperture` is the caller's declaration, and its exhaustion is reported as an exhausted
    /// allowance rather than as an absence.
    pub fn cyclic_generator_receiver(
        &self,
        walk_aperture: u64,
    ) -> Result<CyclicReceiver, ChowError> {
        let pairing = self.generator_pairing()?;
        Ok(cyclic_receiver_of_form(&pairing, walk_aperture)?)
    }

    /// The intersection form of a blown-up projective plane, read off the matroid alone.
    ///
    /// For a simple rank-three matroid the map `x_{{i}} ↦ H − Σ_{G ∋ i} E_G`, `x_G ↦ E_G` on the
    /// rank-two flats `G` sends the Chow ring's generators into the lattice
    /// `⟨H, E_G⟩` with `H² = 1`, `E_G² = −1`, `H·E_G = 0` — the Picard lattice of `ℙ²` blown up at
    /// one point per rank-two flat. For a matroid realised by a complex line arrangement that is a
    /// theorem about a surface; for `F_7` and the non-Pappus matroid there is no such surface and
    /// this is a prediction. Either way it is computed from the flats and compared against
    /// [`ChowRing::generator_pairing`], which is computed from the ring.
    pub fn blowup_lattice_pairing(&self) -> Result<SymmetricForm, ChowError> {
        if self.top != 2 {
            return Err(ChowError::TopIsNotTwo { top: self.top });
        }
        let extent = self.flats.len();
        let rank_of = |flat: Subset| self.matroid.rank_of(flat);
        let mut rows = vec![vec![Rat::zero(); extent]; extent];
        for left in 0..extent {
            for right in 0..extent {
                let (a, b) = (self.flats[left], self.flats[right]);
                let value = match (rank_of(a), rank_of(b)) {
                    (2, 2) => {
                        if a == b {
                            -1
                        } else {
                            0
                        }
                    }
                    (1, 2) => i64::from(a & !b == 0),
                    (2, 1) => i64::from(b & !a == 0),
                    _ => {
                        if a == b {
                            1 - self
                                .flats
                                .iter()
                                .filter(|flat| rank_of(**flat) == 2 && a & !**flat == 0)
                                .count() as i64
                        } else {
                            let shared = self
                                .flats
                                .iter()
                                .filter(|flat| {
                                    rank_of(**flat) == 2 && a & !**flat == 0 && b & !**flat == 0
                                })
                                .count() as i64;
                            1 - shared
                        }
                    }
                };
                rows[left][right] = rational(value);
            }
        }
        Ok(SymmetricForm::from_rows(rows)?)
    }

    /// `μ^k = deg(α^{r−k} β^k)` computed inside the ring, where `α = Σ_{F ∋ i} x_F` and
    /// `β = Σ_{F ∌ i} x_F` for the first ground element `i`.
    ///
    /// AHK identify these with the unsigned coefficients of the reduced characteristic polynomial.
    /// [`Matroid::reduced_characteristic_magnitudes`] computes the same numbers from the Möbius
    /// function of the lattice of flats and never touches the ring, which makes the comparison two
    /// frames on one construction.
    pub fn ring_characteristic_magnitudes(&self) -> Result<Vec<Rat>, ChowError> {
        let alpha = self.class_from_coefficients(
            &self
                .flats
                .iter()
                .map(|flat| rational(i64::from(flat & 1 != 0)))
                .collect::<Vec<Rat>>(),
        )?;
        let beta = self.class_from_coefficients(
            &self
                .flats
                .iter()
                .map(|flat| rational(i64::from(flat & 1 == 0)))
                .collect::<Vec<Rat>>(),
        )?;
        (0..=self.top)
            .map(|k| {
                let left = self.power(&alpha, self.top - k)?;
                let right = self.power(&beta, k)?;
                self.degree_map(&self.multiply(&left, &right)?)
            })
            .collect()
    }

    /// The hard Lefschetz and Hodge–Riemann returns at one degree, for one declared class.
    pub fn lefschetz_report(
        &self,
        class: &Element,
        degree: usize,
    ) -> Result<LefschetzReport, ChowError> {
        if 2 * degree > self.top {
            return Err(ChowError::DegreeAboveTheMiddle {
                degree,
                top: self.top,
            });
        }
        let ambient_dimension = self.dimension(degree);
        let lefschetz = self.multiplication_matrix(class, self.top - 2 * degree, degree)?;
        let lefschetz_rank = rational_rank(&lefschetz, ambient_dimension);
        let target_dimension = self.dimension(self.top - degree);
        let lefschetz_invariant_factors = integral_smith_factors(&lefschetz, ambient_dimension);

        let raising = self.multiplication_matrix(class, self.top - 2 * degree + 1, degree)?;
        let primitive = null_space(&raising, ambient_dimension);
        let primitive_dimension = primitive.len();

        let ambient_form = self.ambient_form(class, degree)?;
        let ambient_split = inertia(&ambient_form);

        // Restrict to the primitive part and apply the declared hand.
        let hand: i64 = if degree.is_multiple_of(2) { 1 } else { -1 };
        let mut rows = vec![vec![Rat::zero(); primitive_dimension]; primitive_dimension];
        for (row, left) in primitive.iter().enumerate() {
            for (column, right) in primitive.iter().enumerate() {
                let mut total = Rat::zero();
                for (i, a) in left.iter().enumerate() {
                    if a.is_zero() {
                        continue;
                    }
                    for (j, b) in right.iter().enumerate() {
                        if b.is_zero() {
                            continue;
                        }
                        total += a.clone() * b.clone() * ambient_form.at(i, j).clone();
                    }
                }
                rows[row][column] = rational(hand) * total;
            }
        }
        let primitive_form = SymmetricForm::from_rows(rows)?;
        let primitive_split = inertia(&primitive_form);

        // The Lefschetz decomposition A^k = ⊕_{j≤k} ω^{k−j} P^j predicts the ambient split.
        let mut predicted = Inertia::default();
        for lower in 0..=degree {
            let raising = self.multiplication_matrix(class, self.top - 2 * lower + 1, lower)?;
            let lower_primitive = null_space(&raising, self.dimension(lower)).len();
            if lower % 2 == 0 {
                predicted.positive += lower_primitive;
            } else {
                predicted.negative += lower_primitive;
            }
        }

        Ok(LefschetzReport {
            degree,
            top: self.top,
            hand,
            ambient_dimension,
            target_dimension,
            lefschetz_rank,
            lefschetz_is_isomorphism: lefschetz_rank == ambient_dimension
                && ambient_dimension == target_dimension,
            lefschetz_invariant_factors,
            primitive_dimension,
            primitive_form,
            primitive_split,
            hodge_riemann_holds: primitive_dimension > 0
                && primitive_split
                    == Inertia {
                        positive: primitive_dimension,
                        zero: 0,
                        negative: 0,
                    },
            ambient_form,
            ambient_split,
            predicted_ambient_split: predicted,
        })
    }

    /// Every degree at or below the middle, for one declared class.
    pub fn lefschetz_reports(&self, class: &Element) -> Result<Vec<LefschetzReport>, ChowError> {
        (0..=self.top / 2)
            .map(|degree| self.lefschetz_report(class, degree))
            .collect()
    }
}

/// The Smith invariant factors of an integral matrix, or `None` when the matrix is not integral.
///
/// **The pivot rule here is load-bearing, and it is a measured cost and not a preference.**
/// [`crate::rebase_invariants::smith_normal_form`] is a naive Euclidean reduction with a
/// divisibility repair. Its three rules are proved to return the same invariant factors — that is
/// its own `the_invariants_do_not_depend_on_the_pivot_rule` — but they do **not** cost the same. On
/// the `11x11` Lefschetz matrix of the Boolean matroid `B_4` under a supermodular class, measured
/// 2026-08-08:
///
/// | rule | returned |
/// |---|---|
/// | [`PivotRule::SmallestMagnitude`] | rank 11 in 396 µs |
/// | [`PivotRule::FirstNonzero`] | did not return in eight minutes |
///
/// The intermediate coefficients explode under a rule that ignores magnitude, which is exactly what
/// that rule's own doc comment warns it is included to expose. Reporting `FirstNonzero`'s agreement
/// without its cost would be the defect `CLAUDE.md` §8 names: *reproducing what an owner returns
/// without reproducing what it costs is not porting it.*
fn integral_smith_factors(matrix: &[Vec<Rat>], columns: usize) -> Option<Vec<BigInt>> {
    if matrix.iter().any(|row| row.iter().any(|e| !e.is_integer())) {
        return None;
    }
    let mut integral = IntegerMatrix::zeros(matrix.len(), columns);
    for (row, entries) in matrix.iter().enumerate() {
        for (column, entry) in entries.iter().enumerate() {
            integral.set(row, column, entry.to_integer());
        }
    }
    Some(smith_normal_form(&integral, PivotRule::SmallestMagnitude).factors)
}

/// One elimination under one declared column order: the chosen monomial basis, the exact expression
/// of every other monomial in it, and whether that expression came out over `Z`.
fn reduce_to_basis(
    rows: &[Vec<Rat>],
    monomials: &[FlagMonomial],
    columns: usize,
    order: BasisOrder,
) -> (Vec<usize>, Vec<Vec<Rat>>, bool) {
    let mut working = rows.to_vec();
    let sequence = order.sequence(monomials);
    let pivots = row_reduce_ordered(&mut working, columns, &sequence);
    let mut is_pivot = vec![false; columns];
    for pivot in &pivots {
        is_pivot[*pivot] = true;
    }
    let basis: Vec<usize> = (0..columns).filter(|column| !is_pivot[*column]).collect();

    let mut reduction = vec![vec![Rat::zero(); basis.len()]; columns];
    for (slot, column) in basis.iter().enumerate() {
        reduction[*column][slot] = Rat::one();
    }
    for (index, pivot) in pivots.iter().enumerate() {
        for (slot, column) in basis.iter().enumerate() {
            reduction[*pivot][slot] = -working[index][*column].clone();
        }
    }
    let integral = reduction
        .iter()
        .all(|row| row.iter().all(num_rational::BigRational::is_integer));
    (basis, reduction, integral)
}

fn build_grade(
    flats: &[Subset],
    comparable: &[Vec<bool>],
    chains: &[Vec<usize>],
    ground: usize,
    degree: usize,
    previous: Option<&Grade>,
) -> Grade {
    build_grade_with(
        flats,
        comparable,
        chains,
        ground,
        degree,
        previous,
        &BasisOrder::ALL,
    )
}

fn build_grade_with(
    flats: &[Subset],
    comparable: &[Vec<bool>],
    chains: &[Vec<usize>],
    ground: usize,
    degree: usize,
    previous: Option<&Grade>,
    orders: &[BasisOrder],
) -> Grade {
    let mut monomials: Vec<FlagMonomial> = if degree == 0 {
        vec![FlagMonomial::unit()]
    } else {
        let mut collected = Vec::new();
        for chain in chains {
            if chain.len() > degree {
                continue;
            }
            for composition in compositions(degree, chain.len()) {
                collected.push(FlagMonomial {
                    factors: chain
                        .iter()
                        .copied()
                        .zip(composition.into_iter())
                        .collect(),
                });
            }
        }
        collected
    };
    monomials.sort();
    monomials.dedup();
    let lookup: BTreeMap<FlagMonomial, usize> = monomials
        .iter()
        .cloned()
        .enumerate()
        .map(|(index, monomial)| (monomial, index))
        .collect();

    let mut rows: Vec<Vec<Rat>> = Vec::new();
    if let Some(previous) = previous {
        for carrier in &previous.monomials {
            for element in 1..ground {
                let mut row = vec![Rat::zero(); monomials.len()];
                let mut touched = false;
                for (index, flat) in flats.iter().enumerate() {
                    let holds_element = flat & (1 << element) != 0;
                    let holds_base = flat & 1 != 0;
                    if holds_element == holds_base {
                        continue;
                    }
                    let Some(product) = carrier.times_generator(index, comparable) else {
                        continue;
                    };
                    let Some(column) = lookup.get(&product) else {
                        continue;
                    };
                    if holds_element {
                        row[*column] += Rat::one();
                    } else {
                        row[*column] -= Rat::one();
                    }
                    touched = true;
                }
                if touched && row.iter().any(|entry| !entry.is_zero()) {
                    rows.push(row);
                }
            }
        }
    }
    let relation_rows = rows.len();
    let columns = monomials.len();

    // The orders are tried **lazily**, stopping at the first that certifies an integral reduction.
    // That is a cost decision and it is visible: `dimension_by_order` records only the orders
    // actually walked, so a reader can never mistake it for an exhaustive independence check. The
    // exhaustive one is `the_dimension_does_not_depend_on_the_basis_order`, which runs the full
    // sweep on small fixtures where the intermediate rationals stay small.
    let mut dimension_by_order = Vec::with_capacity(orders.len());
    let mut kept: Option<(BasisOrder, Vec<usize>, Vec<Vec<Rat>>)> = None;
    let mut fallback: Option<(BasisOrder, Vec<usize>, Vec<Vec<Rat>>)> = None;
    for order in orders.iter().copied() {
        let (basis, reduction, integral) =
            reduce_to_basis(&rows, &monomials, columns, order);
        dimension_by_order.push((order, basis.len()));
        if integral {
            kept = Some((order, basis, reduction));
            break;
        }
        if fallback.is_none() {
            fallback = Some((order, basis, reduction));
        }
    }

    let integral = kept.is_some();
    let (order, basis, reduction) = kept
        .or(fallback)
        .expect("at least one basis order is always tried");

    Grade {
        monomials,
        lookup,
        basis,
        reduction,
        integral,
        order,
        dimension_by_order,
        relation_rows,
    }
}

// -------------------------------------------------------------------------------------------
// what is returned

/// What one grade was built from, and what survived.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GradeCensus {
    pub degree: usize,
    pub monomials: usize,
    pub relation_rows: usize,
    pub dimension: usize,
}

/// Where a declared coefficient family sits relative to the ample cone.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SubmodularVerdict {
    /// Strict on every incomparable pair. Ample, and the theorems are stated for this case.
    StrictlySubmodular,
    /// Submodular but with equality somewhere. On the boundary of the cone, not inside it.
    ModularSomewhere { left: Subset, right: Subset },
    /// Outside the cone, with the pair that shows it.
    Violated {
        left: Subset,
        right: Subset,
        deficit: i64,
    },
}

impl SubmodularVerdict {
    pub const fn is_ample(&self) -> bool {
        matches!(self, Self::StrictlySubmodular)
    }
}

/// The hard Lefschetz and Hodge–Riemann returns at one degree.
///
/// The **split** and the **hand** are separate fields. `primitive_split` is what no change of basis
/// moves; `hand` is the declared `(−1)^k` that decides which cone is being called the returning one.
/// Neither on its own is the claim.
#[derive(Clone, Debug)]
pub struct LefschetzReport {
    pub degree: usize,
    /// The ring's top grade `r`, carried so a reader of one report can name the target grade
    /// `A^{r−k}` without holding the ring.
    pub top: usize,
    pub hand: i64,
    pub ambient_dimension: usize,
    pub target_dimension: usize,
    pub lefschetz_rank: usize,
    pub lefschetz_is_isomorphism: bool,
    /// The Smith invariant factors of `ω^{r−2k}`, when its matrix came out integral. Hard Lefschetz
    /// is a rational statement; these say what it does over `Z`, which is strictly more.
    pub lefschetz_invariant_factors: Option<Vec<BigInt>>,
    pub primitive_dimension: usize,
    pub primitive_form: SymmetricForm,
    pub primitive_split: Inertia,
    pub hodge_riemann_holds: bool,
    pub ambient_form: SymmetricForm,
    pub ambient_split: Inertia,
    /// The split the Lefschetz decomposition predicts for `ambient_form`, computed from the
    /// primitive dimensions alone.
    pub predicted_ambient_split: Inertia,
}

impl LefschetzReport {
    pub fn ambient_split_matches_decomposition(&self) -> bool {
        self.ambient_split == self.predicted_ambient_split
    }
}

#[derive(Clone, Debug, Error)]
pub enum ChowError {
    #[error(transparent)]
    Matroid(#[from] MatroidError),
    #[error("rank {rank} is outside the declared aperture of {aperture}")]
    RankOutsideAperture { rank: usize, aperture: usize },
    #[error("a matroid of rank {rank} has no proper nonempty flat, hence no generator and no class")]
    NoProperFlats { rank: usize },
    #[error("the top grade must be free of rank one; this one has dimension {dimension}")]
    TopGradeNotOneDimensional { dimension: usize },
    #[error("a flag monomial was absent from its own grade's spanning set")]
    FlagMonomialMissing,
    #[error("the degree map is not well defined: one flag gives {first}, another {second}")]
    DegreeMapInconsistent { first: String, second: String },
    #[error("no complete flag of proper flats was found")]
    NoCompleteFlag,
    #[error("a complete flag reduced to zero; the degree map would be degenerate")]
    DegenerateDegreeMap,
    #[error("flat index {index} is out of range")]
    NoSuchFlat { index: usize },
    #[error("a class needs one coefficient per proper flat: {expected} expected, {found} supplied")]
    CoefficientShape { found: usize, expected: usize },
    #[error("the degree map is defined on grade {expected}; grade {found} was supplied")]
    DegreeMismatch { expected: usize, found: usize },
    #[error("Hodge–Riemann is stated for 2k ≤ r; degree {degree} is above the middle of {top}")]
    DegreeAboveTheMiddle { degree: usize, top: usize },
    #[error("this reading is stated for a top grade of two; this ring's is {top}")]
    TopIsNotTwo { top: usize },
    #[error(transparent)]
    Inertia(#[from] InertiaError),
    #[error(transparent)]
    Winding(#[from] WindingError),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::inertia::{PivotOrder, inertia_with_order};

    fn fano() -> Matroid {
        Matroid::rank_three_from_lines(
            "Fano F7",
            7,
            &[
                &[0, 1, 2],
                &[0, 3, 4],
                &[0, 5, 6],
                &[1, 3, 5],
                &[1, 4, 6],
                &[2, 3, 6],
                &[2, 4, 5],
            ],
        )
        .expect("the Fano plane is a matroid")
    }

    fn non_pappus() -> Matroid {
        // Pappus: points 0,1,2 on one line, 3,4,5 on another, and the nine cross joins meeting in
        // 6,7,8. Pappus's theorem forces 6,7,8 collinear over every field; the non-Pappus matroid is
        // the one that declares them not to be, and it is representable over no field.
        Matroid::rank_three_from_lines(
            "non-Pappus",
            9,
            &[
                &[0, 1, 2],
                &[3, 4, 5],
                &[0, 4, 8],
                &[0, 5, 7],
                &[1, 3, 8],
                &[1, 5, 6],
                &[2, 3, 7],
                &[2, 4, 6],
            ],
        )
        .expect("the non-Pappus configuration is a matroid")
    }

    fn complete_graph_on_four() -> Matroid {
        Matroid::graphic(
            "M(K4)",
            4,
            &[(0, 1), (0, 2), (0, 3), (1, 2), (1, 3), (2, 3)],
        )
        .expect("a graph gives a matroid")
    }

    fn fixtures() -> Vec<Matroid> {
        vec![
            Matroid::uniform(2, 3).expect("U(2,3)"),
            Matroid::uniform(3, 3).expect("U(3,3)"),
            Matroid::uniform(3, 4).expect("U(3,4)"),
            complete_graph_on_four(),
            fano(),
            non_pappus(),
            Matroid::uniform(4, 4).expect("U(4,4)"),
        ]
    }

    fn supermodular(ring: &ChowRing) -> Vec<Rat> {
        ring.coefficients_from_set_function(|flat| {
            let size = flat.count_ones() as i64;
            size * size
        })
    }

    fn modular(ring: &ChowRing) -> Vec<Rat> {
        ring.coefficients_from_set_function(|flat| flat.count_ones() as i64)
    }

    // ---- the degenerate refusals ----

    #[test]
    fn a_loop_is_refused_by_type() {
        let ground = 2;
        // Element 1 is a loop: adding it never raises the rank.
        let ranks: Vec<u32> = (0..1usize << ground)
            .map(|subset| u32::from(subset & 1 != 0))
            .collect();
        assert_eq!(
            Matroid::from_rank_table("looped", ground, ranks),
            Err(MatroidError::Loop { element: 1 })
        );
    }

    #[test]
    fn parallel_elements_are_refused_by_type() {
        let ground = 2;
        let ranks: Vec<u32> = (0..1usize << ground)
            .map(|subset| u32::from(subset != 0))
            .collect();
        assert_eq!(
            Matroid::from_rank_table("parallel", ground, ranks),
            Err(MatroidError::ParallelPair { left: 0, right: 1 })
        );
    }

    #[test]
    fn rank_zero_is_refused_by_type() {
        let ground = 3;
        let ranks = vec![0u32; 1usize << ground];
        assert_eq!(
            Matroid::from_rank_table("empty", ground, ranks),
            Err(MatroidError::RankZero)
        );
    }

    #[test]
    fn a_set_function_that_is_not_submodular_is_refused_by_that_name() {
        // `r(S) = min(|S|, 2)` on four elements, except `r(E) = 3`. Every other audit passes it:
        // `r(∅) = 0`, rank grows by zero or one at every single step, no singleton has rank zero,
        // no pair has rank one. Only submodularity fails, at `({0,1,2}, {0,1,3})`:
        //
        //   r({0,1,2}) + r({0,1,3}) = 2 + 2 = 4   <   r(E) + r({0,1}) = 3 + 2 = 5.
        //
        // The fixture is built this way on purpose. An earlier version was caught by the *parallel*
        // branch, which meant the submodularity branch was never proved to fire — and a mutation
        // that deleted the submodularity audit outright survived the suite.
        let ground = 4;
        let full = (1usize << ground) - 1;
        let ranks: Vec<u32> = (0..1usize << ground)
            .map(|subset| {
                if subset == full {
                    3
                } else {
                    (subset.count_ones()).min(2)
                }
            })
            .collect();
        let refusal = Matroid::from_rank_table("not submodular", ground, ranks)
            .expect_err("this rank function is not a matroid");
        assert!(
            matches!(refusal, MatroidError::NotSubmodular { .. }),
            "the audit named {refusal} instead of submodularity"
        );
    }

    #[test]
    fn a_rank_that_jumps_by_two_is_refused_by_that_name() {
        let ground = 3;
        let ranks: Vec<u32> = (0..1usize << ground)
            .map(|subset| if subset == 0 { 0 } else { 2 })
            .collect();
        let refusal = Matroid::from_rank_table("jumping", ground, ranks)
            .expect_err("rank must grow by zero or one");
        assert!(
            matches!(refusal, MatroidError::NotUnitIncrease { .. }),
            "the audit named {refusal} instead of unit increase"
        );
    }

    #[test]
    fn a_rank_one_matroid_has_no_chow_ring_and_says_so() {
        let matroid = Matroid::uniform(1, 1).expect("U(1,1)");
        let refusal = ChowRing::new(matroid).expect_err("rank one has no proper flat");
        assert!(matches!(refusal, ChowError::NoProperFlats { rank: 1 }));
    }

    #[test]
    fn a_rank_above_the_aperture_is_refused_by_name() {
        let matroid = Matroid::uniform(5, 6).expect("U(5,6)");
        let refusal = ChowRing::new(matroid).expect_err("rank five is outside the aperture");
        assert!(matches!(
            refusal,
            ChowError::RankOutsideAperture {
                rank: 5,
                aperture: RANK_APERTURE
            }
        ));
    }

    // ---- the combinatorics ----

    #[test]
    fn the_flat_counts_are_the_hand_counts() {
        assert_eq!(Matroid::uniform(2, 3).unwrap().proper_flats().len(), 3);
        assert_eq!(Matroid::uniform(3, 3).unwrap().proper_flats().len(), 6);
        assert_eq!(Matroid::uniform(3, 4).unwrap().proper_flats().len(), 10);
        assert_eq!(complete_graph_on_four().proper_flats().len(), 13);
        assert_eq!(fano().proper_flats().len(), 14);
        assert_eq!(non_pappus().proper_flats().len(), 29);
        assert_eq!(Matroid::uniform(4, 4).unwrap().proper_flats().len(), 14);
        assert_eq!(Matroid::vamos().unwrap().proper_flats().len(), 77);
    }

    #[test]
    fn the_degree_one_dimension_is_the_ray_count_less_the_ambient_dimension() {
        for matroid in fixtures() {
            let expected = matroid.proper_flats().len() + 1 - matroid.ground();
            let ring = ChowRing::new(matroid).expect("the ring builds");
            assert_eq!(
                ring.dimension(1),
                expected,
                "{} has dim A^1 = {}",
                ring.matroid().name(),
                ring.dimension(1)
            );
        }
    }

    #[test]
    fn the_boolean_matroid_carries_the_eulerian_numbers() {
        // The Bergman fan of a Boolean matroid is the permutohedral fan, whose Betti numbers are the
        // Eulerian numbers. This is an external check on the whole grade construction.
        let three = ChowRing::new(Matroid::uniform(3, 3).unwrap()).expect("B3");
        assert_eq!(three.dimensions(), vec![1, 4, 1]);
        let four = ChowRing::new(Matroid::uniform(4, 4).unwrap()).expect("B4");
        assert_eq!(four.dimensions(), vec![1, 11, 11, 1]);
    }

    #[test]
    fn poincare_duality_holds_on_every_fixture() {
        for matroid in fixtures() {
            let ring = ChowRing::new(matroid).expect("the ring builds");
            let dimensions = ring.dimensions();
            for (degree, dimension) in dimensions.iter().enumerate() {
                assert_eq!(
                    *dimension,
                    dimensions[ring.top() - degree],
                    "{} fails Poincaré duality at degree {degree}",
                    ring.matroid().name()
                );
            }
        }
    }

    #[test]
    fn the_top_grade_is_one_dimensional_and_every_complete_flag_has_degree_one() {
        for matroid in fixtures() {
            let ring = ChowRing::new(matroid).expect("the ring builds");
            assert_eq!(ring.dimension(ring.top()), 1);
            assert!(ring.complete_flag_count() > 0);
            // `ChowRing::new` refuses a disagreement outright, so reaching here is the assertion;
            // re-derive one flag's degree to make the claim explicit rather than implicit.
            let flats = ring.flats().to_vec();
            let mut flag = ring.one();
            for step in 1..=ring.top() {
                let index = flats
                    .iter()
                    .position(|flat| ring.matroid().rank_of(*flat) == step)
                    .expect("a flat of every rank exists");
                flag = ring.multiply(&flag, &ring.generator(index).unwrap()).unwrap();
            }
            // The flag just built is a chain only if each chosen flat contains the previous one;
            // when it is not, the product is zero and the degree is zero. Accept either, but a
            // genuinely complete flag must return one.
            let value = ring.degree_map(&flag).unwrap();
            assert!(
                value == Rat::zero() || value == Rat::one(),
                "{} returned {value} on a flag product",
                ring.matroid().name()
            );
        }
    }

    #[test]
    fn the_grade_above_the_top_vanishes_and_the_same_routine_returns_non_zero_below_it() {
        for matroid in fixtures() {
            let census = chain_monomial_census(&matroid, matroid.rank()).expect("the census runs");
            let rays = matroid.proper_flats().len() + 1 - matroid.ground();
            let ring = ChowRing::new(matroid).expect("the ring builds");
            let name = ring.matroid().name().to_owned();

            // The routine must return non-zero on declared material first, or its zero is a
            // tautology. Degree one and the top grade are the declared controls.
            assert_eq!(
                ring.rebuild_grade(1).dimension,
                rays,
                "{name}: the rebuild routine lost degree one"
            );
            assert_eq!(
                ring.rebuild_grade(ring.top()).dimension,
                1,
                "{name}: the rebuild routine lost the top grade"
            );

            let above = ring.grade_above_the_top();
            assert_eq!(above.degree, ring.top() + 1);
            // And the material must be shown to have existed before it can be said to have vanished.
            assert_eq!(
                (above.monomials, above.relation_rows > 0),
                (census.0, true),
                "{name} did not build the grade above its top"
            );
            assert_eq!(
                above.dimension, 0,
                "{name} carries {} above its top grade",
                above.dimension
            );
        }
    }

    #[test]
    fn the_monomial_basis_is_integral_in_every_grade() {
        for matroid in fixtures() {
            let ring = ChowRing::new(matroid).expect("the ring builds");
            for degree in 0..=ring.top() {
                assert!(
                    ring.monomial_basis_is_integral(degree),
                    "{} grade {degree} reduces over Q but not over Z",
                    ring.matroid().name()
                );
            }
        }
    }

    // ---- the ample cone, certified ----

    #[test]
    fn the_declared_ample_family_is_certified_strictly_submodular() {
        for matroid in fixtures() {
            let ground = matroid.ground() as i64;
            let ring = ChowRing::new(matroid).expect("the ring builds");
            let verdict = ring.submodularity_verdict(|flat| {
                let size = flat.count_ones() as i64;
                size * (ground - size)
            });
            assert_eq!(
                verdict,
                SubmodularVerdict::StrictlySubmodular,
                "{} rejected its own ample family",
                ring.matroid().name()
            );
        }
    }

    #[test]
    fn the_falsifier_family_is_certified_outside_the_cone() {
        for matroid in fixtures() {
            let ring = ChowRing::new(matroid).expect("the ring builds");
            let verdict = ring.submodularity_verdict(|flat| {
                let size = flat.count_ones() as i64;
                size * size
            });
            assert!(
                matches!(verdict, SubmodularVerdict::Violated { .. }),
                "{} did not certify the supermodular family as outside the cone: {verdict:?}",
                ring.matroid().name()
            );
        }
    }

    #[test]
    fn the_modular_family_sits_on_the_boundary_of_the_cone() {
        for matroid in fixtures() {
            let ring = ChowRing::new(matroid).expect("the ring builds");
            let verdict = ring.submodularity_verdict(|flat| flat.count_ones() as i64);
            assert!(
                matches!(verdict, SubmodularVerdict::ModularSomewhere { .. }),
                "{} placed the modular family somewhere other than the boundary: {verdict:?}",
                ring.matroid().name()
            );
        }
    }

    // ---- the theorems ----

    #[test]
    fn hard_lefschetz_holds_for_the_ample_class() {
        for matroid in fixtures() {
            let ring = ChowRing::new(matroid).expect("the ring builds");
            let class = ring
                .class_from_coefficients(&ring.ample_coefficients())
                .unwrap();
            for report in ring.lefschetz_reports(&class).unwrap() {
                assert!(
                    report.lefschetz_is_isomorphism,
                    "{} fails hard Lefschetz at degree {}: rank {} of {}",
                    ring.matroid().name(),
                    report.degree,
                    report.lefschetz_rank,
                    report.ambient_dimension
                );
            }
        }
    }

    #[test]
    fn hodge_riemann_holds_for_the_ample_class() {
        for matroid in fixtures() {
            let ring = ChowRing::new(matroid).expect("the ring builds");
            let class = ring
                .class_from_coefficients(&ring.ample_coefficients())
                .unwrap();
            for report in ring.lefschetz_reports(&class).unwrap() {
                assert_eq!(
                    report.primitive_split,
                    Inertia {
                        positive: report.primitive_dimension,
                        zero: 0,
                        negative: 0
                    },
                    "{} fails Hodge–Riemann at degree {} under hand {}",
                    ring.matroid().name(),
                    report.degree,
                    report.hand
                );
            }
        }
    }

    #[test]
    fn the_lefschetz_decomposition_predicts_the_ambient_split() {
        for matroid in fixtures() {
            let ring = ChowRing::new(matroid).expect("the ring builds");
            let class = ring
                .class_from_coefficients(&ring.ample_coefficients())
                .unwrap();
            for report in ring.lefschetz_reports(&class).unwrap() {
                assert!(
                    report.ambient_split_matches_decomposition(),
                    "{} at degree {}: elimination returned {:?}, the decomposition predicts {:?}",
                    ring.matroid().name(),
                    report.degree,
                    report.ambient_split,
                    report.predicted_ambient_split
                );
            }
        }
    }

    #[test]
    fn the_middle_split_is_the_hodge_index_shape_on_every_rank_three_fixture() {
        for matroid in fixtures() {
            let ring = ChowRing::new(matroid).expect("the ring builds");
            if ring.top() != 2 {
                continue;
            }
            let class = ring
                .class_from_coefficients(&ring.ample_coefficients())
                .unwrap();
            let report = ring.lefschetz_report(&class, 1).unwrap();
            assert_eq!(
                report.ambient_split,
                Inertia {
                    positive: 1,
                    zero: 0,
                    negative: ring.dimension(1) - 1
                },
                "{} does not carry the (1, ρ−1) split",
                ring.matroid().name()
            );
        }
    }

    #[test]
    fn the_split_does_not_depend_on_the_pivot_order() {
        for matroid in fixtures() {
            let ring = ChowRing::new(matroid).expect("the ring builds");
            let class = ring
                .class_from_coefficients(&ring.ample_coefficients())
                .unwrap();
            for report in ring.lefschetz_reports(&class).unwrap() {
                for order in PivotOrder::ALL {
                    assert_eq!(
                        inertia_with_order(&report.primitive_form, order),
                        report.primitive_split,
                        "{} at degree {} moved with the pivot order",
                        ring.matroid().name(),
                        report.degree
                    );
                }
            }
        }
    }

    #[test]
    fn the_smith_rank_of_the_lefschetz_map_agrees_with_the_rational_rank() {
        for matroid in fixtures() {
            let ring = ChowRing::new(matroid).expect("the ring builds");
            let class = ring
                .class_from_coefficients(&ring.ample_coefficients())
                .unwrap();
            for report in ring.lefschetz_reports(&class).unwrap() {
                let factors = report
                    .lefschetz_invariant_factors
                    .as_ref()
                    .expect("the Lefschetz matrix is integral in an integral basis");
                assert_eq!(
                    factors.len(),
                    report.lefschetz_rank,
                    "{} at degree {}: Smith says {} and elimination says {}",
                    ring.matroid().name(),
                    report.degree,
                    factors.len(),
                    report.lefschetz_rank
                );
            }
        }
    }

    // ---- the falsifier ----

    #[test]
    fn the_supermodular_class_breaks_hodge_riemann_wherever_the_top_grade_has_room() {
        for matroid in fixtures() {
            let ring = ChowRing::new(matroid).expect("the ring builds");
            let class = ring.class_from_coefficients(&supermodular(&ring)).unwrap();
            let broke = ring
                .lefschetz_reports(&class)
                .unwrap()
                .into_iter()
                .any(|report| !report.hodge_riemann_holds || !report.lefschetz_is_isomorphism);
            if ring.top() >= 2 {
                assert!(
                    broke,
                    "{} kept Hodge–Riemann under a class certified outside the ample cone",
                    ring.matroid().name()
                );
            } else {
                // r = 1. `A^1` is one-dimensional, so every nonzero class is ample or anti-ample and
                // this one has positive self-intersection. The certificate is on the **coefficient
                // family**, and `c ↦ Σ c_F x_F` has the linear relations in its kernel, so a family
                // outside the cone can still land on a class inside it. That is the finding, and it
                // is why the demand above is conditioned rather than universal.
                assert!(
                    !broke,
                    "{} broke at top grade one, where the class is still ample",
                    ring.matroid().name()
                );
                assert!(
                    ring.top_self_intersection(&class).unwrap() > Rat::zero(),
                    "{} has a supermodular class of non-positive self-intersection",
                    ring.matroid().name()
                );
            }
        }
    }

    #[test]
    fn the_negated_ample_class_breaks_the_odd_top_grade() {
        // For odd r the top-grade hand flips with ω, so deg((−ω)^r) < 0 and the degree-zero
        // Hodge–Riemann form is negative. For even r it does not flip, and this test records that
        // the negation is *not* a falsifier there rather than pretending it is.
        for matroid in fixtures() {
            let ring = ChowRing::new(matroid).expect("the ring builds");
            let negated: Vec<Rat> = ring
                .ample_coefficients()
                .into_iter()
                .map(|coefficient| -coefficient)
                .collect();
            let class = ring.class_from_coefficients(&negated).unwrap();
            let report = ring.lefschetz_report(&class, 0).unwrap();
            if ring.top() % 2 == 1 {
                assert!(
                    !report.hodge_riemann_holds,
                    "{} kept Hodge–Riemann at degree zero under −ω with odd top grade",
                    ring.matroid().name()
                );
            } else {
                assert!(
                    report.hodge_riemann_holds,
                    "{} lost Hodge–Riemann at degree zero under −ω with even top grade",
                    ring.matroid().name()
                );
            }
        }
    }

    #[test]
    fn the_modular_class_survives_a_top_grade_of_two_and_breaks_one_of_three() {
        // `c(S) = |S|` is modular: submodular with equality everywhere, hence exactly on the
        // boundary of the ample cone rather than inside it. The measured behaviour splits by top
        // grade and this test records the split rather than a guess.
        //
        // With `r = 2` the Hodge–Riemann form at `k = 1` is `−deg(a·b)` and `ω` enters only through
        // `P^1 = ω^⊥`. The intersection form on `A^1` has split `(1, 0, ρ−1)` whatever `ω` is, so
        // the theorem survives any class of positive self-intersection — and this one has it.
        //
        // With `r = 3` the form at `k = 1` is `−deg(ω·a·b)`: `ω` is *inside* the form, and a class
        // on the boundary of the cone breaks it.
        for matroid in fixtures() {
            let ring = ChowRing::new(matroid).expect("the ring builds");
            let class = ring.class_from_coefficients(&modular(&ring)).unwrap();
            let broke = ring
                .lefschetz_reports(&class)
                .unwrap()
                .into_iter()
                .any(|report| !report.hodge_riemann_holds || !report.lefschetz_is_isomorphism);
            if ring.top() >= 3 {
                assert!(
                    broke,
                    "{} kept Hodge–Riemann under a boundary class with ω inside the form",
                    ring.matroid().name()
                );
            } else {
                assert!(
                    !broke,
                    "{} broke Hodge–Riemann under a boundary class at top grade {} — that would \
                     be new and belongs in the record",
                    ring.matroid().name(),
                    ring.top()
                );
                assert!(ring.top_self_intersection(&class).unwrap() > Rat::zero());
            }
        }
    }

    #[test]
    fn the_dimension_does_not_depend_on_the_basis_order() {
        // Every order the build walked must have returned the same dimension. The build stops at the
        // first integral one, so this covers whatever was walked on every fixture.
        for matroid in fixtures() {
            let ring = ChowRing::new(matroid).expect("the ring builds");
            for degree in 0..=ring.top() {
                let returned = ring.dimension_by_basis_order(degree);
                assert!(!returned.is_empty());
                for (order, dimension) in &returned {
                    assert_eq!(
                        *dimension,
                        ring.dimension(degree),
                        "{} grade {degree} returned {dimension} under {order:?}",
                        ring.matroid().name()
                    );
                }
            }
        }
        // And an exhaustive sweep on the small fixtures, where the intermediate rationals of a
        // reversed order stay small enough to walk every one.
        for matroid in [
            Matroid::uniform(2, 3).unwrap(),
            Matroid::uniform(3, 3).unwrap(),
            Matroid::uniform(3, 4).unwrap(),
        ] {
            let ring = ChowRing::new(matroid).expect("the ring builds");
            for degree in 0..=ring.top() {
                let expected = ring.dimension(degree);
                for order in BasisOrder::ALL {
                    assert_eq!(
                        exhaustive_dimension(&ring, degree, order),
                        expected,
                        "{} grade {degree} moved under {order:?}",
                        ring.matroid().name()
                    );
                }
            }
        }
    }

    /// Rebuild one grade under one declared order and return only its dimension.
    fn exhaustive_dimension(ring: &ChowRing, degree: usize, order: BasisOrder) -> usize {
        let flats = ring.matroid().proper_flats();
        let comparable = comparability(&flats);
        let containment = strict_containment(&flats);
        let chains = enumerate_chains(&containment, ring.top());
        let mut previous: Option<Grade> = None;
        for step in 0..=degree {
            let grade = build_grade_with(
                &flats,
                &comparable,
                &chains,
                ring.matroid().ground(),
                step,
                previous.as_ref(),
                &[order],
            );
            previous = Some(grade);
        }
        previous.expect("grade zero is always built").dimension()
    }

    // ---- two frames ----

    #[test]
    fn the_ring_characteristic_matches_the_moebius_characteristic() {
        for matroid in fixtures() {
            let expected = matroid
                .reduced_characteristic_magnitudes()
                .expect("(t−1) divides the characteristic polynomial");
            let name = matroid.name().to_owned();
            let ring = ChowRing::new(matroid).expect("the ring builds");
            let found = ring.ring_characteristic_magnitudes().unwrap();
            let found: Vec<BigInt> = found
                .into_iter()
                .map(|value| {
                    assert!(value.is_integer(), "{name} returned a non-integral μ");
                    value.to_integer()
                })
                .collect();
            assert_eq!(found, expected, "{name}: ring against Möbius");
        }
    }

    #[test]
    fn the_reduced_characteristic_coefficients_are_log_concave() {
        for matroid in fixtures() {
            let name = matroid.name().to_owned();
            let sequence = matroid
                .reduced_characteristic_magnitudes()
                .expect("(t−1) divides");
            for window in sequence.windows(3) {
                assert!(
                    &window[1] * &window[1] >= &window[0] * &window[2],
                    "{name} is not log-concave at {window:?}"
                );
            }
        }
    }

    #[test]
    fn the_generator_pairing_is_the_blowup_lattice_of_the_projective_plane() {
        for matroid in fixtures() {
            let ring = ChowRing::new(matroid).expect("the ring builds");
            if ring.top() != 2 {
                continue;
            }
            let computed = ring.generator_pairing().unwrap();
            let predicted = ring.blowup_lattice_pairing().unwrap();
            assert_eq!(
                computed,
                predicted,
                "{} disagrees with its blown-up plane",
                ring.matroid().name()
            );
            let rank_two = ring
                .flats()
                .iter()
                .filter(|flat| ring.matroid().rank_of(**flat) == 2)
                .count();
            assert_eq!(
                inertia(&predicted),
                Inertia {
                    positive: 1,
                    zero: ring.flats().len() - rank_two - 1,
                    negative: rank_two
                },
                "{} carries the wrong blow-up split",
                ring.matroid().name()
            );
        }
    }

    #[test]
    fn the_non_pappus_matroid_carries_hodge_riemann_with_no_field_beneath_it() {
        let ring = ChowRing::new(non_pappus()).expect("the ring builds");
        assert_eq!(ring.dimensions(), vec![1, 21, 1]);
        let class = ring
            .class_from_coefficients(&ring.ample_coefficients())
            .unwrap();
        let report = ring.lefschetz_report(&class, 1).unwrap();
        assert_eq!(report.primitive_dimension, 20);
        assert_eq!(
            report.primitive_split,
            Inertia {
                positive: 20,
                zero: 0,
                negative: 0
            }
        );
        assert_eq!(
            report.ambient_split,
            Inertia {
                positive: 1,
                zero: 0,
                negative: 20
            }
        );
    }

    #[test]
    fn the_vamos_ring_is_outside_the_aperture_and_the_census_says_by_how_much() {
        let vamos = Matroid::vamos().unwrap();
        assert_eq!(vamos.rank(), 4);
        assert_eq!(vamos.proper_flats().len(), 77);
        let (top_monomials, top_rows) = chain_monomial_census(&vamos, 3).unwrap();
        assert!(
            top_monomials > 900 && top_rows > 2500,
            "the Vámos census returned {top_monomials} monomials and {top_rows} rows"
        );
    }

    #[test]
    fn the_census_agrees_with_the_grades_actually_built() {
        for matroid in fixtures() {
            let ring = ChowRing::new(matroid.clone()).expect("the ring builds");
            for degree in 0..=ring.top() {
                let (monomials, rows) = chain_monomial_census(&matroid, degree).unwrap();
                assert_eq!(
                    monomials,
                    ring.chain_monomial_count(degree),
                    "{} grade {degree} monomial census",
                    ring.matroid().name()
                );
                assert!(
                    rows >= ring.relation_row_count(degree),
                    "{} grade {degree} row census {rows} under the {} built",
                    ring.matroid().name(),
                    ring.relation_row_count(degree)
                );
            }
        }
    }

    /// **One matroid hands its pairing to the winding organ and every other one is refused.**
    ///
    /// A sweep that refuses everywhere and a sweep that admits everywhere carry the same evidence,
    /// which is none, so both sides are required to be non-empty here. The single admission is
    /// `U(3,3)`, and the reason it is single is the diagonal argument on
    /// [`ChowRing::cyclic_generator_receiver`] rather than an aperture: a constant `deg(x_F²)` puts
    /// every point on exactly two lines and forces `|E| = 3`.
    #[test]
    fn only_the_boolean_matroid_hands_a_circulant_to_the_organ_that_names_windings() {
        let mut admitted: Vec<String> = Vec::new();
        let mut refused_at_the_diagonal: Vec<String> = Vec::new();
        for matroid in fixtures() {
            let name = matroid.name().to_string();
            let ring = ChowRing::new(matroid).expect("the ring builds");
            if ring.generator_pairing().is_err() {
                // Not a top grade of two; the winding question is never reached.
                continue;
            }
            match ring.cyclic_generator_receiver(1_000_000) {
                Ok(receiver) => {
                    assert!(
                        receiver.native_refusal.is_some(),
                        "{name}: the ring's own flat order was already circulant, so the two-frame \
                         claim would be one frame"
                    );
                    let split = crate::winding_inertia::winding_inertia(&receiver.circulant)
                        .expect("the circulant names its passages")
                        .split();
                    assert_eq!(
                        split,
                        inertia(&ring.generator_pairing().unwrap()),
                        "{name}: the character route and the elimination disagree"
                    );
                    admitted.push(name);
                }
                Err(ChowError::Winding(WindingError::DiagonalIsNotConstant { .. })) => {
                    refused_at_the_diagonal.push(name);
                }
                Err(other) => panic!("{name}: unexpected refusal {other}"),
            }
        }
        assert_eq!(admitted, vec!["U(3,3)".to_string()]);
        assert_eq!(refused_at_the_diagonal.len(), 4, "{refused_at_the_diagonal:?}");
    }

    /// The passages `U(3,3)` returns, named rather than counted.
    ///
    /// The null cone is the ring's own relation ideal: `|E| − 1 = 2` relations, and the two null
    /// passages are the conjugate pair at windings `1/6` and `5/6` — the hexagon traversed each way.
    /// The one returning direction the Hodge index theorem promises is character zero, the
    /// zero-frequency passage, whose star polygon `{1/0}` is the degenerate point.
    #[test]
    fn the_boolean_matroids_null_cone_is_its_relation_ideal_and_the_nulls_have_names() {
        let ring = ChowRing::new(Matroid::uniform(3, 3).expect("U(3,3)")).expect("the ring builds");
        let receiver = ring
            .cyclic_generator_receiver(1_000_000)
            .expect("U(3,3) admits a cyclic reading");
        let reading = crate::winding_inertia::winding_inertia(&receiver.circulant).unwrap();

        let nulls = reading.null_windings();
        assert_eq!(nulls.len(), ring.matroid().ground() - 1);
        assert_eq!(nulls.len(), receiver.reading.extent() - ring.dimension(1));
        assert_eq!(
            nulls,
            vec![
                Rat::new(BigInt::from(1), BigInt::from(6)),
                Rat::new(BigInt::from(5), BigInt::from(6)),
            ]
        );
        assert_eq!(
            reading.windings_past_the_hand(),
            vec![
                Rat::new(BigInt::from(1), BigInt::from(3)),
                Rat::new(BigInt::from(1), BigInt::from(2)),
                Rat::new(BigInt::from(2), BigInt::from(3)),
            ]
        );
        assert_eq!(
            reading.windings_of(crate::winding_inertia::Hand::WithTheTurn),
            vec![Rat::zero()]
        );
        assert_eq!(reading.passage(0).unwrap().star_polygon.label(), "{1/0}");
    }
}
