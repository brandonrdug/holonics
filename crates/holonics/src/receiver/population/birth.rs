//! **Birth: a reached separating covector founds an observable transport representation** (the
//! learner record's §14.1, `research/records/2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_DATA_
//! AS_PARTICLES_WITH_FLUX_AND_RELEASE_AS_A_THRESHOLD_COMMIT.md`; atlas
//! `birth.separator-transport-closure`; THE_REBUILD's ring-search row, "residual-founded transport
//! discovery first"; Lean `Compression/Landmark/Context/Birth`; #73, #63).
//!
//! [definition; agent-inferred] **Where it sits.** A navigator founded from a residual is a birth in
//! the receiver's population: the reserved mass pays for it (the population's "Birth from reserved
//! mass", [`Population::found`]), its declaration is its identity across aeons ([`super::evolution`]),
//! and the population's section residual triggers it. So the law's owner is
//! `receiver::population::birth`, beside the population that founds it; its linear algebra reads the
//! crate's exact carrier (`ratio::linear::ExactRatMatrix`, whose certified kernel returns the founded
//! coordinates) and its prime charts (`ratio::ring::ModularWords`).
//!
//! [proved-derived; formal-checked] **The founding law** (Lean `Birth.{opening_finrank,
//! ladder_stabilizes, strict_steps_le_chart, founded_invariant, founded_le, founding_intertwines,
//! encode_reads}`). In a finite rational chart `ℚ^d`, with the admitted transports `T_a` known and
//! the receiving forms `V_old` already held, a reached covector `λ_r ∉ V_old` founds
//!
//! ```text
//! V₀ = V_old + span{λ_r},   V_(n+1) = V_n + Σ_a T_a* V_n            (T_a* φ = φ ∘ T_a)
//! dim V₀ = dim V_old + 1;  strict steps ≤ d − dim V₀;  the stable rung V is the least
//!   T_a*-invariant space containing V₀
//! φ_i a basis of V,  T_a* φ_i = Σ_j U_(a,ij) φ_j   ⇒   E T_a = U_a E,    E x = (φ_i(x))_i
//! ρ_c ∈ V,  ρ_c = Σ_j D_(c,j) φ_j                  ⇒   D E = ρ
//! ```
//!
//! It constructs an observable transport representation; it does **not** infer an unknown `T_a`
//! ([counterexample] no finite observation determines an unrestricted navigator family,
//! `Computation/NavigatorObservationScope`; an unknown finite-state transport needs equivalence
//! queries, which passive data does not supply). Its refusals are typed ([`BirthError`]): a chart
//! that is not finite (no dimension, or a covector off it), a transport not declared (none, or not a
//! map of the chart), a covector that separates nothing (it lies in `V_old`), a reading outside the
//! founded forms, and a founded reading that is not one class.
//!
//! [definition; agent-inferred] **The execution** ([`Closure::found`]). A candidate `T_a* φ_i` is
//! decided independent in a prime chart (`2^61 − 1` first, then the primes below it): an image
//! independent mod `p` is independent over ℚ (a rational dependence survives the reduction), so
//! every basis vector is exact. The candidates dependent mod `p` are expressed in the basis at once
//! by the kernel of `[φ_0 … φ_(r−1) | dependents]` (`ExactRatMatrix`'s kernel, certified above its
//! crossover: each dependent column free, its kernel vector `−U_(a,i·)` on the basis); a dependent
//! the kernel does not free was an unlucky chart, and the closure restarts in the next chart, at
//! most [`DECLARED_CHARTS`] of them. The returned `U_a` stand only on the exact check
//! `E T_a = U_a E` ([`Closure::check`]), which [`Closure::found`] runs before it returns.
//!
//! [definition; agent-inferred] **The founded family** ([`FoundedFamily`]). Its hypotheses are the
//! chart's states `e_s`, the initial configuration left to be located, uniform over the `d` states
//! (the key a moiré draws). State `s` is carried in the founded chart as `z_s = E e_s`; states with
//! one configuration are one class, future-equivalent because `E T = U E` and `D E = ρ` (the
//! quotient by `ker E` is the retention). Each class is advanced by `U_a` a tick and read by `D`; its
//! reading must be one class (`D z = e_c`). The face is the surviving states' fraction emitting each
//! class, the likelihood `#S/d`, the code `log₂ d − log₂ #S` (survivor filtering, Lean
//! `Population.survivor_code`); a death is not a deposit, so a family whose classes all miss the
//! cell keeps the state it died in. It emits exactly the chart's readings: `ρ(Tᵗ x) = D Uᵗ E x`
//! (Lean `Birth.{encode_iterate, founded_reads_iterate}`).
//!
//! [proved-derived] **The founded dimension against the emission's.** For a permutation of the
//! chart's states the span of an emission's shifts is the founded forms restricted to the visited
//! orbit, so its Hankel rank is that restriction's rank: equal to `dim V` on one orbit, and below it
//! by the forms silent on the orbit, an invariant space (Lean `Birth.silent_invariant`) whose
//! rational eigenvectors are conserved charges or half-turns (`Birth.eigenvalue_of_finite_order`).
//! The founding is the chart's observable representation; the emission's minimal realization is
//! its restriction (measured on the moiré: the record of September 28).
//!
//! [definition; agent-inferred] **Which covector reaches** ([`TransportBirth::reached`]). The
//! reception's comparison at the arrival `y` is the descent covector `κ = e_y − q` on the cell
//! alphabet (`q` the receiver's face); it reaches the chart through the adjoint of the coupling
//! that produced the cells, `λ_r = ρ*κ = Σ_c κ_c ρ_c`. On a binary alphabet `κ = q_(y′)(e_y − e_(y′))`,
//! so `λ_r = q_(y′)(ρ_y − ρ_(y′))`: the polarized reading scaled by the surprise mass, whose span is
//! the polarized reading's whenever the comparison is nonzero (`q_(y′) > 0`, decided on the
//! population's enclosed face). The founding reads only that span, so the section's founding
//! ([`SectionFounding`]) reads the polarized reading `ρ_y − ρ_(y′)` exactly; on a larger alphabet an
//! enclosed comparison's direction is not decided, and it refuses. The receiving forms held are
//! `V_old = span{1}`, the mass form every face carries (`Σ_c ρ_c = 1`).
//!
//! [definition; agent-inferred] **The trigger** ([`SectionFounding`]) is the population's own: at the
//! receiver's section every `section_period` cells, once the code paid since the previous section
//! passes the founding's description `ℓ_g` (the opening section only opens the reading), the
//! founded family is born from the reserved mass `2^(−ℓ_g)` and abstained before its birth. Its
//! declaration, the covector and the closure (the admitted transports named in their declared
//! family), is charged once, in `ℓ_g`.
//!
//! [definition; agent-inferred] **The moiré's chart** ([`TransportBirth::moire`]): the gratings' joint
//! port torus `S = Π_i ℤ/q_i`, `d = Π_i q_i` (ring 0 least significant), the joint tick
//! `T e_x = e_(x + p)` (each ring's rotor, read through `holarchy::terrain::Grating::port`), and the
//! coupling of the declared class (each port's half-turn sheet through `Grating::sheet`: the parity
//! color or the sheet tuple). Only the rates `p_i/q_i` enter; the phases are the key the founded
//! family locates.
//!
//! [definition] The computational object is the helical pair interaction read at a receiver's
//! birth. Of the winding guide's six general objects this owner touches three: the **helix** (the
//! admitted transports: a grating's rotor, circle plus carry, stepping its port a tick), the **tube**
//! (the passage's clocked span over which the residual is read at the receiver's section, and the
//! ladder's rungs) and **faces and placement** (the founded faces `φ_i`, the readout `D` and the
//! founded family's face). The **pair** (the gratings' locks, which the joint torus holds and no
//! founded face reads), the **cell holonomy** (none is claimed) and the **tower thread** (no
//! restriction is founded) stay attached.

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};
use thiserror::Error;

use super::{
    Act, BirthReceipt, Declaration, Family, KeyReadout, Likelihood, Population, PopulationError,
    Readout, Reception, Work,
};
use crate::holarchy::terrain::{Grating, MoireClass, TerrainError};
use crate::ratio::Rat;
use crate::ratio::algebraic::{ExactInterval, interval_difference};
use crate::ratio::linear::{ExactLinearError, ExactRatMatrix};
use crate::ratio::ring::{ExactRing, ModularWords};
use crate::ratio::work::ExactWork;

/// **The prime charts a founding may try** (module header, "The execution"): `2^61 − 1` and the
/// primes below it. [agent-inferred] Four: a chart is unlucky only where it divides a denominator or
/// a minor of the founded forms, so a second unlucky chart is already a coincidence of two primes
/// above `2^60`, and the fourth refusal is returned rather than searched past.
pub const DECLARED_CHARTS: usize = 4;

/// Every refusal of a founding. Bad input is a typed return, never a panic.
#[derive(Debug, Error, PartialEq)]
pub enum BirthError {
    #[error("the chart is not finite: {reason}")]
    ChartNotFinite { reason: &'static str },
    #[error("a transport is not declared: {reason}")]
    TransportUndeclared { reason: &'static str },
    #[error(
        "the reached covector separates nothing: it lies in the span of the receiving forms held"
    )]
    NotSeparating,
    #[error(
        "the coupling's form of class {class} lies outside the founded forms: the reading does not factor through the founded chart"
    )]
    ReadingOutside { class: usize },
    #[error("the founded reading of chart state {state} is not one class")]
    NotAClass { state: u64 },
    #[error("E T_{transport} differs from U_{transport} E on founded form {form}")]
    Intertwining { transport: usize, form: usize },
    #[error("the comparison is {reason}")]
    Comparison { reason: &'static str },
    #[error("every one of the {charts} declared prime charts was unlucky for this founding")]
    ChartsExhausted { charts: usize },
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
    /// Boxed: a terrain's refusals are wide.
    #[error(transparent)]
    Terrain(Box<TerrainError>),
}

impl From<TerrainError> for BirthError {
    fn from(error: TerrainError) -> Self {
        Self::Terrain(Box::new(error))
    }
}

fn chart_refusal(reason: &'static str) -> BirthError {
    BirthError::ChartNotFinite { reason }
}

fn transport_refusal(reason: &'static str) -> BirthError {
    BirthError::TransportUndeclared { reason }
}

/// A sparse exact matrix, one list of `(index, value)` per row (or per column), zeros omitted.
type Sparse = Vec<Vec<(usize, Rat)>>;

/// **The admitted transports as maps of the chart, checked and read by columns**:
/// `columns[a][s] = [(r, T_a[r][s])]`, so `(T_a* φ)_s = Σ_r φ_r T_a[r][s]`.
fn transport_columns(
    chart: usize,
    transports: &[ExactRatMatrix],
) -> Result<Vec<Sparse>, BirthError> {
    if transports.is_empty() {
        return Err(transport_refusal("the founding admits no transport"));
    }
    transports
        .iter()
        .map(|transport| {
            if transport.rows() != chart || transport.columns() != chart {
                return Err(transport_refusal(
                    "an admitted transport is not a map of the declared chart",
                ));
            }
            let mut columns: Sparse = vec![Vec::new(); chart];
            for (row, values) in transport.to_rows().into_iter().enumerate() {
                for (column, value) in values.into_iter().enumerate() {
                    if !value.is_zero() {
                        columns[column].push((row, value));
                    }
                }
            }
            Ok(columns)
        })
        .collect()
}

/// `T_a* φ` over the transport's columns, with its exact work.
fn adjoint(columns: &Sparse, form: &[Rat], work: &mut ExactWork) -> Vec<Rat> {
    columns
        .iter()
        .map(|column| {
            let mut sum = Rat::zero();
            for (row, value) in column {
                if !form[*row].is_zero() {
                    sum += &form[*row] * value;
                    work.multiplied(1);
                    work.added(1);
                }
            }
            work.wrote(&sum);
            sum
        })
        .collect()
}

/// `Σ_j c_j φ_j` over a sparse row of coefficients.
fn combine(
    row: &[(usize, Rat)],
    forms: &[Vec<Rat>],
    chart: usize,
    work: &mut ExactWork,
) -> Vec<Rat> {
    let mut sum = vec![Rat::zero(); chart];
    for (j, coefficient) in row {
        for (entry, value) in sum.iter_mut().zip(&forms[*j]) {
            if !value.is_zero() {
                *entry += coefficient * value;
                work.multiplied(1);
                work.added(1);
            }
        }
    }
    sum
}

/// `M z` over sparse rows.
fn apply(rows: &[Vec<(usize, Rat)>], vector: &[Rat]) -> Vec<Rat> {
    rows.iter()
        .map(|row| {
            row.iter()
                .fold(Rat::zero(), |sum, (j, value)| sum + value * &vector[*j])
        })
        .collect()
}

// -------------------------------------------------------------------------------------------
// the prime chart's semi-echelon

/// **One prime chart's semi-echelon** (module header, "The execution"): rows reduced against the
/// earlier ones, each normalized at its pivot, so a row holds zeros at every earlier pivot.
struct ModularSpan {
    ring: ModularWords,
    rows: Vec<(usize, Vec<u64>)>,
    multiplications: u64,
}

impl ModularSpan {
    fn new(ring: ModularWords) -> Self {
        Self {
            ring,
            rows: Vec::new(),
            multiplications: 0,
        }
    }

    fn mul(&self, left: u64, right: u64) -> u64 {
        self.ring.mul(left, right).unwrap_or(0)
    }

    fn sub(&self, left: u64, right: u64) -> u64 {
        if right == 0 {
            left
        } else {
            self.ring
                .add(left, self.ring.modulus() - right)
                .unwrap_or(0)
        }
    }

    /// `x^{-1}` by Fermat: the chart is a field.
    fn invert(&self, value: u64) -> u64 {
        let (mut base, mut exponent, mut accumulated) = (value, self.ring.modulus() - 2, 1u64);
        while exponent > 0 {
            if exponent & 1 == 1 {
                accumulated = self.mul(accumulated, base);
            }
            base = self.mul(base, base);
            exponent >>= 1;
        }
        accumulated
    }

    /// A rational's residue; none where the chart divides its denominator (an unlucky chart).
    fn residue(&self, value: &Rat) -> Option<u64> {
        let modulus = BigInt::from(self.ring.modulus());
        let reduce = |integer: &BigInt| -> u64 {
            let mut remainder = integer % &modulus;
            if remainder.is_negative() {
                remainder += &modulus;
            }
            remainder
                .to_u64()
                .expect("a residue below a machine-word modulus")
        };
        let denominator = reduce(value.denom());
        (denominator != 0).then(|| self.mul(reduce(value.numer()), self.invert(denominator)))
    }

    fn image(&self, vector: &[Rat]) -> Option<Vec<u64>> {
        vector.iter().map(|value| self.residue(value)).collect()
    }

    /// **Reduce an image against the rows and hold it when independent**; whether it was held.
    fn insert(&mut self, mut image: Vec<u64>) -> bool {
        for index in 0..self.rows.len() {
            let pivot = self.rows[index].0;
            let factor = image[pivot];
            if factor == 0 {
                continue;
            }
            for column in 0..image.len() {
                let entry = self.rows[index].1[column];
                if entry != 0 {
                    image[column] = self.sub(image[column], self.mul(factor, entry));
                    self.multiplications += 1;
                }
            }
        }
        let Some(pivot) = image.iter().position(|&entry| entry != 0) else {
            return false;
        };
        let inverse = self.invert(image[pivot]);
        for entry in &mut image {
            *entry = self.mul(*entry, inverse);
        }
        self.multiplications += image.len() as u64;
        self.rows.push((pivot, image));
        true
    }
}

/// The `n`-th declared chart: `2^61 − 1`, then the primes below it in descending order.
fn declared_chart(index: usize) -> ModularWords {
    let mut modulus = ModularWords::MERSENNE61.modulus();
    for _ in 0..index {
        modulus -= 2;
        while !crate::ratio::primality::is_prime(modulus) {
            modulus -= 2;
        }
    }
    ModularWords::new(modulus).expect("a prime above two names a ring")
}

/// **The exact coordinates of dependent forms in the basis** (module header, "The execution"):
/// the kernel of `[φ_0 … φ_(r−1) | v_0 … v_(k−1)]`, each `v_j` free with its kernel vector
/// `(−c_j, e_j)`; none when a dependent is not freed (the chart was unlucky). [agent-inferred] The
/// dependents are read in blocks of at most `max(r, 1)`: the basis is independent, so each
/// dependent's coordinates are unique and a block's kernel returns exactly them, while the kernel
/// of all `k` at once would carry `k` vectors of `r + k` entries.
fn coordinates(
    forms: &[Vec<Rat>],
    dependents: &[Vec<Rat>],
    chart: usize,
    work: &mut ExactWork,
) -> Result<Option<Vec<Vec<Rat>>>, BirthError> {
    let block = forms.len().max(1);
    if dependents.len() <= block {
        return coordinates_of_block(forms, dependents, chart, work);
    }
    let mut solved = Vec::with_capacity(dependents.len());
    for part in dependents.chunks(block) {
        match coordinates_of_block(forms, part, chart, work)? {
            Some(coordinates) => solved.extend(coordinates),
            None => return Ok(None),
        }
    }
    Ok(Some(solved))
}

/// One block's kernel read (see [`coordinates`]).
fn coordinates_of_block(
    forms: &[Vec<Rat>],
    dependents: &[Vec<Rat>],
    chart: usize,
    work: &mut ExactWork,
) -> Result<Option<Vec<Vec<Rat>>>, BirthError> {
    if dependents.is_empty() {
        return Ok(Some(Vec::new()));
    }
    let (r, k) = (forms.len(), dependents.len());
    let rows: Vec<Vec<Rat>> = (0..chart)
        .map(|s| {
            forms
                .iter()
                .chain(dependents)
                .map(|column| column[s].clone())
                .collect()
        })
        .collect();
    let matrix = ExactRatMatrix::shaped(chart, r + k, rows)?;
    let (kernel, reading) = matrix.kernel_basis_with_work()?;
    *work = work.then(&reading);
    if kernel.len() != k {
        return Ok(None);
    }
    let mut result = Vec::with_capacity(k);
    for (j, vector) in kernel.into_iter().enumerate() {
        let freed = (0..k).all(|i| {
            if i == j {
                vector[r + i].is_one()
            } else {
                vector[r + i].is_zero()
            }
        });
        if !freed {
            return Ok(None);
        }
        result.push(vector[..r].iter().map(|entry| -entry.clone()).collect());
    }
    Ok(Some(result))
}

/// A dense coordinate vector as a sparse row.
fn sparse(coordinates: &[Rat]) -> Vec<(usize, Rat)> {
    coordinates
        .iter()
        .enumerate()
        .filter(|(_, value)| !value.is_zero())
        .map(|(j, value)| (j, value.clone()))
        .collect()
}

// -------------------------------------------------------------------------------------------
// the closure

/// [definition] **The founded closure** (module header): the basis `φ_i` of the stable rung, the
/// dimension of the forms held and of the opening, each rung's dimension, the matrices `U_a`
/// (sparse rows, `T_a* φ_i = Σ_j U_(a,ij) φ_j`), the charts tried and the exact work.
#[derive(Clone, Debug, PartialEq)]
pub struct Closure {
    chart: usize,
    forms: Vec<Vec<Rat>>,
    held: usize,
    rungs: Vec<usize>,
    transports: Vec<Sparse>,
    charts: usize,
    work: ExactWork,
}

/// Where a candidate `T_a* φ_i` went: a new basis form, or a dependent's index.
#[derive(Clone, Copy)]
enum Placed {
    Form(usize),
    Dependent(usize),
}

impl Closure {
    /// **Found the closure** (module header): the forms `held` (`V_old`, its dependents discarded),
    /// the reached covector `separator` (refused when it lies in their span), closed under the
    /// adjoints of the admitted `transports`, each a `chart × chart` map; the consumer equation
    /// `E T_a = U_a E` is checked exactly before the closure is returned.
    pub fn found(
        chart: usize,
        transports: &[ExactRatMatrix],
        held: &[Vec<Rat>],
        separator: &[Rat],
    ) -> Result<Self, BirthError> {
        if chart == 0 {
            return Err(chart_refusal("it declares no dimension"));
        }
        if separator.len() != chart || held.iter().any(|form| form.len() != chart) {
            return Err(chart_refusal("a covector does not read the declared chart"));
        }
        let columns = transport_columns(chart, transports)?;
        for index in 0..DECLARED_CHARTS {
            if let Some(mut closure) = Self::attempt(
                chart,
                &columns,
                held,
                separator,
                declared_chart(index),
                index + 1,
            )? {
                let checked = closure.check_columns(&columns)?;
                closure.work = closure.work.then(&checked);
                return Ok(closure);
            }
        }
        Err(BirthError::ChartsExhausted {
            charts: DECLARED_CHARTS,
        })
    }

    /// One chart's attempt; none when the chart was unlucky.
    fn attempt(
        chart: usize,
        columns: &[Sparse],
        held: &[Vec<Rat>],
        separator: &[Rat],
        ring: ModularWords,
        charts: usize,
    ) -> Result<Option<Self>, BirthError> {
        let mut span = ModularSpan::new(ring);
        let mut work = ExactWork::nothing();
        let mut forms: Vec<Vec<Rat>> = Vec::new();
        let mut discarded: Vec<Vec<Rat>> = Vec::new();
        for form in held {
            let Some(image) = span.image(form) else {
                return Ok(None);
            };
            if span.insert(image) {
                forms.push(form.clone());
            } else {
                discarded.push(form.clone());
            }
        }
        // A held form dependent mod p must be dependent over ℚ on the held forms kept.
        if coordinates(&forms, &discarded, chart, &mut work)?.is_none() {
            return Ok(None);
        }
        let held_dimension = forms.len();
        // Each dependent candidate with the ladder level whose rung it must lie in.
        let mut dependents: Vec<Vec<Rat>> = Vec::new();
        let mut levels: Vec<usize> = Vec::new();
        // The separator: independent mod p is independent over ℚ; dependent mod p is decided over
        // ℚ against the held forms alone.
        let Some(image) = span.image(separator) else {
            return Ok(None);
        };
        if !span.insert(image) {
            match coordinates(&forms, &[separator.to_vec()], chart, &mut work)? {
                Some(_) => return Err(BirthError::NotSeparating),
                None => return Ok(None),
            }
        }
        forms.push(separator.to_vec());
        let mut rungs = vec![forms.len()];
        let mut placed: Vec<Vec<Option<Placed>>> = vec![Vec::new(); columns.len()];
        let mut frontier = 0..forms.len();
        let mut level = 0usize;
        loop {
            let start = forms.len();
            for i in frontier.clone() {
                for (a, transport) in columns.iter().enumerate() {
                    let candidate = adjoint(transport, &forms[i], &mut work);
                    let Some(image) = span.image(&candidate) else {
                        return Ok(None);
                    };
                    let place = if span.insert(image) {
                        forms.push(candidate);
                        Placed::Form(forms.len() - 1)
                    } else {
                        dependents.push(candidate);
                        levels.push(level);
                        Placed::Dependent(dependents.len() - 1)
                    };
                    if placed[a].len() <= i {
                        placed[a].resize(i + 1, None);
                    }
                    placed[a][i] = Some(place);
                }
            }
            work.stepped();
            if forms.len() == start {
                break;
            }
            rungs.push(forms.len());
            frontier = start..forms.len();
            level += 1;
        }
        work.multiplied(span.multiplications);
        let Some(solved) = coordinates(&forms, &dependents, chart, &mut work)? else {
            return Ok(None);
        };
        // A candidate read at level `n` lies in the rung `V_(n+1)`: its coordinates vanish past it
        // (the basis is independent, so they are unique). Otherwise the chart was unlucky and the
        // rungs would misreport the ladder.
        for (coordinates, &level) in solved.iter().zip(&levels) {
            let bound = rungs.get(level + 1).copied().unwrap_or(forms.len());
            if coordinates[bound..].iter().any(|entry| !entry.is_zero()) {
                return Ok(None);
            }
        }
        let r = forms.len();
        let transports = placed
            .into_iter()
            .map(|rows| {
                (0..r)
                    .map(|i| match rows.get(i).copied().flatten() {
                        Some(Placed::Form(m)) => vec![(m, Rat::one())],
                        Some(Placed::Dependent(j)) => sparse(&solved[j]),
                        None => unreachable!("every form is a candidate's source once"),
                    })
                    .collect()
            })
            .collect();
        for form in &forms {
            for entry in form {
                work.wrote(entry);
            }
        }
        work.resident(u64::try_from(r.saturating_mul(chart)).unwrap_or(u64::MAX));
        Ok(Some(Self {
            chart,
            forms,
            held: held_dimension,
            rungs,
            transports,
            charts,
            work,
        }))
    }

    /// **The consumer equation, checked exactly**: row `i` of `E T_a` is `T_a* φ_i` and row `i` of
    /// `U_a E` is `Σ_j U_(a,ij) φ_j`; they agree for every admitted `a` and founded form `i`.
    pub fn check(&self, transports: &[ExactRatMatrix]) -> Result<ExactWork, BirthError> {
        let columns = transport_columns(self.chart, transports)?;
        if columns.len() != self.transports.len() {
            return Err(transport_refusal(
                "the check reads the transports the closure was founded under",
            ));
        }
        self.check_columns(&columns)
    }

    fn check_columns(&self, columns: &[Sparse]) -> Result<ExactWork, BirthError> {
        let mut work = ExactWork::nothing();
        for (a, (transport, rows)) in columns.iter().zip(&self.transports).enumerate() {
            for (i, (form, row)) in self.forms.iter().zip(rows).enumerate() {
                let left = adjoint(transport, form, &mut work);
                let right = combine(row, &self.forms, self.chart, &mut work);
                if left != right {
                    return Err(BirthError::Intertwining {
                        transport: a,
                        form: i,
                    });
                }
            }
        }
        Ok(work)
    }

    /// The chart's dimension `d`.
    pub fn chart(&self) -> usize {
        self.chart
    }

    /// **The founded dimension** `dim V`.
    pub fn dimension(&self) -> usize {
        self.forms.len()
    }

    /// `dim span(V_old)`.
    pub fn held(&self) -> usize {
        self.held
    }

    /// `dim V_n` at each rung, from the opening `V₀` to the stable rung.
    pub fn rungs(&self) -> &[usize] {
        &self.rungs
    }

    /// **The strict steps**: the rungs that raised the dimension.
    pub fn strict_steps(&self) -> usize {
        self.rungs.len() - 1
    }

    /// The founded forms `φ_i`, each a covector on the chart.
    pub fn forms(&self) -> &[Vec<Rat>] {
        &self.forms
    }

    /// The prime charts the founding tried (one unless a chart was unlucky).
    pub fn charts(&self) -> usize {
        self.charts
    }

    /// The exact work of the founding (the check's is returned by [`Closure::check`]).
    pub fn work(&self) -> &ExactWork {
        &self.work
    }

    /// **`U_a`** as a dense exact matrix.
    pub fn transport(&self, a: usize) -> Result<ExactRatMatrix, BirthError> {
        let rows = self
            .transports
            .get(a)
            .ok_or_else(|| transport_refusal("it names an admitted transport"))?;
        let r = self.forms.len();
        let mut dense = vec![vec![Rat::zero(); r]; r];
        for (i, row) in rows.iter().enumerate() {
            for (j, value) in row {
                dense[i][*j] = value.clone();
            }
        }
        Ok(ExactRatMatrix::shaped(r, r, dense)?)
    }

    /// **The encoding** `E x = (φ_i(x))_i`.
    pub fn encode(&self, x: &[Rat]) -> Result<Vec<Rat>, BirthError> {
        if x.len() != self.chart {
            return Err(chart_refusal(
                "a configuration does not lie in the declared chart",
            ));
        }
        Ok(self
            .forms
            .iter()
            .map(|form| form.iter().zip(x).map(|(f, v)| f * v).sum())
            .collect())
    }

    /// `E e_s`: state `s`'s configuration in the founded chart.
    fn state(&self, s: usize) -> Vec<Rat> {
        self.forms.iter().map(|form| form[s].clone()).collect()
    }

    /// **The readout** `D` with `D E = ρ`: each coupling form's coordinates in the founded basis;
    /// refused when a form lies outside the founded forms.
    pub fn readout(&self, coupling: &[Vec<Rat>]) -> Result<ExactRatMatrix, BirthError> {
        if coupling.iter().any(|form| form.len() != self.chart) {
            return Err(chart_refusal(
                "a coupling form does not read the declared chart",
            ));
        }
        let mut work = ExactWork::nothing();
        let Some(solved) = coordinates(&self.forms, coupling, self.chart, &mut work)? else {
            let class = coupling
                .iter()
                .position(|form| {
                    coordinates(
                        &self.forms,
                        std::slice::from_ref(form),
                        self.chart,
                        &mut work,
                    )
                    .ok()
                    .flatten()
                    .is_none()
                })
                .unwrap_or(0);
            return Err(BirthError::ReadingOutside { class });
        };
        Ok(ExactRatMatrix::shaped(
            coupling.len(),
            self.forms.len(),
            solved,
        )?)
    }
}

// -------------------------------------------------------------------------------------------
// the founded family

/// One class of chart states with one founded configuration.
#[derive(Clone, Debug)]
struct Class {
    configuration: Vec<Rat>,
    states: Vec<u64>,
    emits: usize,
}

/// [definition] **The founded family** (module header): survivor filtering over the chart's states,
/// carried in the founded chart and advanced by `U_a` (the declared tick), read by `D`.
#[derive(Clone, Debug)]
pub struct FoundedFamily {
    label: String,
    description: u64,
    declaration: Declaration,
    alphabet: usize,
    transport: Sparse,
    readout: Sparse,
    classes: Vec<Class>,
    space: u64,
    count: u64,
    likelihood: Rat,
    work: Work,
}

/// The one class a founded configuration reads, `D z = e_c`; none otherwise.
fn read_class(readout: &Sparse, configuration: &[Rat]) -> Option<usize> {
    let reading = apply(readout, configuration);
    let class = reading.iter().position(|value| value.is_one())?;
    reading
        .iter()
        .enumerate()
        .all(|(c, value)| c == class || value.is_zero())
        .then_some(class)
}

impl FoundedFamily {
    /// **The family of a closure** (module header): the chart's states grouped by their founded
    /// configuration, each class reading one class of the `alphabet` through `D`; the tick is the
    /// admitted transport `tick`.
    pub fn new(
        closure: &Closure,
        readout: &ExactRatMatrix,
        tick: usize,
        description: u64,
        declaration: Declaration,
    ) -> Result<Self, BirthError> {
        let transport = closure
            .transports
            .get(tick)
            .cloned()
            .ok_or_else(|| transport_refusal("the tick names an admitted transport"))?;
        if readout.columns() != closure.dimension() || readout.rows() == 0 {
            return Err(chart_refusal(
                "the readout reads the founded chart onto a class alphabet",
            ));
        }
        let readout: Sparse = readout.to_rows().iter().map(|row| sparse(row)).collect();
        let mut grouped: BTreeMap<Vec<Rat>, Vec<u64>> = BTreeMap::new();
        for s in 0..closure.chart() {
            grouped.entry(closure.state(s)).or_default().push(s as u64);
        }
        let classes = grouped
            .into_iter()
            .map(|(configuration, states)| {
                let emits = read_class(&readout, &configuration)
                    .ok_or(BirthError::NotAClass { state: states[0] })?;
                Ok(Class {
                    configuration,
                    states,
                    emits,
                })
            })
            .collect::<Result<Vec<_>, BirthError>>()?;
        let space = closure.chart() as u64;
        Ok(Self {
            label: format!(
                "founded: chart {}, {} forms after {} strict steps",
                closure.chart(),
                closure.dimension(),
                closure.strict_steps()
            ),
            description,
            declaration,
            alphabet: readout.len(),
            transport,
            readout,
            classes,
            space,
            count: space,
            likelihood: Rat::one(),
            work: Work::default(),
        })
    }

    /// The classes of chart states the family still holds (one founded configuration each).
    pub fn classes(&self) -> usize {
        self.classes.len()
    }

    /// The surviving chart states `#S`.
    pub fn count(&self) -> u64 {
        self.count
    }
}

impl Family for FoundedFamily {
    fn label(&self) -> String {
        self.label.clone()
    }

    fn alphabet(&self) -> usize {
        self.alphabet
    }

    fn description(&self) -> u64 {
        self.description
    }

    fn face(&self) -> Result<Vec<Rat>, PopulationError> {
        let mut counts = vec![0u64; self.alphabet];
        for class in &self.classes {
            counts[class.emits] += class.states.len() as u64;
        }
        let total = BigInt::from(self.count);
        Ok(counts
            .into_iter()
            .map(|count| Rat::new(BigInt::from(count), total.clone()))
            .collect())
    }

    fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError> {
        if cell >= self.alphabet {
            return Err(PopulationError::CellOutside {
                cell,
                alphabet: self.alphabet,
            });
        }
        self.work.add(Act::Read, self.classes.len() as u64);
        let hits: u64 = self
            .classes
            .iter()
            .filter(|class| class.emits == cell)
            .map(|class| class.states.len() as u64)
            .sum();
        if hits == 0 {
            // A death is not a deposit: the family keeps the state it died in.
            return Ok(Rat::zero());
        }
        let before = self.count;
        let mut kept = Vec::with_capacity(self.classes.len());
        for mut class in std::mem::take(&mut self.classes) {
            if class.emits != cell {
                continue;
            }
            class.configuration = apply(&self.transport, &class.configuration);
            class.emits = read_class(&self.readout, &class.configuration).ok_or(
                PopulationError::Birth(Box::new(BirthError::NotAClass {
                    state: class.states[0],
                })),
            )?;
            kept.push(class);
        }
        self.work.add(Act::Transport, kept.len() as u64);
        self.classes = kept;
        self.count = hits;
        let face = Rat::new(BigInt::from(hits), BigInt::from(before));
        self.likelihood *= &face;
        Ok(face)
    }

    fn likelihood(&self) -> Likelihood {
        Likelihood::Exact(self.likelihood.clone())
    }

    fn readout(&self) -> Readout {
        let mut states: Vec<u64> = self
            .classes
            .iter()
            .flat_map(|class| class.states.iter().copied())
            .collect();
        states.sort_unstable();
        Readout::Keys(KeyReadout {
            spaces: vec![self.space],
            survivors: vec![states.into_iter().map(|s| vec![s]).collect()],
            masses: Vec::new(),
            dormant: Vec::new(),
        })
    }

    fn declaration(&self) -> Declaration {
        self.declaration.clone()
    }

    fn work(&self) -> Work {
        self.work.clone()
    }
}

// -------------------------------------------------------------------------------------------
// the founding's declaration

/// [definition; agent-inferred] **A founding's declaration** (module header): the finite chart and
/// its admitted transports, the coupling `ρ` (one form per cell class), the receiving forms held,
/// the tick, the description `ℓ_g` charged once in the prior, and the transports' declaration.
#[derive(Clone, Debug)]
pub struct TransportBirth {
    chart: usize,
    transports: Vec<ExactRatMatrix>,
    coupling: Vec<Vec<Rat>>,
    held: Vec<Vec<Rat>>,
    tick: usize,
    description: u64,
    declaration: Declaration,
}

/// [definition] **A founding's return**: the closure and the family founded on it.
#[derive(Clone, Debug)]
pub struct Founded {
    pub closure: Closure,
    pub family: FoundedFamily,
}

impl TransportBirth {
    /// **Declare a founding**; refused when the chart is not finite, a covector does not read it, or
    /// a transport (or the tick) is not declared.
    pub fn new(
        chart: usize,
        transports: Vec<ExactRatMatrix>,
        coupling: Vec<Vec<Rat>>,
        held: Vec<Vec<Rat>>,
        tick: usize,
        description: u64,
        declaration: Declaration,
    ) -> Result<Self, BirthError> {
        if chart == 0 {
            return Err(chart_refusal("it declares no dimension"));
        }
        if coupling.is_empty() || coupling.iter().chain(&held).any(|form| form.len() != chart) {
            return Err(chart_refusal(
                "the coupling reads at least one class, and every form reads the declared chart",
            ));
        }
        transport_columns(chart, &transports)?;
        if tick >= transports.len() {
            return Err(transport_refusal("the tick names an admitted transport"));
        }
        Ok(Self {
            chart,
            transports,
            coupling,
            held,
            tick,
            description,
            declaration,
        })
    }

    /// **The moiré's chart** (module header): the joint port torus of rings of the declared rates
    /// `(p_i, q_i)`, its joint tick and the coupling of the declared class; the mass form held. The
    /// declaration names the rates (`kind` "rotor", `[p_i, q_i]` each).
    pub fn moire(
        rates: &[(u64, u64)],
        class: MoireClass,
        description: u64,
    ) -> Result<Self, BirthError> {
        if rates.is_empty() {
            return Err(transport_refusal("the moiré declares at least one ring"));
        }
        let chart = rates
            .iter()
            .try_fold(1usize, |extent, &(_, q)| {
                usize::try_from(q).ok().and_then(|q| extent.checked_mul(q))
            })
            .ok_or_else(|| chart_refusal("the joint torus exceeds the address space"))?;
        // Each ring's rotor after one tick and each port's sheet, read from the terrain's gratings.
        let mut steps = Vec::with_capacity(rates.len());
        let mut sheets = Vec::with_capacity(rates.len());
        for &(p, q) in rates {
            let ports = (0..q)
                .map(|port| Grating::new(p, q, port))
                .collect::<Result<Vec<_>, _>>()?;
            steps.push(ports.iter().map(|g| g.port(1) as usize).collect::<Vec<_>>());
            sheets.push(ports.iter().map(|g| g.sheet(0)).collect::<Vec<_>>());
        }
        let digits = |mut state: usize| -> Vec<usize> {
            rates
                .iter()
                .map(|&(_, q)| {
                    let digit = state % q as usize;
                    state /= q as usize;
                    digit
                })
                .collect()
        };
        let index = |digits: &[usize]| -> usize {
            digits
                .iter()
                .zip(rates)
                .rev()
                .fold(0, |state, (&digit, &(_, q))| state * q as usize + digit)
        };
        let alphabet = match class {
            MoireClass::Parity => 2,
            MoireClass::Sheets => 1usize << rates.len(),
        };
        let mut tick = vec![vec![Rat::zero(); chart]; chart];
        let mut coupling = vec![vec![Rat::zero(); chart]; alphabet];
        for state in 0..chart {
            let x = digits(state);
            let next: Vec<usize> = x
                .iter()
                .zip(&steps)
                .map(|(&port, step)| step[port])
                .collect();
            tick[index(&next)][state] = Rat::one();
            let on = x.iter().zip(&sheets).map(|(&port, sheet)| sheet[port]);
            let cell = match class {
                MoireClass::Parity => on.filter(|&sheet| sheet).count() % 2,
                MoireClass::Sheets => on
                    .enumerate()
                    .map(|(i, sheet)| usize::from(sheet) << i)
                    .sum(),
            };
            coupling[cell][state] = Rat::one();
        }
        let declaration = Declaration::new("separator transport closure", vec![chart as u64]).with(
            rates
                .iter()
                .map(|&(p, q)| Declaration::new("rotor", vec![p, q]))
                .collect(),
        );
        Self::new(
            chart,
            vec![ExactRatMatrix::shaped(chart, chart, tick)?],
            coupling,
            vec![vec![Rat::one(); chart]],
            0,
            description,
            declaration,
        )
    }

    /// The chart's dimension `d`.
    pub fn chart(&self) -> usize {
        self.chart
    }

    /// The description `ℓ_g` charged once in the prior.
    pub fn description(&self) -> u64 {
        self.description
    }

    /// The admitted transports.
    pub fn transports(&self) -> &[ExactRatMatrix] {
        &self.transports
    }

    /// The coupling `ρ`, one form per cell class.
    pub fn coupling(&self) -> &[Vec<Rat>] {
        &self.coupling
    }

    /// **The reached covector** `λ_r = ρ*κ = Σ_c κ_c ρ_c` of a comparison `κ` on the cell alphabet
    /// (module header, "Which covector reaches").
    pub fn reached(&self, comparison: &[Rat]) -> Result<Vec<Rat>, BirthError> {
        if comparison.len() != self.coupling.len() {
            return Err(BirthError::Comparison {
                reason: "not read on the coupling's cell alphabet",
            });
        }
        let mut covector = vec![Rat::zero(); self.chart];
        for (weight, form) in comparison.iter().zip(&self.coupling) {
            if weight.is_zero() {
                continue;
            }
            for (entry, value) in covector.iter_mut().zip(form) {
                *entry += weight * value;
            }
        }
        Ok(covector)
    }

    /// **Found** (module header): the closure of the held forms and the reached covector under the
    /// admitted transports, its consumer equation checked, its readout `D E = ρ`, and the family
    /// founded on it.
    pub fn found(&self, separator: &[Rat]) -> Result<Founded, BirthError> {
        let closure = Closure::found(self.chart, &self.transports, &self.held, separator)?;
        let readout = closure.readout(&self.coupling)?;
        let mut declaration = self.declaration.clone();
        declaration.parameters.push(closure.dimension() as u64);
        let family =
            FoundedFamily::new(&closure, &readout, self.tick, self.description, declaration)?;
        Ok(Founded { closure, family })
    }
}

// -------------------------------------------------------------------------------------------
// the section's founding

/// [definition] **A founding's receipt**: the birth's (its cell, mass, charge, the residual that
/// triggered it), the arrived class whose comparison reached, and the closure's chart, forms held,
/// rungs, founded dimension, charts tried and exact work (its check's included).
#[derive(Clone, Debug, PartialEq)]
pub struct FoundingReceipt {
    pub birth: BirthReceipt,
    pub arrived: usize,
    pub chart: usize,
    pub held: usize,
    pub rungs: Vec<usize>,
    pub dimension: usize,
    pub charts: usize,
    pub work: ExactWork,
}

/// [definition; agent-inferred] **The founding at the receiver's section** (module header, "The
/// trigger"): the declared founding, the section's period, the code at the previous section, and
/// the receipt once founded (one birth a founding).
pub struct SectionFounding {
    birth: TransportBirth,
    section_period: usize,
    previous: Option<ExactInterval>,
    receipt: Option<FoundingReceipt>,
}

impl SectionFounding {
    /// **Declare the section's founding**; refused at an empty section or a coupling that is not
    /// binary (an enclosed comparison's direction is decided only there: module header).
    pub fn new(birth: TransportBirth, section_period: usize) -> Result<Self, BirthError> {
        if section_period == 0 {
            return Err(BirthError::Comparison {
                reason: "read at a section of no cells",
            });
        }
        if birth.coupling.len() != 2 {
            return Err(BirthError::Comparison {
                reason: "decided in direction only on a binary alphabet",
            });
        }
        Ok(Self {
            birth,
            section_period,
            previous: None,
            receipt: None,
        })
    }

    /// The founding's receipt, once founded.
    pub fn receipt(&self) -> Option<&FoundingReceipt> {
        self.receipt.as_ref()
    }

    /// **Receive one cell through the population**; at a section whose residual passes the
    /// founding's description, found the family from the comparison at that cell (module header).
    pub fn receive(
        &mut self,
        population: &mut Population,
        cell: usize,
    ) -> Result<Reception, PopulationError> {
        let at_section =
            self.receipt.is_none() && (population.cells() + 1) % self.section_period == 0;
        let face = if at_section {
            Some(population.face()?)
        } else {
            None
        };
        let reception = population.receive(cell)?;
        let Some(face) = face else {
            return Ok(reception);
        };
        let code = population.code()?;
        let opening = self.previous.is_none();
        let residual = match &self.previous {
            Some(previous) => interval_difference(&code, previous)?,
            None => code.clone(),
        };
        self.previous = Some(code);
        let charge = Rat::from_integer(BigInt::from(self.birth.description));
        if opening || residual.lower <= charge {
            return Ok(reception);
        }
        // The comparison `e_y − q` on the binary alphabet: `q_(y′) (e_y − e_(y′))`, decided nonzero
        // when the other class's enclosed mass is positive; its direction is exact.
        let other = 1 - cell;
        if !face[other].lower.is_positive() {
            return Ok(reception);
        }
        let mut direction = vec![Rat::zero(); 2];
        direction[cell] = Rat::one();
        direction[other] = -Rat::one();
        let separator = self.birth.reached(&direction)?;
        let founded = self.birth.found(&separator)?;
        let birth = population.found(Box::new(founded.family), Some(residual))?;
        self.receipt = Some(FoundingReceipt {
            birth,
            arrived: cell,
            chart: founded.closure.chart(),
            held: founded.closure.held(),
            rungs: founded.closure.rungs().to_vec(),
            dimension: founded.closure.dimension(),
            charts: founded.closure.charts(),
            work: founded.closure.work().clone(),
        });
        Ok(reception)
    }
}
