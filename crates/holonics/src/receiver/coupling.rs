//! Acceptance-side ordered holding contacts, beside the listener.
//!
//! `lambda` is the greatest number of equal, strictly order-consistent contacts and
//! `F* = |H| + |T| - 2 lambda`. Prefix/suffix lengths retain the **union** of all optimal
//! couplings. That union is generally not itself a coupling: crossing contacts remain
//! alternatives. Maximal contiguous diagonal plateaus are individually co-admissible.
//! No selected alignment, repaired class, target-conditioned prediction or deposition is
//! returned. The consumer is the campaign's offline reader of the preserved terminal lives.
//!
//! This is the Rust realization of the validated exterior `coupling_reader.py` recurrence.
//! The equality face is codec-neutral (text, image, sound and motor charts may supply their
//! own cells); the actual 32-class framing adapter is separate. Lock phases are supplied by
//! [`crate::geometry::solenoid::field`], never inferred from cell lag or advanced here.
//! Equal multisets with the same key cancel their group sum at the terminal section;
//! individual intermediate plateaus can still have nonzero phase difference. No converse
//! content inference is made from a phase alone. The joined exact optimal-contact/phase-reading
//! statement remains a Lean obligation #62.

use crate::geometry::solenoid::field::LockPhase;
use num_bigint::{BigInt, BigUint, Sign};
use num_traits::{One, Zero};
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

fn workspace<T: Clone>(size: usize, value: T) -> Result<Vec<T>, CouplingRefusal> {
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

/// The external 32-class chart excludes exactly a trailing `[0,0]`.
/// A zero octet `[0,16]` is payload; an internal end is refused without cutting.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Payload32<'a> {
    pub cells: &'a [usize],
    pub framing_end_present: bool,
}

pub fn payload32(whole: &[usize], strand: Strand) -> Result<Payload32<'_>, CouplingRefusal> {
    for (index, &class) in whole.iter().enumerate() {
        if class >= 32 {
            return Err(CouplingRefusal::Class {
                strand,
                index,
                class,
            });
        }
    }
    if let Some(index) = whole.windows(2).position(|pair| pair == [0, 0]) {
        if index + 2 != whole.len() {
            return Err(CouplingRefusal::InternalEnd { strand, index });
        }
        Ok(Payload32 {
            cells: &whole[..index],
            framing_end_present: true,
        })
    } else {
        Ok(Payload32 {
            cells: whole,
            framing_end_present: false,
        })
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct FramedCoupling {
    pub coupling: Coupling,
    pub h_framing_end_present: bool,
    pub t_framing_end_present: bool,
}

pub fn coupling32(h_whole: &[usize], t_whole: &[usize]) -> Result<FramedCoupling, CouplingRefusal> {
    let h = payload32(h_whole, Strand::H)?;
    let t = payload32(t_whole, Strand::T)?;
    Ok(FramedCoupling {
        coupling: coupling(h.cells, t.cells)?,
        h_framing_end_present: h.framing_end_present,
        t_framing_end_present: t.framing_end_present,
    })
}

/// Exact `Delta-lambda = V_H - V_T`, including the supplied Z lift.
/// `z_lift = residue + modulus * whole_winding`; digits are least significant first.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PhaseDifference {
    pub z_lift: BigInt,
    pub residue: BigUint,
    pub whole_winding: BigInt,
    pub digits: Vec<BigUint>,
}

/// Carries of the actual participants, retained even when their difference is constant.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PairedCarry {
    pub h_index: usize,
    pub t_index: usize,
    pub h_winding: BigInt,
    pub t_winding: BigInt,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LockPlateau {
    /// Index of the co-admissible diagonal plateau before phase refinement.
    pub contact_plateau: usize,
    pub h_start: usize,
    pub t_start: usize,
    pub length: usize,
    pub first_rank: usize,
    pub delta: PhaseDifference,
    pub carries: Vec<PairedCarry>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LockReading {
    /// Ordered factors are retained, including non-prime ring radices.
    pub radices: Vec<BigUint>,
    pub modulus: BigUint,
    /// All geometric plateaus, split only where the actual lifted difference changes.
    pub plateaus: Vec<LockPlateau>,
    pub least_friction: usize,
    /// Friction read at both strands' supplied terminal sections, also for empty replies.
    pub end_delta: PhaseDifference,
    pub h_end_winding: BigInt,
    pub t_end_winding: BigInt,
}

fn validate_path(
    path: &[LockPhase],
    cells: usize,
    strand: Strand,
    radices: &[BigUint],
    modulus: &BigUint,
) -> Result<(), CouplingRefusal> {
    let expected = cells.checked_add(1).ok_or(CouplingRefusal::Shape)?;
    if path.len() != expected {
        return Err(CouplingRefusal::PhaseShape {
            strand,
            expected,
            actual: path.len(),
        });
    }
    for (index, phase) in path.iter().enumerate() {
        let refuse = |reason| CouplingRefusal::Phase {
            strand,
            index,
            reason,
        };
        if phase.digits.len() != radices.len() {
            return Err(refuse(PhaseDefect::DigitArity));
        }
        let mut value = BigUint::zero();
        let mut place = BigUint::one();
        for (digit, radix) in phase.digits.iter().zip(radices) {
            if digit >= radix {
                return Err(refuse(PhaseDefect::DigitRange));
            }
            value += digit * &place;
            place *= radix;
        }
        if phase.value >= *modulus {
            return Err(refuse(PhaseDefect::ValueRange));
        }
        if value != phase.value {
            return Err(refuse(PhaseDefect::DigitValue));
        }
        if phase.lift != BigInt::from(value) + BigInt::from(modulus.clone()) * &phase.winding {
            return Err(refuse(PhaseDefect::Lift));
        }
    }
    Ok(())
}

fn difference(
    h: &LockPhase,
    t: &LockPhase,
    radices: &[BigUint],
    modulus: &BigUint,
) -> PhaseDifference {
    let z_lift = &h.lift - &t.lift;
    let modulus_z = BigInt::from(modulus.clone());
    let mut remainder = &z_lift % &modulus_z;
    if remainder.sign() == Sign::Minus {
        remainder += &modulus_z;
    }
    let whole_winding = (&z_lift - &remainder) / modulus_z;
    let residue = remainder
        .to_biguint()
        .expect("Euclidean remainder is nonnegative");
    let mut digits = Vec::with_capacity(radices.len());
    let mut rest = residue.clone();
    for radix in radices {
        digits.push(&rest % radix);
        rest /= radix;
    }
    PhaseDifference {
        z_lift,
        residue,
        whole_winding,
        digits,
    }
}

/// Annotate the class reading through actual J1 phases at each cell's entrance and at
/// the terminal section (`path.len() == cells.len()+1`). The caller supplies the declared
/// Lock chain radices; Own clocks are not folded into this modulus. An annotation does
/// not assert a dynamical lock: it checks/splits constancy of the observed phase difference.
/// Carries come from J1's current, not from a second stepping law.
pub fn annotate_lock_phases(
    reading: &Coupling,
    radices: &[BigUint],
    h: &[LockPhase],
    t: &[LockPhase],
) -> Result<LockReading, CouplingRefusal> {
    let mut modulus = BigUint::one();
    for (level, radix) in radices.iter().enumerate() {
        if radix.is_zero() {
            return Err(CouplingRefusal::ZeroRadix { level });
        }
        modulus *= radix;
    }
    validate_path(h, reading.h_cells, Strand::H, radices, &modulus)?;
    validate_path(t, reading.t_cells, Strand::T, radices, &modulus)?;
    let total = reading
        .h_cells
        .checked_add(reading.t_cells)
        .ok_or(CouplingRefusal::Shape)?;
    if reading.lambda > reading.h_cells.min(reading.t_cells)
        || reading.least_friction != total - 2 * reading.lambda
        || reading.unresolved_h_per_optimum != reading.h_cells - reading.lambda
        || reading.unresolved_t_per_optimum != reading.t_cells - reading.lambda
        || reading.plural_optimal_contacts.len() < reading.lambda
    {
        return Err(CouplingRefusal::ContactShape);
    }
    let mut previous = None;
    for contact in &reading.plural_optimal_contacts {
        let here = (contact.h_index, contact.t_index);
        if contact.h_index >= reading.h_cells
            || contact.t_index >= reading.t_cells
            || contact.rank_on_any_optimal_coupling == 0
            || contact.rank_on_any_optimal_coupling > reading.lambda
            || previous.is_some_and(|before| before >= here)
        {
            return Err(CouplingRefusal::ContactShape);
        }
        previous = Some(here);
    }
    let mut covered = Vec::new();
    let mut plateaus = Vec::<LockPlateau>::new();
    for (contact_plateau, plateau) in reading.maximal_contiguous_plateaus.iter().enumerate() {
        if plateau.length == 0
            || plateau.h_start > reading.h_cells
            || plateau.t_start > reading.t_cells
            || plateau.length > reading.h_cells - plateau.h_start
            || plateau.length > reading.t_cells - plateau.t_start
            || plateau.first_rank == 0
            || plateau.first_rank > reading.lambda
            || plateau.length > reading.lambda - plateau.first_rank + 1
        {
            return Err(CouplingRefusal::ContactShape);
        }
        for k in 0..plateau.length {
            let (i, j) = (plateau.h_start + k, plateau.t_start + k);
            let contact_index = reading
                .plural_optimal_contacts
                .binary_search_by_key(&(i, j), |c| (c.h_index, c.t_index))
                .map_err(|_| CouplingRefusal::ContactShape)?;
            if reading.plural_optimal_contacts[contact_index].rank_on_any_optimal_coupling
                != plateau.first_rank + k
            {
                return Err(CouplingRefusal::ContactShape);
            }
            covered.push((i, j));
            let delta = difference(&h[i], &t[j], radices, &modulus);
            let carry = PairedCarry {
                h_index: i,
                t_index: j,
                h_winding: h[i].winding.clone(),
                t_winding: t[j].winding.clone(),
            };
            if let Some(last) = plateaus
                .last_mut()
                .filter(|p| p.contact_plateau == contact_plateau && p.delta == delta)
            {
                last.length += 1;
                last.carries.push(carry);
            } else {
                plateaus.push(LockPlateau {
                    contact_plateau,
                    h_start: i,
                    t_start: j,
                    length: 1,
                    first_rank: plateau.first_rank + k,
                    delta,
                    carries: vec![carry],
                });
            }
        }
    }
    covered.sort_unstable();
    if !covered.iter().copied().eq(reading
        .plural_optimal_contacts
        .iter()
        .map(|c| (c.h_index, c.t_index)))
    {
        return Err(CouplingRefusal::ContactShape);
    }
    let h_end = &h[reading.h_cells];
    let t_end = &t[reading.t_cells];
    Ok(LockReading {
        radices: radices.to_vec(),
        end_delta: difference(h_end, t_end, radices, &modulus),
        modulus,
        plateaus,
        least_friction: reading.least_friction,
        h_end_winding: h_end.winding.clone(),
        t_end_winding: t_end.winding.clone(),
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
/// **Exact arithmetic.** A face enters as its masses and total; `p̂_i(c) = release(m_c 2^62 / total)` on `2^(−62)`.
/// Each row of a sweep is formed from the row before (each term a product released to `2^(−62)`), summed as integers,
/// and divided by its own sum (released to the nearest): the rows are the posterior's own normalization, and the code
/// is `L = −Σ_i log₂ c_i − log₂ α̂(n, m)`, read on `2^(−20)` bits from the integer row sums. Every operation is an integer
/// with a declared release, so any realization that forms the same rows gives the same bits. A row whose mass releases
/// to zero is refused, never repaired.
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

/// The grain of a sweep's probabilities and rows.
const SWEEP_BITS: u32 = 62;
/// The grain of a placed share and a lag (the learner's covector grain, `hnn::tower::COVECTOR_BITS`).
const SHARE_BITS_T: u32 = 24;
/// The grain of a code (`hnn::tower::READ_BITS`).
const CODE_BITS: u32 = 20;

fn nearest(x: u128, k: u128) -> u128 {
    (x + k / 2) / k
}

fn released(x: u128) -> u128 {
    (x + (1u128 << (SWEEP_BITS - 1))) >> SWEEP_BITS
}

/// `log₂(v / 2^62)` on `2^(−20)` for `v > 0`: the whole part from `v`'s width, then the mantissa's digits by squaring
/// (released at `2^(−62)`), as `hnn::keyed_modes::log2_face` reads them, without its bound on `v`.
fn log2_ratio(v: u128) -> i128 {
    let width = 128 - v.leading_zeros();
    let whole = width as i128 - 1 - SWEEP_BITS as i128;
    let mut mantissa = if width > 63 { v >> (width - 63) } else { v << (63 - width) };
    let mut fraction = 0i128;
    for _ in 0..CODE_BITS {
        mantissa = (mantissa * mantissa) >> SWEEP_BITS;
        fraction <<= 1;
        if mantissa >= 1u128 << 63 {
            fraction |= 1;
            mantissa >>= 1;
        }
    }
    (whole << CODE_BITS) + fraction
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
    let p = |i: usize, c: usize| -> u128 { nearest(faces[i].0[c] << SWEEP_BITS, faces[i].1) };
    // The omission's weight 2^(−ℓ) on 2^(−62): the whole bits as a shift, the fraction's binary digits as the square
    // roots 2^(−2^(−k)), each the square root of the one before, released at 2^(−62).
    let w: u128 = match omit {
        None => 0,
        Some(l) => {
            let l = l.max(0) as u128;
            let (whole, frac) = (l >> CODE_BITS, l & ((1 << CODE_BITS) - 1));
            if whole >= SWEEP_BITS as u128 {
                0
            } else {
                let (mut v, mut root) = (1u128 << SWEEP_BITS, (1u128 << SWEEP_BITS) / 2);
                for k in 1..=CODE_BITS {
                    root = (root << SWEEP_BITS).isqrt();
                    if frac >> (CODE_BITS - k) & 1 == 1 {
                        v = released(v * root);
                    }
                }
                v >> whole
            }
        }
    };
    // The feasible cells of row i: with nothing omitted, m − j ≤ n − i and j ≤ i.
    let lo = |i: usize| if omit.is_some() { 0 } else { m.saturating_sub(n - i) };
    let hi = |i: usize| if omit.is_some() { m } else { i.min(m) };
    let one = 1u128 << SWEEP_BITS;
    // The prefix sweep: rows 0..=n, each over cells 0..=m, normalized; the sums kept for the code.
    let mut alpha = vec![vec![0u128; m + 1]; n + 1];
    let mut sums = Vec::with_capacity(n + 1);
    {
        let row = &mut alpha[0];
        row[0] = one;
        for j in 1..=hi(0) {
            row[j] = released(row[j - 1] * w);
        }
        let c: u128 = row.iter().sum();
        if c == 0 {
            return Err(TemperatureRefusal::Released { row: 0 });
        }
        for v in row.iter_mut() {
            *v = nearest(*v << SWEEP_BITS, c);
        }
        sums.push(c);
    }
    for i in 1..=n {
        let mut row = vec![0u128; m + 1];
        let pv = p(i - 1, void);
        for j in lo(i)..=hi(i) {
            let mut a = released(alpha[i - 1][j] * pv);
            if j > 0 {
                a += released(alpha[i - 1][j - 1] * p(i - 1, target[j - 1]));
                if omit.is_some() {
                    a += released(row[j - 1] * w);
                }
            }
            row[j] = a;
        }
        let c: u128 = row.iter().sum();
        if c == 0 {
            return Err(TemperatureRefusal::Released { row: i });
        }
        for v in row.iter_mut() {
            *v = nearest(*v << SWEEP_BITS, c);
        }
        sums.push(c);
        alpha[i] = row;
    }
    let end = alpha[n][m];
    if end == 0 {
        return Err(TemperatureRefusal::Released { row: n });
    }
    let code = -(sums.iter().map(|&c| log2_ratio(c)).sum::<i128>() + log2_ratio(end));
    // The suffix sweep: rows n..=0, normalized alike.
    let mut beta = vec![vec![0u128; m + 1]; n + 1];
    {
        let row = &mut beta[n];
        row[m] = one;
        if omit.is_some() {
            for j in (0..m).rev() {
                row[j] = released(row[j + 1] * w);
            }
        }
        let c: u128 = row.iter().sum();
        for v in row.iter_mut() {
            *v = nearest(*v << SWEEP_BITS, c);
        }
    }
    for i in (0..n).rev() {
        let mut row = vec![0u128; m + 1];
        let pv = p(i, void);
        for j in (lo(i)..=hi(i)).rev() {
            let mut b = released(beta[i + 1][j] * pv);
            if j < m {
                b += released(beta[i + 1][j + 1] * p(i, target[j]));
                if omit.is_some() {
                    b += released(row[j + 1] * w);
                }
            }
            row[j] = b;
        }
        let c: u128 = row.iter().sum();
        if c == 0 {
            return Err(TemperatureRefusal::Released { row: i });
        }
        for v in row.iter_mut() {
            *v = nearest(*v << SWEEP_BITS, c);
        }
        beta[i] = row;
    }
    // The posterior, place by place: contact (i, j) is α(i−1, j−1) p̂_i(t_j) β(i, j), the void α(i−1, j) p̂_i(void) β(i, j).
    let share = 1u128 << SHARE_BITS_T;
    let mut placed = Vec::with_capacity(n);
    let mut lag = Vec::with_capacity(n);
    for i in 1..=n {
        let pv = p(i - 1, void);
        let mut contact = vec![0u128; m + 1];
        let mut total = 0u128;
        for j in 0..=m {
            let v = released(released(alpha[i - 1][j] * pv) * beta[i][j]);
            total += v;
            if j > 0 {
                let c = released(released(alpha[i - 1][j - 1] * p(i - 1, target[j - 1])) * beta[i][j]);
                contact[j] = c;
                total += c;
            }
        }
        if total == 0 {
            return Err(TemperatureRefusal::Released { row: i });
        }
        let mut by_class: Vec<(usize, u64)> = Vec::new();
        let (mut mass, mut moment) = (0u64, 0i64);
        for j in 1..=m {
            if contact[j] == 0 {
                continue;
            }
            let g = nearest(contact[j] * share, total) as u64;
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
        let rest = (share as u64).saturating_sub(mass);
        by_class.push((void, rest));
        placed.push(by_class);
        lag.push((mass, moment));
    }
    Ok(CouplingCode { code: code as i64, placed, lag })
}

#[cfg(test)]
mod tests {
    use super::*;
    use std::collections::BTreeSet;

    // ---- The coupling at temperature one (#601) ----

    /// A face from weights over the classes (masses at 2^40 each unit), its total their sum.
    fn face(weights: &[u128]) -> (Vec<u128>, u128) {
        let masses: Vec<u128> = weights.iter().map(|&w| w << 40).collect();
        let total = masses.iter().sum();
        (masses, total)
    }

    fn view(faces: &[(Vec<u128>, u128)]) -> Vec<(&[u128], u128)> {
        faces.iter().map(|(m, t)| (m.as_slice(), *t)).collect()
    }

    /// `−log₂(m/t)` on 2^(−20), the field's own reading of a face's code.
    fn bits(m: u128, t: u128) -> i64 {
        crate::hnn::tower::face_code(m, t)
    }

    /// `log₂ v` on 2^(−20) for a whole `v ≥ 1`: its width, and its leading 63 bits read by [`log2_ratio`].
    fn log2_whole(v: &BigUint) -> i128 {
        let width = v.bits();
        let top: u128 = if width > 63 { (v >> (width - 63)).try_into().unwrap() } else { u128::try_from(v.clone()).unwrap() << (63 - width) };
        ((width as i128 - 1) << CODE_BITS) + log2_ratio(top)
    }

    /// The place-wise code: each cell at its own place, every later place the void.
    fn place_wise(faces: &[(Vec<u128>, u128)], void: usize, target: &[usize]) -> i64 {
        faces.iter().enumerate().map(|(i, (m, t))| bits(m[target.get(i).copied().unwrap_or(void)], *t)).sum()
    }

    /// A sharp face on `class` among `classes` (one part in 2^20 spread over the rest).
    fn sharp(class: usize, classes: usize) -> (Vec<u128>, u128) {
        face(&(0..classes).map(|c| if c == class { 1u128 << 20 } else { 1 }).collect::<Vec<_>>())
    }

    #[test]
    fn with_as_many_places_as_cells_the_coupling_is_the_place_wise_code() {
        let faces: Vec<_> = [[3u128, 1, 2, 5], [1, 4, 1, 1], [2, 2, 7, 1]].iter().map(|w| face(w)).collect();
        let target = [1usize, 1, 2];
        let read = coupling_code(&view(&faces), 0, &target, None).unwrap();
        assert!((read.code - place_wise(&faces, 0, &target)).abs() <= 8, "{} against {}", read.code, place_wise(&faces, 0, &target));
        for (i, placed) in read.placed.iter().enumerate() {
            assert_eq!(placed, &vec![(target[i], 1u64 << 24), (0, 0)], "place {i}");
        }
        assert!(read.lag.iter().all(|&(mass, lag)| mass == 1 << 24 && lag == 0));
    }

    /// A code: every target the places can write (each place a class or the void) has its coupling `Z(T | H)`, read
    /// here by enumerating every writing in exact rationals; the `Z` of every target sum to one exactly (each writing maps
    /// to one target once its voids are dropped), and each coupling's code is `−log₂ Z` to a few grains of its reading.
    #[test]
    fn the_coupling_is_a_code() {
        use num_rational::BigRational;
        let weights: [[u128; 3]; 3] = [[2, 1, 3], [1, 1, 1], [4, 1, 2]];
        let faces: Vec<_> = weights.iter().map(|w| face(w)).collect();
        // Z(T | H) by enumeration: every writing of the three places, its voids dropped.
        let mut z: std::collections::BTreeMap<Vec<usize>, BigRational> = std::collections::BTreeMap::new();
        for writing in 0..27usize {
            let classes: Vec<usize> = (0..3).map(|i| writing / 3usize.pow(i as u32) % 3).collect();
            let p = classes.iter().enumerate().fold(BigRational::from_integer(1.into()), |acc, (i, &c)| acc * BigRational::new((weights[i][c]).into(), weights[i].iter().sum::<u128>().into()));
            let target: Vec<usize> = classes.into_iter().filter(|&c| c != 0).collect();
            *z.entry(target).or_insert_with(|| BigRational::from_integer(0.into())) += p;
        }
        assert_eq!(z.values().fold(BigRational::from_integer(0.into()), |a, b| a + b), BigRational::from_integer(1.into()));
        for (target, zt) in &z {
            let read = coupling_code(&view(&faces), 0, target, None).unwrap();
            let (num, den) = (zt.numer().to_biguint().unwrap(), zt.denom().to_biguint().unwrap());
            let exact = log2_whole(&den) - log2_whole(&num);
            assert!((read.code as i128 - exact).abs() <= 16, "{target:?}: {} against {exact}", read.code);
        }
        let mut targets: Vec<Vec<usize>> = vec![vec![]];
        for len in 1..=3usize {
            let mut next = Vec::new();
            for t in targets.iter().filter(|t| t.len() == len - 1) {
                for c in 1..3 {
                    let mut u = t.clone();
                    u.push(c);
                    next.push(u);
                }
            }
            targets.extend(next);
        }
        assert_eq!(targets.iter().filter(|t| z.contains_key(*t)).count(), z.len(), "every target the places write is read");
    }

    #[test]
    fn the_coupling_is_never_worse_than_the_place() {
        let faces: Vec<_> = [[3u128, 1, 2, 5], [1, 4, 1, 1], [2, 2, 7, 1], [5, 1, 1, 1], [1, 1, 1, 9]].iter().map(|w| face(w)).collect();
        for target in [vec![1usize, 2], vec![3, 3, 3], vec![2, 1, 3, 1], vec![1, 1, 2, 2, 3]] {
            let read = coupling_code(&view(&faces), 0, &target, None).unwrap();
            assert!(read.code <= place_wise(&faces, 0, &target) + 8, "{target:?}");
        }
    }

    /// [the comparison record §3.5] **The witness**: a release equal to its target one place late, and one with a byte
    /// inserted, are charged their slip alone by the coupling where the place-wise code charges every byte after it,
    /// and the lag field reads `+1` after the slip; one with a byte deleted is charged its slip alone where a cell may be
    /// omitted (the lock face), and reads `−1` after it. The place-wise code charges each.
    #[test]
    fn the_witness_one_late_one_inserted_one_deleted() {
        let (classes, void) = (6usize, 0usize);
        let target = [1usize, 2, 3, 4, 5, 1, 2, 3];
        let slip = 8 * (1i64 << 20); // eight bits: a slip costs about log₂ of the face's sharpness (20 bits), well under it
        // One place late: a leading void, then the target.
        let late: Vec<_> = std::iter::once(void).chain(target.iter().copied()).map(|c| sharp(c, classes)).collect();
        let read = coupling_code(&view(&late), void, &target, None).unwrap();
        assert!(read.code < 4 * (1i64 << 20), "late: {}", read.code);
        assert!(place_wise(&late, void, &target) > (target.len() as i64 - 1) * slip, "the place charges every byte after the slip");
        assert!(read.lag[2..].iter().all(|&(mass, lag)| mass > (1 << 24) - 64 && (lag - (1 << 24)).abs() < 64), "lag +1 after the slip");
        // One byte inserted (a 9 after the third cell): n = m + 1.
        let mut inserted: Vec<usize> = target.to_vec();
        inserted.insert(3, 5);
        let faces: Vec<_> = inserted.iter().map(|&c| sharp(c, classes)).collect();
        let read = coupling_code(&view(&faces), void, &target, None).unwrap();
        assert!(read.code < 24 * (1i64 << 20), "inserted: the slip alone, {}", read.code);
        assert!(place_wise(&faces, void, &target) > 4 * slip);
        assert!(read.lag[4..].iter().all(|&(_, lag)| (lag - (1 << 24)).abs() < 1 << 12), "lag +1 after the insertion");
        // One byte deleted (the fourth cell), the release padded with a void place: omissions at a declared cost.
        let mut deleted: Vec<usize> = target.to_vec();
        deleted.remove(3);
        deleted.push(void);
        let faces: Vec<_> = deleted.iter().map(|&c| sharp(c, classes)).collect();
        let omit = 3 * (1i64 << 20);
        let read = coupling_code(&view(&faces), void, &target, Some(omit)).unwrap();
        assert!(read.code < omit + 4 * (1i64 << 20), "deleted: the slip alone, {}", read.code);
        assert!(place_wise(&faces, void, &target) > 4 * slip);
        assert!(read.lag[3..7].iter().all(|&(_, lag)| (lag + (1 << 24)).abs() < 1 << 12), "lag −1 after the deletion: {:?}", read.lag);
    }

    #[test]
    fn the_coupling_refuses_what_it_cannot_read() {
        let faces: Vec<_> = [[1u128, 1], [1, 1]].iter().map(|w| face(w)).collect();
        assert_eq!(coupling_code(&view(&faces), 0, &[1, 1, 1], None), Err(TemperatureRefusal::Short { cells: 3, places: 2 }));
        assert_eq!(coupling_code(&view(&faces), 0, &[0], None), Err(TemperatureRefusal::VoidCell));
        assert_eq!(coupling_code(&view(&faces), 0, &[2], None), Err(TemperatureRefusal::Face));
    }

    type Choice = Vec<(usize, usize)>;

    // Independent exhaustive enumeration of all increasing chains of equal contacts;
    // no prefix/suffix dynamic-programming recurrence is used in this oracle.
    fn brute(h: &[u8], t: &[u8]) -> BTreeSet<Choice> {
        fn visit(
            h: &[u8],
            t: &[u8],
            i: usize,
            j: usize,
            chain: &mut Choice,
            choices: &mut BTreeSet<Choice>,
        ) {
            choices.insert(chain.clone());
            for a in i..h.len() {
                for b in j..t.len() {
                    if h[a] == t[b] {
                        chain.push((a, b));
                        visit(h, t, a + 1, b + 1, chain, choices);
                        chain.pop();
                    }
                }
            }
        }
        let mut choices = BTreeSet::new();
        visit(h, t, 0, 0, &mut Vec::new(), &mut choices);
        let longest = choices.iter().map(Vec::len).max().unwrap();
        choices.into_iter().filter(|c| c.len() == longest).collect()
    }

    fn contact_set(q: &Coupling) -> BTreeSet<(usize, usize)> {
        q.plural_optimal_contacts
            .iter()
            .map(|c| (c.h_index, c.t_index))
            .collect()
    }

    fn plateau_set(q: &Coupling) -> BTreeSet<(usize, usize, usize, usize)> {
        q.maximal_contiguous_plateaus
            .iter()
            .map(|p| (p.h_start, p.t_start, p.length, p.first_rank))
            .collect()
    }

    fn check(h: &[u8], t: &[u8]) {
        let q = coupling(h, t).unwrap();
        let choices = brute(h, t);
        let lambda = choices.first().unwrap().len();
        let union: BTreeSet<_> = choices.iter().flatten().copied().collect();
        assert_eq!(q.lambda, lambda, "{h:?} {t:?}");
        assert_eq!(q.least_friction, h.len() + t.len() - 2 * lambda);
        assert_eq!(q.unresolved_h_per_optimum, h.len() - lambda);
        assert_eq!(q.unresolved_t_per_optimum, t.len() - lambda);
        assert_eq!(contact_set(&q), union);
        for c in &q.plural_optimal_contacts {
            for choice in choices
                .iter()
                .filter(|v| v.contains(&(c.h_index, c.t_index)))
            {
                assert_eq!(
                    choice
                        .iter()
                        .position(|v| *v == (c.h_index, c.t_index))
                        .unwrap()
                        + 1,
                    c.rank_on_any_optimal_coupling
                );
            }
        }
        let may_h: BTreeSet<_> = choices
            .iter()
            .flat_map(|c| (0..h.len()).filter(move |i| !c.iter().any(|(a, _)| a == i)))
            .collect();
        let may_t: BTreeSet<_> = choices
            .iter()
            .flat_map(|c| (0..t.len()).filter(move |j| !c.iter().any(|(_, b)| b == j)))
            .collect();
        assert_eq!(
            q.may_be_unresolved_h_indices,
            may_h.iter().copied().collect::<Vec<_>>()
        );
        assert_eq!(
            q.may_be_unresolved_t_indices,
            may_t.iter().copied().collect::<Vec<_>>()
        );
        assert_eq!(
            q.always_held_h_indices,
            (0..h.len())
                .filter(|i| !may_h.contains(i))
                .collect::<Vec<_>>()
        );
        assert_eq!(
            q.always_held_t_indices,
            (0..t.len())
                .filter(|j| !may_t.contains(j))
                .collect::<Vec<_>>()
        );
        assert_eq!(
            q.never_held_h_indices,
            (0..h.len())
                .filter(|i| !union.iter().any(|(a, _)| a == i))
                .collect::<Vec<_>>()
        );
        assert_eq!(
            q.never_held_t_indices,
            (0..t.len())
                .filter(|j| !union.iter().any(|(_, b)| b == j))
                .collect::<Vec<_>>()
        );
        let mut covered = BTreeSet::new();
        for p in &q.maximal_contiguous_plateaus {
            let members: BTreeSet<_> = (0..p.length)
                .map(|k| (p.h_start + k, p.t_start + k))
                .collect();
            assert!(
                choices
                    .iter()
                    .any(|c| members.iter().all(|v| c.contains(v))),
                "plateau must fit one optimum"
            );
            assert!(
                p.h_start == 0
                    || p.t_start == 0
                    || !union.contains(&(p.h_start - 1, p.t_start - 1))
            );
            assert!(!union.contains(&(p.h_start + p.length, p.t_start + p.length)));
            for member in members {
                assert!(covered.insert(member));
            }
        }
        assert_eq!(covered, union);
        let swap = coupling(t, h).unwrap();
        assert_eq!(
            (swap.lambda, swap.least_friction),
            (q.lambda, q.least_friction)
        );
        assert_eq!(
            contact_set(&swap),
            union.iter().map(|&(i, j)| (j, i)).collect()
        );
        assert_eq!(
            plateau_set(&swap),
            plateau_set(&q)
                .iter()
                .map(|&(i, j, n, rank)| (j, i, n, rank))
                .collect()
        );
        let hr: Vec<_> = h.iter().rev().copied().collect();
        let tr: Vec<_> = t.iter().rev().copied().collect();
        let reverse = coupling(&hr, &tr).unwrap();
        assert_eq!(
            (reverse.lambda, reverse.least_friction),
            (q.lambda, q.least_friction)
        );
        assert_eq!(
            contact_set(&reverse),
            union
                .iter()
                .map(|&(i, j)| (h.len() - 1 - i, t.len() - 1 - j))
                .collect()
        );
        assert_eq!(
            plateau_set(&reverse),
            plateau_set(&q)
                .iter()
                .map(|&(i, j, n, rank)| (
                    h.len() - i - n,
                    t.len() - j - n,
                    n,
                    lambda + 2 - rank - n
                ))
                .collect()
        );
        assert_eq!(
            reverse.may_be_unresolved_h_indices,
            may_h
                .iter()
                .rev()
                .map(|&i| h.len() - 1 - i)
                .collect::<Vec<_>>()
        );
        assert_eq!(
            reverse.may_be_unresolved_t_indices,
            may_t
                .iter()
                .rev()
                .map(|&j| t.len() - 1 - j)
                .collect::<Vec<_>>()
        );
    }

    #[test]
    fn bounded_exhaustive_plural_contacts_unresolved_and_symmetries() {
        // Same bounded population as the validated Python reader: 31 words, 961 pairs.
        let words: Vec<Vec<u8>> = (0..=4)
            .flat_map(|n| {
                (0..(1usize << n))
                    .map(move |bits| (0..n).map(|i| ((bits >> i) & 1) as u8).collect())
            })
            .collect();
        assert_eq!(words.len(), 31);
        for h in &words {
            for t in &words {
                check(h, t);
            }
        }
    }

    #[test]
    fn named_plural_crossing_stutter_and_disjoint_cases() {
        for (h, t, lambda, friction) in [
            (vec![], vec![], 0, 0),
            (vec![], vec![1, 2], 0, 2),
            (vec![1, 2, 3], vec![1, 2, 3], 3, 0),
            (vec![1, 1, 2], vec![1, 2], 2, 1),
            (vec![1, 2, 3], vec![1, 4, 3], 2, 2),
            (vec![1, 2], vec![2, 1], 1, 2),
            (vec![1, 3, 2, 4], vec![1, 2, 3, 4], 3, 2),
            (vec![1, 1], vec![2, 2], 0, 4),
        ] {
            check(&h, &t);
            let q = coupling(&h, &t).unwrap();
            assert_eq!((q.lambda, q.least_friction), (lambda, friction));
        }
        let stutter = coupling(&[1, 1, 2], &[1, 2]).unwrap();
        assert_eq!(stutter.plural_optimal_contacts.len(), 3);
        assert_eq!(stutter.may_be_unresolved_h_indices, [0, 1]);
        assert_eq!(stutter.always_held_h_indices, [2]);
        let crossing = coupling(&[1, 2], &[2, 1]).unwrap();
        assert_eq!(crossing.plural_optimal_contacts.len(), 2);
        assert_eq!(crossing.lambda, 1);
        assert_eq!(crossing.maximal_contiguous_plateaus.len(), 2);
        assert!(!coupling::<u8>(&[], &[]).unwrap().nonempty_zero_friction);
        assert!(coupling(&[1], &[1]).unwrap().nonempty_zero_friction);
    }

    #[test]
    fn declared_class_chart_preserves_zero_octet_and_refuses_internal_end() {
        let whole = [0, 16, 0, 0];
        assert_eq!(
            payload32(&whole, Strand::H).unwrap(),
            Payload32 {
                cells: &[0, 16],
                framing_end_present: true
            }
        );
        assert_eq!(payload32(&[5], Strand::T).unwrap().cells, [5]);
        assert_eq!(coupling32(&whole, &whole).unwrap().coupling.lambda, 2);
        assert!(matches!(
            payload32(&[0, 0, 3, 16], Strand::H),
            Err(CouplingRefusal::InternalEnd {
                strand: Strand::H,
                index: 0
            })
        ));
        assert!(matches!(
            payload32(&[32], Strand::T),
            Err(CouplingRefusal::Class {
                strand: Strand::T,
                index: 0,
                class: 32
            })
        ));
        assert!(matches!(
            payload32(&[0, 0, 0], Strand::T),
            Err(CouplingRefusal::InternalEnd { .. })
        ));
    }

    // Static supplied chart sections; this helper represents integers, never advances a Field.
    fn phase(lift: BigInt, radices: &[BigUint]) -> LockPhase {
        let modulus: BigUint = radices.iter().product();
        let n = BigInt::from(modulus.clone());
        let mut residue = &lift % &n;
        if residue.sign() == Sign::Minus {
            residue += &n;
        }
        let winding = (&lift - &residue) / &n;
        let value = residue.to_biguint().unwrap();
        let mut rest = value.clone();
        let digits = radices
            .iter()
            .map(|d| {
                let digit = &rest % d;
                rest /= d;
                digit
            })
            .collect();
        LockPhase {
            digits,
            value,
            lift,
            winding,
        }
    }

    fn path(values: &[i64], radices: &[BigUint]) -> Vec<LockPhase> {
        values
            .iter()
            .map(|&v| phase(BigInt::from(v), radices))
            .collect()
    }

    fn radices() -> Vec<BigUint> {
        vec![2u8.into(), 3u8.into()]
    }

    #[test]
    fn actual_lock_phase_splits_changes_and_retains_both_carry_series() {
        let r = radices();
        let q = coupling(&[1, 2, 3], &[1, 2, 3]).unwrap();
        let h = path(&[-1, 0, 2, 3], &r);
        let t = path(&[0, 1, 2, 4], &r);
        let lock = annotate_lock_phases(&q, &r, &h, &t).unwrap();
        assert_eq!(q.maximal_contiguous_plateaus.len(), 1);
        assert_eq!(
            lock.plateaus.iter().map(|p| p.length).collect::<Vec<_>>(),
            [2, 1]
        );
        let first = &lock.plateaus[0];
        assert_eq!(first.delta.z_lift, BigInt::from(-1));
        assert_eq!(first.delta.residue, BigUint::from(5u8));
        assert_eq!(first.delta.whole_winding, BigInt::from(-1));
        assert_eq!(first.delta.digits, [BigUint::from(1u8), BigUint::from(2u8)]);
        assert_eq!(
            first
                .carries
                .iter()
                .map(|c| c.h_winding.clone())
                .collect::<Vec<_>>(),
            [BigInt::from(-1), BigInt::zero()]
        );
        assert_eq!(lock.plateaus[1].delta.z_lift, BigInt::zero());
        assert_eq!(lock.plateaus[1].first_rank, 3);
        assert_eq!(lock.end_delta.z_lift, BigInt::from(-1));
        // Modulo equality must not erase a genuine difference in the Z lift.
        let q = coupling(&[1, 2], &[1, 2]).unwrap();
        let lock =
            annotate_lock_phases(&q, &r, &path(&[0, 6, 7], &r), &path(&[0, 0, 1], &r)).unwrap();
        assert_eq!(lock.plateaus.len(), 2);
        assert!(lock.plateaus.iter().all(|p| p.delta.residue.is_zero()));
        assert_eq!(lock.plateaus[1].delta.whole_winding, BigInt::one());
    }

    #[test]
    fn a_reordering_cancels_at_the_end_but_not_at_each_intermediate_plateau() {
        // A(a)=1, A(b)=2 in Z/6, same initial key. Cell-order lag cannot replace V_H-V_T.
        let r = radices();
        let q = coupling(&[1, 2], &[2, 1]).unwrap();
        let lock =
            annotate_lock_phases(&q, &r, &path(&[0, 1, 3], &r), &path(&[0, 2, 3], &r)).unwrap();
        assert_eq!(lock.end_delta.z_lift, BigInt::zero());
        assert_eq!(
            lock.plateaus
                .iter()
                .map(|p| p.delta.z_lift.clone())
                .collect::<Vec<_>>(),
            [BigInt::from(-2), BigInt::from(1)]
        );
        assert_eq!(q.lambda, 1);
        assert_eq!(lock.plateaus.len(), 2); // Both incompatible alternatives remain.
    }

    #[test]
    fn phase_uses_unbounded_lifts_and_swap_negates_the_actual_difference() {
        let r = radices();
        let q = coupling(&[1], &[1]).unwrap();
        let large: BigInt = (BigInt::one() << 256usize) + BigInt::from(17u8);
        let h = vec![phase(large.clone(), &r), phase(&large + 1, &r)];
        let t = path(&[-5, -4], &r);
        let forward = annotate_lock_phases(&q, &r, &h, &t).unwrap();
        let backward = annotate_lock_phases(&q, &r, &t, &h).unwrap();
        assert_eq!(forward.end_delta.z_lift, &large + 5);
        assert_eq!(backward.end_delta.z_lift, -&forward.end_delta.z_lift);
        for delta in [&forward.end_delta, &backward.end_delta] {
            assert_eq!(
                delta.z_lift,
                BigInt::from(delta.residue.clone())
                    + BigInt::from(forward.modulus.clone()) * &delta.whole_winding
            );
        }
    }

    #[test]
    fn native_j1_field_paths_supply_every_plural_plateau_without_a_second_clock() {
        use crate::geometry::solenoid::field::FieldSolenoid;
        use crate::hnn::field::{Field, FieldDeclaration};

        let field = Field::declare(FieldDeclaration::campaign_one(1 << 17)).unwrap();
        let chart = FieldSolenoid::from_field(&field).unwrap();
        let key: Vec<_> = field.rings().iter().map(|_| BigInt::one()).collect();
        let h = [0, 1, 0, 1];
        let t = [0, 1];
        let hp: Vec<_> = chart
            .phase_path(&field, &key, &h)
            .unwrap()
            .into_iter()
            .map(|p| p.lock)
            .collect();
        let tp: Vec<_> = chart
            .phase_path(&field, &key, &t)
            .unwrap()
            .into_iter()
            .map(|p| p.lock)
            .collect();
        let q = coupling(&h, &t).unwrap();
        let read = annotate_lock_phases(&q, chart.lock_radices(), &hp, &tp).unwrap();
        assert_eq!(q.lambda, 2);
        assert_eq!(q.least_friction, 2);
        assert_eq!(read.plateaus.len(), 2);
        assert!(read.plateaus.iter().all(|p| p.length == 2));
        assert_eq!(
            read.plateaus.iter().map(|p| p.length).sum::<usize>(),
            q.plural_optimal_contacts.len()
        );
        for p in &read.plateaus {
            for k in 0..p.length {
                assert_eq!(
                    p.delta.z_lift,
                    &hp[p.h_start + k].lift - &tp[p.t_start + k].lift
                );
            }
        }
        let skipped_sum =
            chart.class_increment(&field, 0).unwrap() + chart.class_increment(&field, 1).unwrap();
        assert_eq!(read.end_delta.z_lift, BigInt::from(skipped_sum));
    }

    #[test]
    fn actual_phase_chart_refuses_shape_digit_and_lift_defects() {
        let r = radices();
        let q = coupling(&[1], &[1]).unwrap();
        let good = path(&[0, 1], &r);
        assert!(matches!(
            annotate_lock_phases(&q, &r, &good[..1], &good),
            Err(CouplingRefusal::PhaseShape {
                strand: Strand::H,
                expected: 2,
                actual: 1
            })
        ));
        assert!(matches!(
            annotate_lock_phases(&q, &[], &good, &good),
            Err(CouplingRefusal::Phase {
                reason: PhaseDefect::DigitArity,
                ..
            })
        ));
        let no_lock = vec![phase(BigInt::zero(), &[]), phase(BigInt::zero(), &[])];
        let identity = annotate_lock_phases(&q, &[], &no_lock, &no_lock).unwrap();
        assert_eq!(identity.modulus, BigUint::one());
        assert!(identity.end_delta.digits.is_empty());
        assert!(matches!(
            annotate_lock_phases(&q, &[BigUint::zero()], &good, &good),
            Err(CouplingRefusal::ZeroRadix { level: 0 })
        ));
        for defect in [
            PhaseDefect::DigitArity,
            PhaseDefect::DigitRange,
            PhaseDefect::DigitValue,
            PhaseDefect::ValueRange,
            PhaseDefect::Lift,
        ] {
            let mut bad = good.clone();
            match defect {
                PhaseDefect::DigitArity => {
                    bad[0].digits.pop();
                }
                PhaseDefect::DigitRange => {
                    bad[0].digits[0] = 2u8.into();
                }
                PhaseDefect::DigitValue => {
                    bad[0].digits[0] = 1u8.into();
                }
                PhaseDefect::ValueRange => {
                    bad[0].value = 6u8.into();
                }
                PhaseDefect::Lift => {
                    bad[0].lift = BigInt::one();
                }
            }
            assert_eq!(
                annotate_lock_phases(&q, &r, &good, &bad),
                Err(CouplingRefusal::Phase {
                    strand: Strand::T,
                    index: 0,
                    reason: defect
                })
            );
        }
        let mut bad = q.clone();
        bad.maximal_contiguous_plateaus[0].length = 2;
        assert!(matches!(
            annotate_lock_phases(&bad, &r, &good, &good),
            Err(CouplingRefusal::ContactShape)
        ));
        // Empty replies still carry their independently supplied terminal section.
        let empty = coupling::<u8>(&[], &[]).unwrap();
        let reading = annotate_lock_phases(&empty, &r, &path(&[-1], &r), &path(&[3], &r)).unwrap();
        assert!(reading.plateaus.is_empty());
        assert_eq!(reading.end_delta.z_lift, BigInt::from(-4));
    }
}
