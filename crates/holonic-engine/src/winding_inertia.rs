//! Inertia returned as **windings**: every passage of a circulant form named by how far it turns.
//!
//! ## Why this exists
//!
//! [`crate::inertia`] computes the split `(positive, zero, negative)` correctly, by elimination,
//! with no trigonometry anywhere. What it returns is a *count of signs*, and `CLAUDE.md` §2b strikes
//! that reading:
//!
//! > *"What the signed floor signs is the PASSAGE, never the state."* — Brandon, 2026-08-08
//!
//! > **A count of signs is a state reading. Name the windings instead.** Where a form carries a
//! > cyclic or circulant symmetry its inertia factors through the character group and every negative
//! > direction has a name — its winding number — so the lawful return is *these nine passages, each
//! > labelled by how far it winds*, never *nine negative directions*.
//!
//! Holomorphically `−1 = e^{iπ}`. There is no separate species of quantity called negative; there is
//! rotation, and a sign is what remains of a phase once the winding has been deleted. This module
//! declines to delete it.
//!
//! ## The mechanism, and why the symmetry is what makes the naming possible
//!
//! A circulant `C = circ(c_0, …, c_{n−1})` commutes with the cyclic shift, so its eigendirections
//! are the characters of `Z/n` and nothing else. The eigenvalue at character `k` is the **symbol**
//! evaluated at an `n`-th root of unity,
//!
//! ```text
//!   λ_k = Σ_j c_j ω^{jk},        ω = e^{2πi/n},        f(x) = Σ_j c_j x^j
//! ```
//!
//! and for a *symmetric* circulant (`c_j = c_{n−j}`) the conjugate terms pair off, leaving a real
//! integer combination of the star-polygon values `β_m = 2cos(2πm/n)`. The inertia therefore
//! **factors through the character group**: the sign of a direction is determined by `k` alone, and
//! `k` is a winding. That is the whole content of the module.
//!
//! For the cycle's own adjacency, `c = e_1 + e_{n−1}`, this collapses to `λ_k = β_k` and the law
//! becomes the measured one:
//!
//! ```text
//!   2cos(2πk/n) < 0   ⟺   2πk/n > π/2   ⟺   the step exceeds ONE QUARTER TURN
//! ```
//!
//! so the eigenvalue's sign *is* the winding of its star polygon `{n/k}` past the hand, and the null
//! directions sit at exactly `k/n = 1/4` and `3/4`, present exactly when `4 | n`. The form returns
//! nothing precisely at the hand.
//!
//! ## The exactness route taken, and why
//!
//! **Exact algebraic, with an exact rational special case where Niven's theorem supplies one.** No
//! float, no tolerance, no epsilon, and no transcendental evaluation.
//!
//! 1. **The star table.** `β_m = 2cos(2πm/n)` for `m = 0..=n/2` are the distinct real roots of the
//!    squarefree part of `D_n(x) − 2`, where `D_n` is the Dickson polynomial with
//!    `D_n(z + z^{-1}) = z^n + z^{-n}`. Those roots are isolated by **exact Sturm bisection** through
//!    [`IntegerPolynomial::distinct_root_count`], and `β_m` is strictly decreasing in `m`, so the
//!    descending order of the isolated intervals *is* the labelling by `m`. This drives the
//!    Sturm/`AlgebraicRoot` carrier, which `CLAUDE.md` §11 measured at **zero drivers** in any
//!    `examples/`, `tests/` or `bin/` path.
//! 2. **The rational special case.** By Niven's theorem `2cos(2πm/n)` is rational exactly when
//!    `n/gcd(m,n) ∈ {1,2,3,4,6}`, with values `2, −2, −1, 0, 1`. Those entries are stored as exact
//!    points, never refined — and each is **cross-checked against the interval Sturm isolated
//!    independently**, so the two routes to the star table have to agree ([`WindingError::
//!    NivenDisagreesWithSturm`]).
//! 3. **The null decision is exact and finite, never a limit.** Interval refinement can prove
//!    `λ_k ≠ 0`; it can never prove `λ_k = 0`. So nullity is decided algebraically instead:
//!    `ω^k` is a *primitive* `d`-th root of unity for `d = n/gcd(k,n)`, its minimal polynomial over
//!    `Q` is the cyclotomic `Φ_d`, and therefore
//!
//!    ```text
//!      λ_k = f(ω^k) = 0   ⟺   Φ_d divides f
//!    ```
//!
//!    which is one exact polynomial division. The quotient is retained as the witness. `Φ_d` is the
//!    star polygon `{n/k}` in lowest terms, so the null test literally asks *whether this passage's
//!    own star polygon divides the form*.
//! 4. **The hand.** For a passage the cyclotomic test has already proved nonzero, the star-table
//!    intervals are combined by exact rational interval arithmetic and refined until the enclosure
//!    is strictly on one side of zero. Termination is guaranteed because the value is known nonzero
//!    *before* the refinement starts.
//! 5. **The certificate.** The enclosure is then handed to [`AlgebraicRoot::isolate`] against the
//!    **characteristic polynomial** `det(xI − C)`, computed by Faddeev–LeVerrier over exact
//!    rationals. That computation knows nothing about `n`, `k`, characters or roots of unity: it is
//!    a determinant. So the returned certificate is a Sturm proof that an interval derived from
//!    *character arithmetic* isolates exactly one root of a polynomial derived from a *determinant*.
//!
//! ## What is cross-checked against what
//!
//! ```text
//!   character route  ──►  (p, z, q)  ◄──  symmetric elimination      inertia::inertia
//!   character route  ──►  enclosure  ──►  Sturm on det(xI − C)       AlgebraicRoot::isolate
//!   Niven            ──►  β_m        ◄──  Sturm bisection            distinct_root_count
//!   quarter turn     ──►  hand       ◄──  character route            cycle adjacency only
//! ```
//!
//! The elimination is never told `n`, never told `k`, and never shown the first row: it receives a
//! [`SymmetricForm`] of entries. `the_elimination_never_sees_the_symmetry_because_it_agrees_after_a_
//! congruence_destroys_it` proves the independence rather than asserting it — the transported form
//! `P^T C P` is refused by [`SymmetricCirculant::from_symmetric_form`] as **not circulant**, and the
//! elimination still returns the split the characters named.
//!
//! ## The hand is a convention; the split is not
//!
//! §2b: *"`A` and `−A` have swapped inertia, so which side is called positive is a convention — a
//! hand. […] What no frame touches is **the split**."* [`Hand`] is that convention, named rather
//! than assumed, and `the_two_hands_swap_under_negation_while_the_split_does_not` holds this module
//! to it.
//!
//! ## Exactness and governance
//!
//! `Rat` and `BigInt` throughout. The split-point schedule in [`StarTable`] and the refinement
//! counter choose *which exact step to take next* and can never change what is returned — that is
//! measurement, not governance, exactly as [`crate::inertia::PivotOrder`] is.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::exact_value::{AlgebraicRoot, ExactInterval, ExactValueError, IntegerPolynomial};
use crate::grown_cell::GrownComplex;
use crate::inertia::{Inertia, InertiaError, SymmetricForm};

/// How many times the star table may be halved before the construction refuses.
///
/// A bound, not a tolerance: each refinement halves every inexact interval, so this is `2^-64` of
/// the starting width. A construction that has not decided a hand by then has a defect and must say
/// so rather than spin.
const REFINEMENT_APERTURE: usize = 64;

/// How deep the isolating bisection may go before it refuses.
const ISOLATION_APERTURE: usize = 64;

// ===============================================================================================
// the form

/// A symmetric circulant, validated at construction.
///
/// **A matrix that is not circulant is refused by type.** There is no constructor that accepts an
/// arbitrary matrix and symmetrizes, wraps, or averages it: [`SymmetricCirculant::
/// from_symmetric_form`] returns [`WindingError::NotCirculant`] naming the first entry that does not
/// depend only on `(column − row) mod n`, and [`SymmetricCirculant::from_first_row`] returns
/// [`WindingError::NotReversalSymmetric`] naming the first step at which `c_j ≠ c_{n−j}`. Everything
/// downstream may therefore assume the character decomposition without re-checking it.
///
/// Reversal symmetry is exactly the condition that makes the eigenvalues real. A circulant that is
/// not reversal-symmetric is a perfectly good operator with a perfectly good spectrum; it simply
/// has no inertia, because it is not a symmetric bilinear form.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SymmetricCirculant {
    first_row: Vec<Rat>,
}

impl SymmetricCirculant {
    pub fn from_first_row(first_row: Vec<Rat>) -> Result<Self, WindingError> {
        let extent = first_row.len();
        if extent == 0 {
            return Err(WindingError::EmptyCirculant);
        }
        for step in 1..extent {
            if first_row[step] != first_row[extent - step] {
                return Err(WindingError::NotReversalSymmetric { step });
            }
        }
        Ok(Self { first_row })
    }

    pub fn from_integers(first_row: &[i64]) -> Result<Self, WindingError> {
        Self::from_first_row(
            first_row
                .iter()
                .map(|entry| Rat::from_integer(BigInt::from(*entry)))
                .collect(),
        )
    }

    /// Read a symmetric form as a circulant, refusing one that is not.
    ///
    /// The refusal is the point. A caller who hands in a form whose entries do not depend only on
    /// the displacement `(column − row) mod n` has a form whose inertia does **not** factor through
    /// any character group, and naming its passages by winding would be a fabrication.
    pub fn from_symmetric_form(form: &SymmetricForm) -> Result<Self, WindingError> {
        let extent = form.extent();
        if extent == 0 {
            return Err(WindingError::EmptyCirculant);
        }
        for row in 0..extent {
            for column in 0..extent {
                let displacement = (column + extent - row) % extent;
                if form.at(row, column) != form.at(0, displacement) {
                    return Err(WindingError::NotCirculant { row, column });
                }
            }
        }
        Self::from_first_row(
            (0..extent)
                .map(|column| form.at(0, column).clone())
                .collect(),
        )
    }

    pub fn extent(&self) -> usize {
        self.first_row.len()
    }

    pub fn first_row(&self) -> &[Rat] {
        &self.first_row
    }

    /// `-C`. §2b's convention test rests on this: negation swaps the two hands and moves no split.
    pub fn negated(&self) -> Self {
        Self {
            first_row: self.first_row.iter().map(|entry| -entry).collect(),
        }
    }

    pub fn as_symmetric_form(&self) -> Result<SymmetricForm, WindingError> {
        let extent = self.extent();
        let rows = (0..extent)
            .map(|row| {
                (0..extent)
                    .map(|column| self.first_row[(column + extent - row) % extent].clone())
                    .collect()
            })
            .collect();
        Ok(SymmetricForm::from_rows(rows)?)
    }

    /// The primitive integral **symbol** `f(x) = Σ_j c_j x^j`, and the positive rational the row was
    /// multiplied by to reach it.
    ///
    /// Scaling a symmetric form by a *positive* rational moves no hand, no null and no split, so
    /// every certificate below may be taken against the integral symbol and read as a statement
    /// about the form itself. The scale is carried in the return rather than discarded, because a
    /// scale silently dropped is exactly the retained-state defect §2b's audit is about.
    ///
    /// The zero circulant has no content to divide out; its scale is one.
    pub fn integral_symbol(&self) -> (Rat, Vec<BigInt>) {
        let mut denominator = BigInt::one();
        for entry in &self.first_row {
            denominator = lcm_integer(&denominator, entry.denom());
        }
        let mut symbol: Vec<BigInt> = self
            .first_row
            .iter()
            .map(|entry| entry.numer() * (&denominator / entry.denom()))
            .collect();
        let mut content = BigInt::zero();
        for entry in &symbol {
            content = gcd_integer(&content, entry);
        }
        if content.is_zero() {
            return (Rat::from_integer(denominator), symbol);
        }
        for entry in &mut symbol {
            *entry /= &content;
        }
        (Rat::new(denominator, content), symbol)
    }
}

// ===============================================================================================
// what is returned

/// The two hands through the fork.
///
/// **Not a `bool` and not `±1`.** A `bool` names neither of its sides, and a signed unit re-reifies
/// the state with a sign on it — which is the move §2b strikes: *"that would re-reify the state with
/// a sign on it. What the signed floor signs is the PASSAGE, never the state: CW/CCW = the two hands
/// through the fork."*
///
/// **Which hand is which is a declared convention.** `A` and `−A` have swapped inertia, so the side
/// called positive is a choice; here [`Hand::WithTheTurn`] is the side on which the form returns a
/// positive value. What no frame touches is the split, and
/// `the_two_hands_swap_under_negation_while_the_split_does_not` is the test of exactly that.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum Hand {
    /// Traversal returns on the form's declared side. For the cycle's adjacency this is the passage
    /// whose star polygon `{n/k}` steps **within** the quarter turn: the traversal still advances
    /// along its own heading.
    WithTheTurn,
    /// Traversal returns on the other side. For the cycle's adjacency the step has passed the
    /// quarter turn and the traversal now opposes its own heading.
    AgainstTheTurn,
}

impl Hand {
    pub const fn reversed(self) -> Self {
        match self {
            Self::WithTheTurn => Self::AgainstTheTurn,
            Self::AgainstTheTurn => Self::WithTheTurn,
        }
    }

    pub const fn name(self) -> &'static str {
        match self {
            Self::WithTheTurn => "with the turn",
            Self::AgainstTheTurn => "against the turn",
        }
    }
}

/// What traversing a passage returns.
///
/// Three cases and not two, and the third is the one that carries the content: §2b reads `Q(v)` as
/// *what traversing `v` returns*, and the null cone as *where traversal returns nothing*. For the
/// cycle's adjacency the null cone sits at exactly `k/n = 1/4` and `3/4` — the form returns nothing
/// precisely at the hand.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum PassageReturn {
    Handed(Hand),
    OnTheNullCone,
}

impl PassageReturn {
    pub const fn hand(self) -> Option<Hand> {
        match self {
            Self::Handed(hand) => Some(hand),
            Self::OnTheNullCone => None,
        }
    }

    pub const fn name(self) -> &'static str {
        match self {
            Self::Handed(hand) => hand.name(),
            Self::OnTheNullCone => "on the null cone",
        }
    }
}

/// The star polygon a character traces: `{points/step}` in lowest terms.
///
/// The `n`-grams on the same vertex set. Character `k` on `Z/n` visits every `g`-th vertex where
/// `g = gcd(k, n)`, so it traces `{(n/g) / (k/g)}` and returns to its start after `n/g` steps. The
/// principal character `k = 0` traces `{1/0}`, the degenerate point: the zero-frequency passage.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct StarPolygon {
    pub points: usize,
    pub step: usize,
}

impl StarPolygon {
    pub fn of(character: usize, extent: usize) -> Self {
        let common = gcd_usize(character, extent);
        Self {
            points: extent / common,
            step: character / common,
        }
    }

    pub fn label(&self) -> String {
        format!("{{{}/{}}}", self.points, self.step)
    }
}

/// The exact, finite witness that a passage lies on the null cone.
///
/// `Φ_order` is the minimal polynomial of `ω^k` over `Q`, and `Φ_order · quotient = symbol` as
/// integer polynomials, so `λ_k = f(ω^k) = Φ_order(ω^k) · quotient(ω^k) = 0`. This is a *proof*,
/// not a limit: no amount of interval refinement can establish that a value is zero, and this
/// module never pretends otherwise.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CyclotomicWitness {
    /// `d = n / gcd(k, n)`: the number of points of the passage's star polygon.
    pub order: usize,
    pub cyclotomic: Vec<BigInt>,
    pub quotient: Vec<BigInt>,
}

impl CyclotomicWitness {
    /// Re-multiply the witness. A certificate that is never checked is a receipt, and §8 grades the
    /// implementation rather than the receipt.
    pub fn verify(&self, symbol: &[BigInt]) -> bool {
        let product = integer_polynomial_product(&self.cyclotomic, &self.quotient);
        let mut expected: Vec<BigInt> = symbol.to_vec();
        while expected.last().is_some_and(Zero::is_zero) {
            expected.pop();
        }
        product == expected
    }
}

/// One eigendirection, named by its winding rather than counted by its sign.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Passage {
    /// The character index `k`. The passage **is** the character `χ_k`.
    pub character: usize,
    /// `k/n`, exact: how far the character winds per step of the cycle.
    pub winding: Rat,
    /// The star polygon `{n/k}` in lowest terms that the character traces.
    pub star_polygon: StarPolygon,
    /// What traversing this passage returns.
    pub returns: PassageReturn,
    /// An exact rational enclosure of the eigenvalue **of the integral symbol**. Strictly on one
    /// side of zero for a handed passage; containing zero for a null one.
    pub scaled_enclosure: ExactInterval,
    /// The Sturm proof that [`Passage::scaled_enclosure`] isolates exactly one root of the
    /// characteristic polynomial `det(xI − C)` — a polynomial computed by a determinant, which knows
    /// nothing of characters or roots of unity.
    pub certificate: AlgebraicRoot,
    /// Present exactly when the passage is on the null cone.
    pub null_witness: Option<CyclotomicWitness>,
}

impl Passage {
    /// The enclosure of this form's own eigenvalue, with the integral scaling divided back out.
    pub fn enclosure(&self, integral_scale: &Rat) -> ExactInterval {
        ExactInterval {
            lower: &self.scaled_enclosure.lower / integral_scale,
            upper: &self.scaled_enclosure.upper / integral_scale,
        }
    }
}

/// The inertia of a circulant form, returned as its passages.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct WindingInertia {
    pub extent: usize,
    /// The positive rational the first row was multiplied by to make the symbol integral. Every
    /// certificate below is taken against the scaled form; a positive scale moves no hand.
    pub integral_scale: Rat,
    /// `f(x) = Σ_j c_j x^j`, primitive and integral.
    pub symbol: Vec<BigInt>,
    /// The squarefree part of `det(xI − C)`, computed by Faddeev–LeVerrier — the polynomial every
    /// [`Passage::certificate`] is isolated against.
    pub characteristic_polynomial: IntegerPolynomial,
    /// One per character, in character order.
    pub passages: Vec<Passage>,
    /// How many times the star table was halved. A measurement of the construction, not of the form.
    pub refinements: usize,
}

impl WindingInertia {
    /// The aggregate split, for comparison with an elimination that never sees the symmetry.
    ///
    /// This is the *only* place a count appears, and it exists so that the naming can be
    /// cross-checked — not so that it can be replaced by the count.
    pub fn split(&self) -> Inertia {
        let mut split = Inertia::default();
        for passage in &self.passages {
            match passage.returns {
                PassageReturn::Handed(Hand::WithTheTurn) => split.positive += 1,
                PassageReturn::Handed(Hand::AgainstTheTurn) => split.negative += 1,
                PassageReturn::OnTheNullCone => split.zero += 1,
            }
        }
        split
    }

    /// The windings of the passages returning a given hand — the artifact §2b asks for, in place of
    /// a count.
    pub fn windings_of(&self, hand: Hand) -> Vec<Rat> {
        self.passages
            .iter()
            .filter(|passage| passage.returns == PassageReturn::Handed(hand))
            .map(|passage| passage.winding.clone())
            .collect()
    }

    /// The windings of the passages that returned against the turn. For the cycle's adjacency these
    /// are exactly the windings strictly between `1/4` and `3/4`.
    pub fn windings_past_the_hand(&self) -> Vec<Rat> {
        self.windings_of(Hand::AgainstTheTurn)
    }

    /// The windings at which the form returns nothing.
    pub fn null_windings(&self) -> Vec<Rat> {
        self.passages
            .iter()
            .filter(|passage| passage.returns == PassageReturn::OnTheNullCone)
            .map(|passage| passage.winding.clone())
            .collect()
    }

    pub fn passage(&self, character: usize) -> Option<&Passage> {
        self.passages.get(character)
    }
}

// ===============================================================================================
// the construction

/// Name every passage of a symmetric circulant by its winding.
pub fn winding_inertia(circulant: &SymmetricCirculant) -> Result<WindingInertia, WindingError> {
    let extent = circulant.extent();
    let (integral_scale, symbol) = circulant.integral_symbol();

    let characteristic = squarefree_part(&characteristic_polynomial(&symbol)?);
    let characteristic_polynomial = IntegerPolynomial::new(primitive_integer(&characteristic))?;

    let mut table = StarTable::found(extent)?;
    let symbol_rational: Vec<Rat> = symbol.iter().cloned().map(Rat::from_integer).collect();

    let mut passages = Vec::with_capacity(extent);
    for character in 0..extent {
        let star_polygon = StarPolygon::of(character, extent);
        let cyclotomic = cyclotomic_polynomial(star_polygon.points);
        let (quotient, remainder) =
            poly_divmod(&symbol_rational, &cyclotomic).ok_or(WindingError::NoSplitPoint)?;
        let null_witness = if remainder.is_empty() {
            // `Φ_d` is monic and integral and the symbol is integral, so the quotient is integral
            // too. Refuse rather than round if it ever is not.
            let (Some(cyclotomic), Some(quotient)) = (
                integer_coefficients(&cyclotomic),
                integer_coefficients(&quotient),
            ) else {
                return Err(WindingError::NonIntegralWitness { character });
            };
            Some(CyclotomicWitness {
                order: star_polygon.points,
                cyclotomic,
                quotient,
            })
        } else {
            None
        };

        let passage = loop {
            let scaled_enclosure = table.enclose(&symbol, character)?;
            let returns = if null_witness.is_some() {
                if scaled_enclosure.lower.is_positive() || scaled_enclosure.upper.is_negative() {
                    return Err(WindingError::NullDisagreesWithEnclosure { character });
                }
                PassageReturn::OnTheNullCone
            } else if scaled_enclosure.lower.is_positive() {
                PassageReturn::Handed(Hand::WithTheTurn)
            } else if scaled_enclosure.upper.is_negative() {
                PassageReturn::Handed(Hand::AgainstTheTurn)
            } else {
                if scaled_enclosure.is_point() {
                    // The enclosure is exact and it is zero, yet the cyclotomic test said the
                    // passage is not null. The two exact routes contradict each other.
                    return Err(WindingError::HandDisagreesWithCyclotomic { character });
                }
                table.refine()?;
                continue;
            };
            if let Some(certificate) = certify(&characteristic_polynomial, &scaled_enclosure) {
                break Passage {
                    character,
                    winding: Rat::new(BigInt::from(character), BigInt::from(extent)),
                    star_polygon,
                    returns,
                    scaled_enclosure,
                    certificate,
                    null_witness: null_witness.clone(),
                };
            }
            table.refine()?;
        };
        passages.push(passage);
    }

    Ok(WindingInertia {
        extent,
        integral_scale,
        symbol,
        characteristic_polynomial,
        passages,
        refinements: table.refinements,
    })
}

/// The adjacency of the cycle `C_n`: the one family in which `λ_k = 2cos(2πk/n)` exactly.
pub fn cycle_adjacency(extent: usize) -> Result<SymmetricCirculant, WindingError> {
    if extent < 3 {
        return Err(WindingError::CycleTooSmall { extent });
    }
    let mut first_row = vec![Rat::zero(); extent];
    first_row[1] = Rat::one();
    first_row[extent - 1] = Rat::one();
    SymmetricCirculant::from_first_row(first_row)
}

/// The Laplacian of the cycle `C_n`: `λ_k = 2 − 2cos(2πk/n)`, one null and nothing against the turn.
pub fn cycle_laplacian(extent: usize) -> Result<SymmetricCirculant, WindingError> {
    if extent < 3 {
        return Err(WindingError::CycleTooSmall { extent });
    }
    let mut first_row = vec![Rat::zero(); extent];
    first_row[0] = Rat::from_integer(BigInt::from(2));
    first_row[1] = -Rat::one();
    first_row[extent - 1] = -Rat::one();
    SymmetricCirculant::from_first_row(first_row)
}

/// The quarter-turn reading of the cycle's adjacency: **exact rational, no algebra at all**.
///
/// `λ_k = 2cos(2πk/n)` is negative exactly when the step exceeds a quarter turn, so the hand is
/// decided by comparing the winding `k/n` against `1/4` and `3/4` **as rationals**. No Sturm
/// sequence, no characteristic polynomial, no interval, no elimination — which is what makes it an
/// independent route rather than a restatement.
pub fn quarter_turn_reading(extent: usize) -> Result<Vec<PassageReturn>, WindingError> {
    if extent < 3 {
        return Err(WindingError::CycleTooSmall { extent });
    }
    let quarter = Rat::new(BigInt::one(), BigInt::from(4));
    let three_quarters = Rat::new(BigInt::from(3), BigInt::from(4));
    Ok((0..extent)
        .map(|character| {
            let winding = Rat::new(BigInt::from(character), BigInt::from(extent));
            if winding == quarter || winding == three_quarters {
                PassageReturn::OnTheNullCone
            } else if quarter < winding && winding < three_quarters {
                PassageReturn::Handed(Hand::AgainstTheTurn)
            } else {
                PassageReturn::Handed(Hand::WithTheTurn)
            }
        })
        .collect())
}

/// Read a grown circuit on an `n`-fold cyclic receiver.
///
/// The receiver is the declaration `net ↦ net mod n`, and what it retains of the growth is the
/// **conduction counted by displacement class**: `c_d` is the number of grown arcs whose endpoints
/// differ by `d` around the cycle, counted in both orientations. Counting both orientations is what
/// makes the return reversal-symmetric, so the result is a symmetric circulant by construction and
/// not by a repair.
///
/// This is a chart, not a fixture. The entries are whatever the growth put there — routinely far
/// beyond `{0,1}` — and the receiver's own extent is the only thing declared.
///
/// **The net identifier is a schedule coordinate, so this chart is schedule-relative and measurably
/// so.** [`crate::grown_cell`] declares it directly: *"Net identifiers, gate identifiers and
/// instance identifiers are all allocated at expansion time. Two schedules therefore produce the
/// same circuit under different symbols."* Folding those identifiers modulo `n` therefore reads a
/// receiver coordinate along with the conduction, and
/// `a_grown_circuit_read_on_a_cyclic_receiver_returns_its_passages_by_winding` **measures the
/// difference rather than asserting it away**: the same circuit at extent seven returns `(3,0,4)`
/// under two schedules and `(1,0,6)` under the third. What is invariant across all of them is the
/// claim this module makes — that the character route and the elimination return one split — and an
/// invariant is only visible across two frames.
pub fn cyclic_receiver_of_growth(
    grown: &GrownComplex,
    extent: usize,
) -> Result<SymmetricCirculant, WindingError> {
    if extent == 0 {
        return Err(WindingError::EmptyCirculant);
    }
    let mut counts = vec![0_i64; extent];
    for arc in &grown.arcs {
        let tail = (arc.tail.0 as usize) % extent;
        let head = (arc.head.0 as usize) % extent;
        counts[(head + extent - tail) % extent] += 1;
        counts[(tail + extent - head) % extent] += 1;
    }
    SymmetricCirculant::from_integers(&counts)
}

// ===============================================================================================
// the star table

/// `2cos(2πm/n)` for `m = 0..=n/2`, exactly, in descending value order.
///
/// The values are the distinct real roots of the squarefree part of `D_n(x) − 2`, and `2cos(2πm/n)`
/// is strictly decreasing on `m ∈ [0, n/2]` because `2πm/n` sweeps `[0, π]` — so the descending
/// order of the isolated intervals *is* the labelling by `m`, with no separate matching step.
#[derive(Clone, Debug)]
pub struct StarTable {
    extent: usize,
    values: Vec<ExactInterval>,
    /// The entries Niven's theorem makes exactly rational. Never refined, and each was checked
    /// against the interval Sturm isolated for it.
    exact: Vec<bool>,
    polynomial: IntegerPolynomial,
    refinements: usize,
}

impl StarTable {
    pub fn found(extent: usize) -> Result<Self, WindingError> {
        if extent == 0 {
            return Err(WindingError::EmptyCirculant);
        }
        let population = extent / 2 + 1;
        let polynomial = IntegerPolynomial::new(primitive_integer(&squarefree_part(
            &dickson_less_two(extent),
        )))?;
        // Every `2cos` lies in `[-2, 2]`, so `(-3, 3)` strictly contains the whole population.
        let bound = ExactInterval::new(
            Rat::from_integer(BigInt::from(-3)),
            Rat::from_integer(BigInt::from(3)),
        )?;
        let mut isolated = isolate_all_roots(&polynomial, &bound)?;
        if isolated.len() != population {
            return Err(WindingError::RootPopulation {
                expected: population,
                found: isolated.len(),
            });
        }
        // ascending -> descending, which is ascending in `m`.
        isolated.reverse();

        let mut exact = vec![false; population];
        for (step, interval) in isolated.iter_mut().enumerate() {
            let Some(value) = niven_value(step, extent) else {
                continue;
            };
            // The independent cross-check: Niven says the value, Sturm says the interval, and the
            // value has to be inside the interval Sturm isolated for that position.
            if value < interval.lower || value > interval.upper {
                return Err(WindingError::NivenDisagreesWithSturm { step });
            }
            *interval = ExactInterval::point(value);
            exact[step] = true;
        }

        Ok(Self {
            extent,
            values: isolated,
            exact,
            polynomial,
            refinements: 0,
        })
    }

    pub fn extent(&self) -> usize {
        self.extent
    }

    /// `2cos(2πm/n)`, enclosed.
    pub fn value(&self, step: usize) -> Option<&ExactInterval> {
        self.values.get(step)
    }

    pub fn is_exact(&self, step: usize) -> bool {
        self.exact.get(step).copied().unwrap_or(false)
    }

    /// Halve every inexact interval. A schedule, not a governor.
    pub fn refine(&mut self) -> Result<(), WindingError> {
        if self.refinements >= REFINEMENT_APERTURE {
            return Err(WindingError::RefinementAperture {
                aperture: REFINEMENT_APERTURE,
            });
        }
        let mut moved = false;
        for (step, interval) in self.values.iter_mut().enumerate() {
            if self.exact[step] {
                continue;
            }
            *interval = halve_isolating_interval(&self.polynomial, interval)?;
            moved = true;
        }
        if !moved {
            // Every entry is exactly rational, so nothing can be sharpened. Whatever the caller was
            // waiting for will never arrive; say so rather than spin.
            return Err(WindingError::NothingLeftToRefine);
        }
        self.refinements += 1;
        Ok(())
    }

    /// `λ_k` of the integral symbol, enclosed.
    ///
    /// The conjugate terms of `Σ_j c_j ω^{jk}` pair off under reversal symmetry, leaving
    /// `c_0 + [n even] c_{n/2}(−1)^k + Σ_{j=1}^{(n−1)/2} c_j · 2cos(2πjk/n)`.
    pub fn enclose(
        &self,
        symbol: &[BigInt],
        character: usize,
    ) -> Result<ExactInterval, WindingError> {
        let extent = self.extent;
        let mut total = ExactInterval::point(Rat::from_integer(symbol[0].clone()));
        if extent % 2 == 0 {
            let middle = &symbol[extent / 2];
            let signed = if character % 2 == 0 {
                middle.clone()
            } else {
                -middle.clone()
            };
            total = add_intervals(&total, &ExactInterval::point(Rat::from_integer(signed)))?;
        }
        for pair in 1..=(extent.saturating_sub(1) / 2) {
            let step = fold_step(pair * character % extent, extent);
            let value = self.values.get(step).ok_or(WindingError::RootPopulation {
                expected: step + 1,
                found: self.values.len(),
            })?;
            total = add_intervals(&total, &scaled_interval(&symbol[pair], value)?)?;
        }
        Ok(total)
    }
}

/// `m ↦ min(m, n − m)`: `2cos` does not distinguish a step from its reversal, so the table is
/// indexed by the fold and never by the raw residue.
fn fold_step(residue: usize, extent: usize) -> usize {
    let reversed = (extent - residue) % extent;
    residue.min(reversed)
}

/// The rational values of `2cos(2πm/n)`, by Niven's theorem.
///
/// `2cos(2πm/n) ∈ Q` exactly when `d = n/gcd(m,n) ∈ {1,2,3,4,6}`, and `d` fixes the value:
/// `d = 1 → 2`, `d = 2 → −2`, `d = 3 → −1`, `d = 4 → 0`, `d = 6 → 1`. Everything else is a genuine
/// algebraic irrational and is carried as an interval.
fn niven_value(step: usize, extent: usize) -> Option<Rat> {
    let order = extent / gcd_usize(step, extent);
    match order {
        1 => Some(Rat::from_integer(BigInt::from(2))),
        2 => Some(Rat::from_integer(BigInt::from(-2))),
        3 => Some(-Rat::one()),
        4 => Some(Rat::zero()),
        6 => Some(Rat::one()),
        _ => None,
    }
}

// ===============================================================================================
// exact root isolation

/// The split points a bisection may take, as fractions of the interval.
///
/// A **schedule**. An endpoint of a Sturm count may not itself be a root, so a midpoint that lands
/// on one is stepped over rather than nudged by an epsilon. A polynomial of degree `d` has at most
/// `d` roots, so a list this long exhausts the obstruction for every degree this module reaches.
fn split_fractions() -> Vec<Rat> {
    let mut fractions = Vec::new();
    for denominator in [2_i64, 3, 5, 7, 11, 13, 17, 19] {
        for numerator in 1..denominator {
            if gcd_usize(numerator as usize, denominator as usize) == 1 {
                fractions.push(Rat::new(BigInt::from(numerator), BigInt::from(denominator)));
            }
        }
    }
    fractions
}

fn interior_non_root(
    polynomial: &IntegerPolynomial,
    interval: &ExactInterval,
) -> Result<Rat, WindingError> {
    let width = &interval.upper - &interval.lower;
    for fraction in split_fractions() {
        let candidate = &interval.lower + &width * &fraction;
        if !polynomial.evaluate(&candidate).is_zero() {
            return Ok(candidate);
        }
    }
    Err(WindingError::NoSplitPoint)
}

/// Every distinct real root of a squarefree polynomial in one interval, isolated, ascending.
fn isolate_all_roots(
    polynomial: &IntegerPolynomial,
    bound: &ExactInterval,
) -> Result<Vec<ExactInterval>, WindingError> {
    let mut pending = vec![(
        bound.clone(),
        polynomial.distinct_root_count(bound)?,
        0_usize,
    )];
    let mut isolated: Vec<ExactInterval> = Vec::new();
    while let Some((interval, count, depth)) = pending.pop() {
        if count == 0 {
            continue;
        }
        if count == 1 {
            isolated.push(interval);
            continue;
        }
        if depth >= ISOLATION_APERTURE {
            return Err(WindingError::IsolationAperture {
                aperture: ISOLATION_APERTURE,
            });
        }
        let middle = interior_non_root(polynomial, &interval)?;
        let lower = ExactInterval::new(interval.lower.clone(), middle.clone())?;
        let upper = ExactInterval::new(middle, interval.upper.clone())?;
        let lower_count = polynomial.distinct_root_count(&lower)?;
        let upper_count = polynomial.distinct_root_count(&upper)?;
        pending.push((lower, lower_count, depth + 1));
        pending.push((upper, upper_count, depth + 1));
    }
    isolated.sort_by(|left, right| left.lower.cmp(&right.lower));
    Ok(isolated)
}

/// Halve an interval already known to isolate exactly one root, keeping the half that has it.
fn halve_isolating_interval(
    polynomial: &IntegerPolynomial,
    interval: &ExactInterval,
) -> Result<ExactInterval, WindingError> {
    let middle = interior_non_root(polynomial, interval)?;
    let lower = ExactInterval::new(interval.lower.clone(), middle.clone())?;
    if polynomial.distinct_root_count(&lower)? == 1 {
        return Ok(lower);
    }
    Ok(ExactInterval::new(middle, interval.upper.clone())?)
}

/// Prove that an enclosure isolates exactly one root of the characteristic polynomial.
///
/// A point enclosure — the eigenvalue came out exactly rational — is grown outwards; an interval
/// enclosure is tried as it stands and then grown by shrinking pads, because an endpoint that lands
/// on a root is refused by [`AlgebraicRoot::isolate`] and must be stepped over rather than nudged.
/// `None` means the enclosure is still too wide to separate two eigenvalues, which the caller
/// answers by refining the star table.
fn certify(polynomial: &IntegerPolynomial, enclosure: &ExactInterval) -> Option<AlgebraicRoot> {
    let two = Rat::from_integer(BigInt::from(2));
    if !enclosure.is_point() {
        if let Ok(root) = AlgebraicRoot::isolate(polynomial.clone(), enclosure.clone()) {
            return Some(root);
        }
    }
    let mut pad = if enclosure.is_point() {
        Rat::one()
    } else {
        (&enclosure.upper - &enclosure.lower) / &two
    };
    for _ in 0..REFINEMENT_APERTURE {
        let candidate =
            ExactInterval::new(&enclosure.lower - &pad, &enclosure.upper + &pad).ok()?;
        if let Ok(root) = AlgebraicRoot::isolate(polynomial.clone(), candidate) {
            return Some(root);
        }
        pad /= &two;
    }
    None
}

// ===============================================================================================
// exact polynomial arithmetic

fn trim(coefficients: &mut Vec<Rat>) {
    while coefficients.last().is_some_and(Zero::is_zero) {
        coefficients.pop();
    }
}

fn poly_sub(left: &[Rat], right: &[Rat]) -> Vec<Rat> {
    let mut result = vec![Rat::zero(); left.len().max(right.len())];
    for (index, value) in left.iter().enumerate() {
        result[index] += value;
    }
    for (index, value) in right.iter().enumerate() {
        result[index] -= value;
    }
    trim(&mut result);
    result
}

fn poly_shift(coefficients: &[Rat]) -> Vec<Rat> {
    let mut shifted = vec![Rat::zero()];
    shifted.extend_from_slice(coefficients);
    trim(&mut shifted);
    shifted
}

fn poly_derivative(coefficients: &[Rat]) -> Vec<Rat> {
    let mut result: Vec<Rat> = coefficients
        .iter()
        .enumerate()
        .skip(1)
        .map(|(degree, value)| value * Rat::from_integer(BigInt::from(degree)))
        .collect();
    trim(&mut result);
    result
}

fn poly_divmod(dividend: &[Rat], divisor: &[Rat]) -> Option<(Vec<Rat>, Vec<Rat>)> {
    if divisor.is_empty() {
        return None;
    }
    let divisor_degree = divisor.len() - 1;
    let mut remainder = dividend.to_vec();
    trim(&mut remainder);
    if remainder.len() <= divisor_degree {
        return Some((Vec::new(), remainder));
    }
    let mut quotient = vec![Rat::zero(); remainder.len() - divisor_degree];
    while remainder.len() > divisor_degree {
        let shift = remainder.len() - 1 - divisor_degree;
        let factor = remainder[remainder.len() - 1].clone() / &divisor[divisor_degree];
        quotient[shift] = factor.clone();
        for (index, coefficient) in divisor.iter().enumerate() {
            remainder[index + shift] -= &factor * coefficient;
        }
        trim(&mut remainder);
        if remainder.is_empty() {
            break;
        }
    }
    trim(&mut quotient);
    Some((quotient, remainder))
}

fn monic(mut coefficients: Vec<Rat>) -> Vec<Rat> {
    trim(&mut coefficients);
    let Some(leading) = coefficients.last().cloned() else {
        return coefficients;
    };
    for coefficient in &mut coefficients {
        *coefficient /= &leading;
    }
    coefficients
}

fn poly_gcd(left: &[Rat], right: &[Rat]) -> Vec<Rat> {
    let mut current = left.to_vec();
    trim(&mut current);
    let mut next = right.to_vec();
    trim(&mut next);
    while !next.is_empty() {
        let (_, remainder) = poly_divmod(&current, &next).expect("the divisor is nonempty");
        current = next;
        next = remainder;
    }
    monic(current)
}

/// `p / gcd(p, p')`: the same roots, each once. Correct over `Q` because the characteristic is zero.
fn squarefree_part(coefficients: &[Rat]) -> Vec<Rat> {
    let common = poly_gcd(coefficients, &poly_derivative(coefficients));
    if common.is_empty() {
        return coefficients.to_vec();
    }
    poly_divmod(coefficients, &common)
        .map(|(quotient, _)| quotient)
        .unwrap_or_else(|| coefficients.to_vec())
}

/// Clear denominators, divide out the content, and make the leading coefficient positive.
fn primitive_integer(coefficients: &[Rat]) -> Vec<BigInt> {
    let mut trimmed = coefficients.to_vec();
    trim(&mut trimmed);
    if trimmed.is_empty() {
        return vec![BigInt::zero()];
    }
    let mut denominator = BigInt::one();
    for value in &trimmed {
        denominator = lcm_integer(&denominator, value.denom());
    }
    let mut integral: Vec<BigInt> = trimmed
        .iter()
        .map(|value| value.numer() * (&denominator / value.denom()))
        .collect();
    let mut content = BigInt::zero();
    for value in &integral {
        content = gcd_integer(&content, value);
    }
    if !content.is_zero() {
        for value in &mut integral {
            *value /= &content;
        }
    }
    if integral.last().is_some_and(Signed::is_negative) {
        for value in &mut integral {
            *value = -value.clone();
        }
    }
    integral
}

/// The exact integer coefficients of a polynomial already known to be integral.
///
/// Deliberately **not** [`primitive_integer`]. The null witness has to satisfy
/// `Φ_d · quotient = symbol` on the nose, and dividing out a content or normalizing a leading sign
/// would break exactly that identity while leaving the witness looking well formed.
fn integer_coefficients(coefficients: &[Rat]) -> Option<Vec<BigInt>> {
    let mut trimmed = coefficients.to_vec();
    trim(&mut trimmed);
    trimmed
        .iter()
        .map(|value| value.is_integer().then(|| value.to_integer()))
        .collect()
}

fn integer_polynomial_product(left: &[BigInt], right: &[BigInt]) -> Vec<BigInt> {
    if left.is_empty() || right.is_empty() {
        return Vec::new();
    }
    let mut result = vec![BigInt::zero(); left.len() + right.len() - 1];
    for (position, value) in left.iter().enumerate() {
        for (offset, other) in right.iter().enumerate() {
            result[position + offset] += value * other;
        }
    }
    while result.last().is_some_and(Zero::is_zero) {
        result.pop();
    }
    result
}

/// `D_n(x) − 2`, where `D_n(z + z^{-1}) = z^n + z^{-n}`.
///
/// `D_0 = 2`, `D_1 = x`, `D_m = x·D_{m−1} − D_{m−2}`, all integral. Setting `z = ω^m` gives
/// `D_n(β_m) = ω^{mn} + ω^{-mn} = 2`, so every `β_m` is a root — and those are all of them.
fn dickson_less_two(extent: usize) -> Vec<Rat> {
    let mut previous = vec![Rat::from_integer(BigInt::from(2))];
    let mut current = vec![Rat::zero(), Rat::one()];
    if extent == 0 {
        return poly_sub(&previous, &[Rat::from_integer(BigInt::from(2))]);
    }
    for _ in 2..=extent {
        let next = poly_sub(&poly_shift(&current), &previous);
        previous = current;
        current = next;
    }
    poly_sub(&current, &[Rat::from_integer(BigInt::from(2))])
}

/// `Φ_d`, by `x^d − 1 = Π_{e | d} Φ_e`.
///
/// `Φ_d` is the minimal polynomial over `Q` of a *primitive* `d`-th root of unity — the star polygon
/// `{n/k}` in lowest terms — which is what makes the divisibility test in [`winding_inertia`] a
/// decision rather than an estimate.
fn cyclotomic_polynomial(order: usize) -> Vec<Rat> {
    if order == 0 {
        return vec![Rat::one()];
    }
    let mut result = vec![Rat::zero(); order + 1];
    result[order] = Rat::one();
    result[0] = -Rat::one();
    for divisor in 1..order {
        if order % divisor == 0 {
            let (quotient, _) = poly_divmod(&result, &cyclotomic_polynomial(divisor))
                .expect("a cyclotomic polynomial is nonzero");
            result = quotient;
        }
    }
    result
}

/// `det(xI − C)` by Faddeev–LeVerrier, over exact rationals.
///
/// `N_0 = I`, `M_k = C·N_{k−1}`, `c_k = −tr(M_k)/k`, `N_k = M_k + c_k I`, and
/// `p(x) = x^n + c_1 x^{n−1} + … + c_n`. **This routine is never told `n` as a symmetry, never told
/// `k`, and never sees the first row as a symbol.** It multiplies matrices and takes traces, which
/// is what makes the certificate it supports an independent check on the character route.
fn characteristic_polynomial(symbol: &[BigInt]) -> Result<Vec<Rat>, WindingError> {
    let extent = symbol.len();
    let matrix = ExactRatMatrix::new(
        (0..extent)
            .map(|row| {
                (0..extent)
                    .map(|column| {
                        Rat::from_integer(symbol[(column + extent - row) % extent].clone())
                    })
                    .collect()
            })
            .collect(),
    )?;
    let mut coefficients = vec![Rat::zero(); extent + 1];
    coefficients[extent] = Rat::one();
    let mut carried = ExactRatMatrix::identity(extent)?;
    for step in 1..=extent {
        let product = matrix.multiply(&carried)?;
        let mut trace = Rat::zero();
        for index in 0..extent {
            trace += product.get(index, index)?;
        }
        let coefficient = -trace / Rat::from_integer(BigInt::from(step));
        coefficients[extent - step] = coefficient.clone();
        carried = product.add(&ExactRatMatrix::identity(extent)?.scaled(&coefficient))?;
    }
    Ok(coefficients)
}

// ===============================================================================================
// exact interval arithmetic

fn scaled_interval(
    coefficient: &BigInt,
    interval: &ExactInterval,
) -> Result<ExactInterval, WindingError> {
    let factor = Rat::from_integer(coefficient.clone());
    let (lower, upper) = if coefficient.is_negative() {
        (&factor * &interval.upper, &factor * &interval.lower)
    } else {
        (&factor * &interval.lower, &factor * &interval.upper)
    };
    Ok(ExactInterval::new(lower, upper)?)
}

fn add_intervals(
    left: &ExactInterval,
    right: &ExactInterval,
) -> Result<ExactInterval, WindingError> {
    Ok(ExactInterval::new(
        &left.lower + &right.lower,
        &left.upper + &right.upper,
    )?)
}

// ===============================================================================================
// integers

fn gcd_usize(mut left: usize, mut right: usize) -> usize {
    while right != 0 {
        let remainder = left % right;
        left = right;
        right = remainder;
    }
    left
}

fn gcd_integer(left: &BigInt, right: &BigInt) -> BigInt {
    let mut left = left.abs();
    let mut right = right.abs();
    while !right.is_zero() {
        let remainder = &left % &right;
        left = right;
        right = remainder;
    }
    left
}

fn lcm_integer(left: &BigInt, right: &BigInt) -> BigInt {
    let common = gcd_integer(left, right);
    if common.is_zero() {
        return BigInt::zero();
    }
    (left / &common * right).abs()
}

// ===============================================================================================
// refusals

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum WindingError {
    #[error("a circulant on no characters has no passages")]
    EmptyCirculant,
    #[error(
        "a circulant is symmetric only when c_j = c_(n-j); step {step} breaks it, so the form has no real spectrum and no inertia"
    )]
    NotReversalSymmetric { step: usize },
    #[error(
        "entry ({row}, {column}) does not depend only on (column - row) mod n, so this form is not circulant and its inertia does not factor through any character group"
    )]
    NotCirculant { row: usize, column: usize },
    #[error("the cycle C_{extent} is not a simple graph; the cycle family starts at three")]
    CycleTooSmall { extent: usize },
    #[error("the star polynomial should carry {expected} distinct real roots and carries {found}")]
    RootPopulation { expected: usize, found: usize },
    #[error(
        "Niven's rational value for star step {step} lies outside the interval Sturm isolated for it"
    )]
    NivenDisagreesWithSturm { step: usize },
    #[error(
        "character {character} was proved null by its cyclotomic divisor yet its enclosure excludes zero"
    )]
    NullDisagreesWithEnclosure { character: usize },
    #[error(
        "character {character} encloses exactly zero yet its cyclotomic divisor test says it is not null"
    )]
    HandDisagreesWithCyclotomic { character: usize },
    #[error(
        "the cyclotomic witness for character {character} is not integral, so it cannot be a divisor of an integral symbol"
    )]
    NonIntegralWitness { character: usize },
    #[error("no interior split point avoided a root of the polynomial")]
    NoSplitPoint,
    #[error("root isolation exceeded its declared aperture of {aperture} bisections")]
    IsolationAperture { aperture: usize },
    #[error("the star table exceeded its declared aperture of {aperture} refinements")]
    RefinementAperture { aperture: usize },
    #[error("every star value is already exact, so nothing can be refined further")]
    NothingLeftToRefine,
    #[error(transparent)]
    Exact(#[from] ExactValueError),
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
    #[error(transparent)]
    Form(#[from] InertiaError),
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::grown_cell::{ComplexAperture, Schedule, found_complex, grow, standard_cells};
    use crate::inertia::{PivotOrder, congruence, inertia, inertia_with_schedule};

    fn circulant(first_row: &[i64]) -> SymmetricCirculant {
        SymmetricCirculant::from_integers(first_row).expect("fixture is reversal-symmetric")
    }

    fn winding(numerator: i64, denominator: i64) -> Rat {
        Rat::new(BigInt::from(numerator), BigInt::from(denominator))
    }

    /// A unitriangular rational basis that is deliberately **not** circulant, so `P^T C P` carries no
    /// cyclic symmetry at all.
    fn scrambling_basis(extent: usize) -> ExactRatMatrix {
        let mut rows = vec![vec![Rat::zero(); extent]; extent];
        for (index, row) in rows.iter_mut().enumerate() {
            row[index] = Rat::one();
        }
        if extent >= 3 {
            rows[0][2] = Rat::from_integer(BigInt::from(3));
        }
        if extent >= 4 {
            rows[1][3] = -Rat::from_integer(BigInt::from(2));
        }
        if extent >= 5 {
            rows[0][4] = Rat::new(BigInt::from(1), BigInt::from(2));
        }
        ExactRatMatrix::new(rows).expect("the basis is rectangular")
    }

    // -----------------------------------------------------------------------------------------
    // the measured claim

    /// §2b, measured 2026-08-08: the triangle returns `(1, 0, 2)` — **one zero-frequency passage and
    /// two that wind past the quarter** — and this asserts the naming, not the count.
    #[test]
    fn the_triangle_returns_one_zero_frequency_passage_and_two_that_wind_past_the_quarter() {
        let reading = winding_inertia(&cycle_adjacency(3).unwrap()).unwrap();
        assert_eq!(
            reading.split(),
            Inertia {
                positive: 1,
                zero: 0,
                negative: 2
            }
        );

        let zero_frequency = reading.passage(0).unwrap();
        assert_eq!(zero_frequency.winding, Rat::zero());
        assert_eq!(
            zero_frequency.star_polygon,
            StarPolygon { points: 1, step: 0 }
        );
        assert_eq!(
            zero_frequency.returns,
            PassageReturn::Handed(Hand::WithTheTurn)
        );

        // The artifact §2b asks for: the windings, not the number two.
        assert_eq!(
            reading.windings_past_the_hand(),
            vec![winding(1, 3), winding(2, 3)]
        );
        for character in [1_usize, 2] {
            assert_eq!(
                reading.passage(character).unwrap().star_polygon,
                StarPolygon {
                    points: 3,
                    step: character
                },
                "both non-principal passages trace the triangle itself"
            );
        }

        // Bit-identical to the elimination, which never sees the symmetry.
        assert_eq!(
            reading.split(),
            inertia(&cycle_adjacency(3).unwrap().as_symmetric_form().unwrap())
        );
    }

    /// The quarter-turn law, swept over both halves of `4 | n` so that neither "always null" nor
    /// "never null" can pass, and checked against a route that never touches Sturm, the
    /// characteristic polynomial, or the elimination.
    #[test]
    fn the_quarter_turn_law_holds_and_both_halves_of_the_divisibility_sweep_fire() {
        let quarter = winding(1, 4);
        let three_quarters = winding(3, 4);
        let mut saw_a_null_bearing_cycle = false;
        let mut saw_a_null_free_cycle = false;

        for extent in 3..=12_usize {
            let reading = winding_inertia(&cycle_adjacency(extent).unwrap()).unwrap();
            let rational_route = quarter_turn_reading(extent).unwrap();
            assert_eq!(
                reading
                    .passages
                    .iter()
                    .map(|passage| passage.returns)
                    .collect::<Vec<_>>(),
                rational_route,
                "the exact-rational quarter-turn route and the exact-algebraic character route \
                 disagree on C_{extent}"
            );

            for passage in &reading.passages {
                let past = quarter < passage.winding && passage.winding < three_quarters;
                let at = passage.winding == quarter || passage.winding == three_quarters;
                let expected = if at {
                    PassageReturn::OnTheNullCone
                } else if past {
                    PassageReturn::Handed(Hand::AgainstTheTurn)
                } else {
                    PassageReturn::Handed(Hand::WithTheTurn)
                };
                assert_eq!(
                    passage.returns, expected,
                    "C_{extent} character {}",
                    passage.character
                );
            }

            let nulls = reading.null_windings();
            if extent % 4 == 0 {
                assert_eq!(
                    nulls,
                    vec![quarter.clone(), three_quarters.clone()],
                    "C_{extent} has 4 | n, so the form must return nothing at exactly the hand"
                );
                saw_a_null_bearing_cycle = true;
            } else {
                assert!(
                    nulls.is_empty(),
                    "C_{extent} does not have 4 | n, so no winding may sit on the hand: {nulls:?}"
                );
                saw_a_null_free_cycle = true;
            }
        }

        assert!(
            saw_a_null_bearing_cycle && saw_a_null_free_cycle,
            "a sweep that saw only one half of `4 | n` cannot distinguish the law from a constant"
        );
    }

    /// The whole point of the winding reading: `C_12` returns five passages against the turn, and
    /// they have **names**.
    #[test]
    fn the_passages_against_the_hand_are_returned_by_name_and_never_as_a_number() {
        let reading = winding_inertia(&cycle_adjacency(12).unwrap()).unwrap();
        assert_eq!(
            reading.windings_past_the_hand(),
            vec![
                winding(1, 3),
                winding(5, 12),
                winding(1, 2),
                winding(7, 12),
                winding(2, 3)
            ]
        );
        assert_eq!(
            reading.windings_of(Hand::WithTheTurn),
            vec![
                Rat::zero(),
                winding(1, 12),
                winding(1, 6),
                winding(5, 6),
                winding(11, 12)
            ]
        );
        assert_eq!(
            reading.null_windings(),
            vec![winding(1, 4), winding(3, 4)],
            "the form returns nothing precisely at the hand"
        );
        assert_eq!(
            reading.split(),
            Inertia {
                positive: 5,
                zero: 2,
                negative: 5
            }
        );
        // Every star polygon named, including the degenerate ones the divisors force.
        assert_eq!(
            reading
                .passages
                .iter()
                .map(|passage| passage.star_polygon.label())
                .collect::<Vec<_>>(),
            vec![
                "{1/0}", "{12/1}", "{6/1}", "{4/1}", "{3/1}", "{12/5}", "{2/1}", "{12/7}", "{3/2}",
                "{4/3}", "{6/5}", "{12/11}"
            ]
        );
    }

    // -----------------------------------------------------------------------------------------
    // the two routes, and their independence

    /// The character split against the elimination's split, on a family that contains all three
    /// shapes — definite, indefinite, degenerate — and non-cycle circulants with entries well beyond
    /// `{0,1}`. A family of one shape could not disagree, which is §8's tautology rule.
    #[test]
    fn the_character_split_equals_the_split_the_elimination_finds() {
        let family: Vec<Vec<i64>> = vec![
            vec![0, 1, 1],                            // C_3 adjacency
            vec![0, 1, 0, 1],                         // C_4 adjacency, two nulls
            vec![0, 1, 1, 1, 1],                      // K_5 = C_5^2
            vec![2, -1, 0, 0, 0, -1],                 // L(C_6), one null
            vec![2, 1, 0, 0, 1],                      // Q(C_5), definite
            vec![1, 0, 0, 0, 0, 0],                   // the identity
            vec![-1, 0, 0, 0, 0, 0],                  // the negated identity
            vec![0, 2, 3, 3, 2],                      // weighted, beyond {0,1}
            vec![1, -2, 3, -4, 3, -2],                // mixed signs, two nulls
            vec![3, -1, 0, 2, -5, 2, 0, -1],          // mixed, one null
            vec![0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1], // three nulls
            vec![0, 0, 0, 0],                         // the zero form, wholly radical
        ];
        let mut saw_definite = false;
        let mut saw_indefinite = false;
        let mut saw_degenerate = false;

        for first_row in &family {
            let form = circulant(first_row);
            let reading = winding_inertia(&form).unwrap();
            let by_elimination = inertia(&form.as_symmetric_form().unwrap());
            assert_eq!(
                reading.split(),
                by_elimination,
                "the character route and the elimination disagree on {first_row:?}"
            );
            assert_eq!(reading.passages.len(), first_row.len());
            saw_definite |=
                by_elimination.is_positive_definite() || by_elimination.is_negative_definite();
            saw_indefinite |= by_elimination.is_indefinite();
            saw_degenerate |= by_elimination.is_degenerate();
        }

        assert!(
            saw_definite && saw_indefinite && saw_degenerate,
            "a family carrying only one shape of split cannot exhibit a disagreement"
        );
    }

    /// **The independence proof.** The elimination is handed `P^T C P` for a non-circulant `P`. The
    /// transported form is refused as not circulant — so it carries no symmetry to read — and the
    /// elimination still returns exactly the split the characters named. It therefore cannot have
    /// been reading `n` or `k`.
    #[test]
    fn the_elimination_never_sees_the_symmetry_because_it_agrees_after_a_congruence_destroys_it() {
        let family: Vec<Vec<i64>> = vec![
            vec![0, 1, 1],
            vec![0, 1, 0, 1],
            vec![2, -1, 0, 0, 0, -1],
            vec![0, 2, 3, 3, 2],
            vec![1, -2, 3, -4, 3, -2],
            vec![3, -1, 0, 2, -5, 2, 0, -1],
        ];
        let mut destroyed_the_symmetry = 0;
        for first_row in &family {
            let form = circulant(first_row);
            let named = winding_inertia(&form).unwrap().split();
            let transported = congruence(
                &form.as_symmetric_form().unwrap(),
                &scrambling_basis(first_row.len()),
            )
            .expect("the unitriangular basis is invertible");
            assert_ne!(
                transported,
                form.as_symmetric_form().unwrap(),
                "a basis that fixes the form would leave the symmetry intact"
            );
            assert!(
                matches!(
                    SymmetricCirculant::from_symmetric_form(&transported),
                    Err(WindingError::NotCirculant { .. })
                ),
                "the transported form still carries the cyclic symmetry, so it proves nothing \
                 about independence: {first_row:?}"
            );
            destroyed_the_symmetry += 1;
            for order in PivotOrder::ALL {
                let (reading, schedule) = inertia_with_schedule(&transported, order);
                assert_eq!(
                    reading, named,
                    "elimination on the de-symmetrized {first_row:?} under {order:?}"
                );
                assert!(!schedule.steps.is_empty());
            }
        }
        assert_eq!(
            destroyed_the_symmetry,
            family.len(),
            "the independence claim rests on every transported form losing its symmetry"
        );

        // Where the check provably cannot fire, and why. `P^T · 0 · P = 0`, so the zero form has no
        // symmetry to destroy and is still circulant after any congruence whatsoever. §8: a negative
        // control's absence is evidence, so the exception is exhibited rather than excluded from the
        // family without comment.
        let zero = circulant(&[0, 0, 0, 0]);
        let flattened = congruence(&zero.as_symmetric_form().unwrap(), &scrambling_basis(4))
            .expect("the unitriangular basis is invertible");
        assert_eq!(
            SymmetricCirculant::from_symmetric_form(&flattened),
            Ok(zero),
            "the zero form cannot lose a symmetry it does not have"
        );
    }

    // -----------------------------------------------------------------------------------------
    // the refusals

    #[test]
    fn a_matrix_that_is_not_circulant_is_refused_by_name() {
        let form = SymmetricForm::from_integers(&[vec![1, 2, 0], vec![2, 5, 0], vec![0, 0, -3]])
            .expect("symmetric");
        // Row 0 is consistent with itself by definition, so the first entry that can break is in
        // row 1: `at(1,0)` must equal `at(0,2)` and does not.
        assert_eq!(
            SymmetricCirculant::from_symmetric_form(&form),
            Err(WindingError::NotCirculant { row: 1, column: 0 })
        );
        // `diag(1, -1)` is symmetric and indefinite and is refused at the diagonal, where a
        // circulant would have to repeat `c_0`.
        let signature =
            SymmetricForm::from_integers(&[vec![1, 0], vec![0, -1]]).expect("symmetric");
        assert_eq!(
            SymmetricCirculant::from_symmetric_form(&signature),
            Err(WindingError::NotCirculant { row: 1, column: 1 })
        );
        // And a genuine circulant is not refused, so the refusal discriminates rather than refusing
        // everything. `E8`'s Cartan matrix is the non-circulant partner of this pair.
        let cyclic = cycle_adjacency(5).unwrap().as_symmetric_form().unwrap();
        assert_eq!(
            SymmetricCirculant::from_symmetric_form(&cyclic),
            Ok(cycle_adjacency(5).unwrap())
        );
    }

    /// The hyperbolic plane **is** `circ(0, 1)`, and the winding reading names what the elimination
    /// only counts: its one negative direction is the **half turn**.
    ///
    /// `inertia.rs` reaches `(1, 0, 1)` here through its zero-diagonal `2x2` branch, having no
    /// nonzero diagonal entry to pivot on. The character route never meets that obstruction, because
    /// the two characters of `Z/2` are `+1` and `−1` and the second is `e^{iπ}` — which is the whole
    /// of §2b in one two-by-two matrix.
    #[test]
    fn the_hyperbolic_plane_is_a_circulant_whose_negative_direction_is_the_half_turn() {
        let hyperbolic =
            SymmetricForm::from_integers(&[vec![0, 1], vec![1, 0]]).expect("symmetric");
        let form = SymmetricCirculant::from_symmetric_form(&hyperbolic)
            .expect("the hyperbolic plane is circ(0,1)");
        let reading = winding_inertia(&form).unwrap();
        assert_eq!(
            reading.split(),
            Inertia {
                positive: 1,
                zero: 0,
                negative: 1
            }
        );
        assert_eq!(reading.split(), inertia(&hyperbolic));
        assert_eq!(reading.windings_past_the_hand(), vec![winding(1, 2)]);
        assert_eq!(
            reading.passage(1).unwrap().star_polygon,
            StarPolygon { points: 2, step: 1 }
        );
        assert_eq!(reading.windings_of(Hand::WithTheTurn), vec![Rat::zero()]);
    }

    #[test]
    fn a_first_row_that_is_not_reversal_symmetric_is_refused_by_the_step_that_breaks_it() {
        assert_eq!(
            SymmetricCirculant::from_integers(&[0, 1, 2, 0]),
            Err(WindingError::NotReversalSymmetric { step: 1 })
        );
        assert_eq!(
            SymmetricCirculant::from_integers(&[]),
            Err(WindingError::EmptyCirculant)
        );
        assert_eq!(
            cycle_adjacency(2),
            Err(WindingError::CycleTooSmall { extent: 2 })
        );
    }

    // -----------------------------------------------------------------------------------------
    // the poles

    /// The negative pole on the winding reading itself: a circulant whose passages are **all** one
    /// hand must report no winding past the hand at all. Without it, an implementation that always
    /// found something against the turn would still pass every test above.
    #[test]
    fn a_circulant_of_one_hand_reports_no_winding_past_the_hand() {
        let identity = winding_inertia(&circulant(&[1, 0, 0, 0, 0, 0])).unwrap();
        assert!(identity.windings_past_the_hand().is_empty());
        assert!(identity.null_windings().is_empty());
        assert_eq!(identity.windings_of(Hand::WithTheTurn).len(), 6);
        assert!(identity.split().is_positive_definite());

        let negated = winding_inertia(&circulant(&[-1, 0, 0, 0, 0, 0])).unwrap();
        assert!(negated.windings_of(Hand::WithTheTurn).is_empty());
        assert!(negated.null_windings().is_empty());
        assert_eq!(
            negated.windings_past_the_hand(),
            (0..6)
                .map(|character| winding(character, 6))
                .collect::<Vec<_>>()
        );
        assert!(negated.split().is_negative_definite());
    }

    /// The wholly-null pole. `Q(v) = 0` for every `v`, so every passage is on the null cone and no
    /// hand is returned anywhere.
    #[test]
    fn the_zero_circulant_returns_nothing_on_every_passage() {
        let reading = winding_inertia(&circulant(&[0, 0, 0, 0, 0])).unwrap();
        assert_eq!(
            reading.split(),
            Inertia {
                positive: 0,
                zero: 5,
                negative: 0
            }
        );
        assert_eq!(reading.null_windings().len(), 5);
        assert!(reading.windings_past_the_hand().is_empty());
        assert!(reading.windings_of(Hand::WithTheTurn).is_empty());
    }

    /// §2b: *"`A` and `−A` have swapped inertia, so which side is called positive is a convention —
    /// a hand. […] What no frame touches is the split."* Both halves are asserted: the hands swap,
    /// and the shape of the split is carried across unchanged.
    #[test]
    fn the_two_hands_swap_under_negation_while_the_split_does_not() {
        let mut swapped_hands = 0;
        let mut saw_an_asymmetric_split = false;
        for first_row in [
            vec![0, 1, 1],
            vec![0, 1, 0, 1],
            vec![0, 2, 3, 3, 2],
            vec![1, -2, 3, -4, 3, -2],
        ] {
            let form = circulant(&first_row);
            let forward = winding_inertia(&form).unwrap();
            let reversed = winding_inertia(&form.negated()).unwrap();
            for (here, there) in forward.passages.iter().zip(&reversed.passages) {
                assert_eq!(here.character, there.character);
                assert_eq!(here.winding, there.winding);
                assert_eq!(
                    there.returns,
                    match here.returns {
                        PassageReturn::Handed(hand) => PassageReturn::Handed(hand.reversed()),
                        PassageReturn::OnTheNullCone => PassageReturn::OnTheNullCone,
                    },
                    "negation must swap the hand of character {}",
                    here.character
                );
                if here.returns != there.returns {
                    swapped_hands += 1;
                }
            }
            let (before, after) = (forward.split(), reversed.split());
            assert_eq!(before.positive, after.negative);
            assert_eq!(before.negative, after.positive);
            assert_eq!(before.zero, after.zero, "no frame touches the null cone");
            // `circ(0,1,0,1)` has split `(1,2,1)`, which is its own reverse. The hands still swap on
            // every handed passage, and that is what the convention claim is about — so the
            // aggregate is only required to move *somewhere* in the family.
            saw_an_asymmetric_split |= before != after;
        }
        assert!(
            swapped_hands >= 12,
            "only {swapped_hands} passages changed hand, so the negation was barely visible"
        );
        assert!(
            saw_an_asymmetric_split,
            "every fixture had a self-reversing split, so the aggregate half of the claim is vacuous"
        );
    }

    // -----------------------------------------------------------------------------------------
    // the certificates

    /// Every passage carries a Sturm proof against `det(xI − C)` — a polynomial produced by a
    /// determinant, which knows nothing of characters. §8: grade the implementation, so the
    /// certificate is re-checked here rather than trusted.
    #[test]
    fn every_passage_is_sturm_certified_against_the_characteristic_polynomial() {
        for first_row in [
            vec![0, 1, 1],
            vec![0, 1, 0, 1],
            vec![0, 2, 3, 3, 2],
            vec![1, -2, 3, -4, 3, -2],
            vec![3, -1, 0, 2, -5, 2, 0, -1],
        ] {
            let form = circulant(&first_row);
            let reading = winding_inertia(&form).unwrap();
            for passage in &reading.passages {
                assert_eq!(
                    passage.certificate.polynomial, reading.characteristic_polynomial,
                    "the certificate must be against the determinant's polynomial"
                );
                assert_eq!(
                    passage
                        .certificate
                        .certificate
                        .variations_at_lower
                        .checked_sub(passage.certificate.certificate.variations_at_upper),
                    Some(1),
                    "an isolating certificate carries exactly one root"
                );
                // The character route's enclosure sits inside the interval Sturm certified.
                assert!(
                    passage.certificate.isolating_interval.lower <= passage.scaled_enclosure.lower
                        && passage.scaled_enclosure.upper
                            <= passage.certificate.isolating_interval.upper
                );
                // The enclosure really does place the passage on the side its hand claims.
                match passage.returns {
                    PassageReturn::Handed(Hand::WithTheTurn) => {
                        assert!(passage.scaled_enclosure.lower.is_positive())
                    }
                    PassageReturn::Handed(Hand::AgainstTheTurn) => {
                        assert!(passage.scaled_enclosure.upper.is_negative())
                    }
                    PassageReturn::OnTheNullCone => {
                        assert!(
                            !passage.scaled_enclosure.lower.is_positive()
                                && !passage.scaled_enclosure.upper.is_negative()
                        )
                    }
                }
            }
            // The characteristic polynomial's degree is the number of DISTINCT eigenvalues, which is
            // strictly below the extent whenever a character and its conjugate share a value.
            assert!(reading.characteristic_polynomial.degree() >= 1);
        }
    }

    /// The null witness is exact and finite, and it is re-multiplied here rather than believed.
    #[test]
    fn a_null_passage_carries_a_cyclotomic_divisor_that_really_divides_the_symbol() {
        let mut witnessed = 0;
        for first_row in [
            vec![0, 1, 0, 1],
            vec![2, -1, 0, 0, 0, -1],
            vec![1, -2, 3, -4, 3, -2],
            vec![0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 1],
        ] {
            let reading = winding_inertia(&circulant(&first_row)).unwrap();
            for passage in &reading.passages {
                match (&passage.returns, &passage.null_witness) {
                    (PassageReturn::OnTheNullCone, Some(witness)) => {
                        assert_eq!(witness.order, passage.star_polygon.points);
                        assert!(
                            witness.verify(&reading.symbol),
                            "Phi_{} * quotient must reproduce the symbol of {first_row:?}",
                            witness.order
                        );
                        witnessed += 1;
                    }
                    (PassageReturn::OnTheNullCone, None) => {
                        panic!("a null passage without a witness is an unproved zero")
                    }
                    (PassageReturn::Handed(_), Some(_)) => {
                        panic!("a handed passage must carry no null witness")
                    }
                    (PassageReturn::Handed(_), None) => {}
                }
            }
        }
        assert!(
            witnessed >= 8,
            "the witness check saw {witnessed} nulls; a control that never fires is a defect report"
        );
    }

    /// Niven's rational values and the Sturm isolation are two routes to the same table, and the
    /// construction refuses when they disagree. Both branches are exhibited: `C_12` has rational
    /// entries at the divisor positions and genuine irrationals elsewhere.
    #[test]
    fn the_star_table_carries_nivens_rationals_and_sturms_irrationals_and_they_agree() {
        let table = StarTable::found(12).unwrap();
        // m = 0, 2, 3, 4, 6 have n/gcd(m,n) in {1, 6, 4, 3, 2}: rational, by Niven.
        for (step, expected) in [(0_usize, 2_i64), (2, 1), (3, 0), (4, -1), (6, -2)] {
            assert!(table.is_exact(step), "step {step} must be exactly rational");
            let value = table.value(step).unwrap();
            assert!(value.is_point());
            assert_eq!(value.lower, Rat::from_integer(BigInt::from(expected)));
        }
        // m = 1, 5 are 2cos(pi/6) = sqrt 3 and 2cos(5pi/6) = -sqrt 3: genuinely irrational.
        for step in [1_usize, 5] {
            assert!(!table.is_exact(step), "step {step} must not be rational");
            let value = table.value(step).unwrap();
            assert!(!value.is_point());
        }
        // Descending in m, which is what makes the ordering the labelling.
        for step in 1..=6 {
            assert!(
                table.value(step).unwrap().upper <= table.value(step - 1).unwrap().lower,
                "2cos(2*pi*m/n) must strictly decrease in m"
            );
        }
    }

    /// A form whose entries are not integers at all. The scaling path fires, the symbol comes out
    /// primitive and integral, and the split does not move — a positive scale changes no hand.
    #[test]
    fn a_fractional_circulant_is_scaled_to_a_primitive_symbol_and_the_split_does_not_move() {
        let fractional = SymmetricCirculant::from_first_row(vec![
            Rat::new(BigInt::from(1), BigInt::from(3)),
            Rat::new(BigInt::from(-1), BigInt::from(2)),
            Rat::new(BigInt::from(5), BigInt::from(6)),
            Rat::new(BigInt::from(5), BigInt::from(6)),
            Rat::new(BigInt::from(-1), BigInt::from(2)),
        ])
        .unwrap();
        let (scale, symbol) = fractional.integral_symbol();
        assert_eq!(scale, Rat::from_integer(BigInt::from(6)));
        assert_eq!(
            symbol,
            vec![
                BigInt::from(2),
                BigInt::from(-3),
                BigInt::from(5),
                BigInt::from(5),
                BigInt::from(-3)
            ]
        );
        let reading = winding_inertia(&fractional).unwrap();
        assert_eq!(
            reading.split(),
            inertia(&fractional.as_symmetric_form().unwrap())
        );
        // The unscaled enclosure is the scaled one divided back by a positive rational, so it lands
        // on the same side.
        for passage in &reading.passages {
            let own = passage.enclosure(&reading.integral_scale);
            assert_eq!(
                own.lower.is_negative(),
                passage.scaled_enclosure.lower.is_negative()
            );
            assert_eq!(
                own.upper.is_positive(),
                passage.scaled_enclosure.upper.is_positive()
            );
        }
        assert!(reading.split().is_indefinite());
    }

    // -----------------------------------------------------------------------------------------
    // grown material

    /// Not a fixture: a circuit the machine grew, read on a cyclic receiver.
    ///
    /// The entries are conduction counted by displacement class, so they are whatever the growth put
    /// there — and the test asserts they are beyond `{0,1}` so the law is visibly not a property of
    /// the adjacency fixture.
    ///
    /// All three schedules are grown because the net identifier is a *schedule coordinate*, so the
    /// charts genuinely differ. The claim under test is the one that survives that: the character
    /// route and the elimination return one split on every chart. The schedule dependence is
    /// **measured here rather than asserted away**, because an invariant is only visible across two
    /// frames and a suite that never varied the frame could not tell the two apart.
    #[test]
    fn a_grown_circuit_read_on_a_cyclic_receiver_returns_its_passages_by_winding() {
        let table = standard_cells();
        let mut readings = Vec::new();
        for schedule in Schedule::ALL {
            let growth = grow(&table, "brent-kung-adder", &[8, 8, 1], schedule)
                .expect("the standard cells grow an eight-bit adder");
            let complex = found_complex(&growth, ComplexAperture::DIVISION)
                .expect("the growth founds its complex");
            assert!(
                complex.arcs.len() > 100,
                "the grown material must be substantial: {} arcs",
                complex.arcs.len()
            );
            for extent in [5_usize, 7, 9] {
                let receiver = cyclic_receiver_of_growth(&complex, extent).unwrap();
                assert!(
                    receiver.first_row().iter().any(|entry| *entry > Rat::one()),
                    "the grown receiver must carry entries beyond {{0,1}}: {:?}",
                    receiver.first_row()
                );
                let reading = winding_inertia(&receiver).unwrap();
                assert_eq!(
                    reading.split(),
                    inertia(&receiver.as_symmetric_form().unwrap()),
                    "grown extent {extent} under {}",
                    schedule.name()
                );
                assert_eq!(reading.passages.len(), extent);
                // Every passage is named, and the principal one carries the whole conduction.
                assert_eq!(reading.passage(0).unwrap().winding, Rat::zero());
                readings.push((schedule, extent, reading));
            }
        }

        // The law fires on this material rather than returning a trivial reading: at least one grown
        // receiver is genuinely indefinite, so both cones are occupied.
        assert!(
            readings
                .iter()
                .any(|(_, _, reading)| reading.split().is_indefinite()),
            "a grown family in which no receiver is indefinite exercises nothing"
        );
        assert!(
            readings
                .iter()
                .any(|(_, _, reading)| !reading.windings_past_the_hand().is_empty()),
            "no grown passage wound past the hand, so the naming was never exercised"
        );

        // The frame really moves. Folding a schedule-allocated net identifier modulo `n` reads the
        // schedule along with the conduction, so at least one extent must return different splits
        // under different schedules. If none did, this whole sweep would be one chart read three
        // times and the agreement above would carry no evidence about frames.
        let mut moved_with_the_schedule = Vec::new();
        for extent in [5_usize, 7, 9] {
            let splits: Vec<Inertia> = readings
                .iter()
                .filter(|(_, size, _)| *size == extent)
                .map(|(_, _, reading)| reading.split())
                .collect();
            assert_eq!(splits.len(), 3);
            if splits.windows(2).any(|pair| pair[0] != pair[1]) {
                moved_with_the_schedule.push((extent, splits));
            }
        }
        assert!(
            !moved_with_the_schedule.is_empty(),
            "no grown chart moved with the expansion schedule, so the three schedules produced one \
             frame and the cross-check never crossed anything"
        );
    }

    // -----------------------------------------------------------------------------------------
    // the exact machinery, checked directly

    #[test]
    fn the_cyclotomic_recursion_returns_the_classical_polynomials() {
        let expect = |order: usize, coefficients: &[i64]| {
            assert_eq!(
                primitive_integer(&cyclotomic_polynomial(order)),
                coefficients
                    .iter()
                    .map(|value| BigInt::from(*value))
                    .collect::<Vec<_>>(),
                "Phi_{order}"
            );
        };
        expect(1, &[-1, 1]);
        expect(2, &[1, 1]);
        expect(3, &[1, 1, 1]);
        expect(4, &[1, 0, 1]);
        expect(6, &[1, -1, 1]);
        expect(12, &[1, 0, -1, 0, 1]);
    }

    #[test]
    fn the_characteristic_polynomial_of_a_circulant_is_the_determinant_it_claims_to_be() {
        // circ(0,1,1) = the triangle: eigenvalues 2, -1, -1, so det(xI - C) = (x-2)(x+1)^2.
        let triangle =
            characteristic_polynomial(&[BigInt::zero(), BigInt::one(), BigInt::one()]).unwrap();
        assert_eq!(
            primitive_integer(&triangle),
            vec![
                BigInt::from(-2),
                BigInt::from(-3),
                BigInt::zero(),
                BigInt::one()
            ]
        );
        // The squarefree part drops the repeated root and keeps both values.
        assert_eq!(
            primitive_integer(&squarefree_part(&triangle)),
            vec![BigInt::from(-2), BigInt::from(-1), BigInt::one()]
        );
    }

    #[test]
    fn the_dickson_polynomial_carries_every_star_value_as_a_root() {
        // n = 4: D_4 - 2 has the squarefree part x^3 - 4x, roots 2, 0, -2.
        assert_eq!(
            primitive_integer(&squarefree_part(&dickson_less_two(4))),
            vec![
                BigInt::zero(),
                BigInt::from(-4),
                BigInt::zero(),
                BigInt::one()
            ]
        );
        // n = 6: x^4 - 5x^2 + 4, roots 2, 1, -1, -2.
        assert_eq!(
            primitive_integer(&squarefree_part(&dickson_less_two(6))),
            vec![
                BigInt::from(4),
                BigInt::zero(),
                BigInt::from(-5),
                BigInt::zero(),
                BigInt::one()
            ]
        );
    }
}
