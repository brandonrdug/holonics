//! **An identity is two constructions with one face.**
//!
//! For a configuration variety `V`, a finite receiver family `F = {f_1 … f_m}` and a declared
//! monomial family `Mon(F)`, the **face map** sends a formal combination of monomials in `F` to the
//! function it denotes on `V`. Its kernel `Id(V, F)` is the identities. This module computes,
//! certifies, closes and compares that kernel for the two-sided-angle configurations of
//! `docs/plans/THE_IDENTITIES_OF_A_CONFIGURATION_ARE_THE_KERNEL_OF_ITS_FACE_MAP.md` (I1–I8, as
//! corrected by the September 19 audit).
//!
//! # What is returned, and what is not claimed
//!
//! The four corrections that make this honest are enforced by the types, not by prose:
//!
//! - **`ker E` is a candidate space.** [`KernelReading`] is not a return. Every true identity of
//!   the declared family lies in it for valid samples, but finite sampling may leave **spurious**
//!   directions, and a returned basis vector is not thereby an identity. Only
//!   [`CertifiedIdentity`] — a vector whose exact substitution on **every** declared chart is the
//!   zero polynomial — is an identity.
//! - **`rank E` is the sampled rank until certification.** [`KernelReading::sampled_rank`] is named
//!   sampled and is a **lower bound** on the dimension of the received filtration: one sample at
//!   `x = 0` gives rank 1 for `{1, x, x²}` whose true filtered dimension is 3. Only after every
//!   basis vector is certified does [`AtlasReturn::filtered_dimension`] equal that dimension, and
//!   for the graded families here it is the **cumulative** Hilbert function through the declared
//!   degree, never a single graded piece.
//! - **A chart family owes coverage of every component.** [`Configuration::coverage`] carries the
//!   declared statement and [`Configuration::charts`] the charts it names; certification runs on
//!   **all** of them. `a_single_chart_wrongly_certifies_the_galilean_collapse` in this module's
//!   tests is the falsifier: the `k = 0` fibre of the two-sided circle has two components
//!   `C = ±1`, the principal winding covers only `C = +1`, and that chart alone certifies `C − 1`,
//!   which the half-turn winding refuses with an exact counterexample point. This is `V(xy)`'s
//!   `y = 0` chart wrongly certifying `y`, in the configuration this atlas is for.
//! - **Buchberger closure certifies reductions inside `J`, not `J = ker`.** [`GroebnerClosure`] is
//!   a basis **of the ideal supplied**; `{x}` is already a Gröbner basis and does not generate
//!   `⟨x, y⟩`. [`BoundedDegreeCompleteness`] therefore returns *bounded-degree* completeness —
//!   every certified kernel vector reduces to zero modulo the closure — and names the remaining
//!   all-degree ideal obligation in [`BoundedDegreeCompleteness::remaining_obligation`] rather than
//!   discharging it.
//! - **A collapse can create relations.** [`CollapseComparison`] computes the specialized kernel
//!   **independently** and reduces it against the transported generic ideal; whatever does not
//!   reduce to zero is returned as [`CollapseComparison::extra_relations`], with the two-chart and
//!   four-chart declarations of the same collapse returning different answers on purpose.
//!
//! The filtered Hilbert dimension counts **independent algebraic faces**. It is not encoded bits,
//! not runtime and not preservation of continuing conduct; [`AtlasReturn::certificate_terms`] and
//! [`AtlasReturn::elapsed_millis`] are the separately measured codec and check costs.
//!
//! # Owners composed
//!
//! [`holonics::exact_linear::ExactRatMatrix::rank`] and
//! [`holonics::exact_linear::ExactRatMatrix::kernel_basis`] carry every solve; this module never
//! eliminates. [`crate::matroid_chow`] reads the column matroid **at its supported scope** — it
//! accepts simple matroids presented by a complete rank function over `2^|E|` subsets, so a
//! 130-column family is refused by extent and the simplification (loops, parallel classes) plus the
//! circuit of each certified identity is returned instead. `derivation_atlas` route homology is
//! **not** a syzygy resolution of these identities without a connecting chain map, and none is
//! supplied here. `Millennium/Border.lean` concerns degeneration and receiver blindness; the
//! Buchberger completion below is implemented here and is not inferred from that filename.
//!
//! # Lean correspondence
//!
//! | Lean | Rust |
//! |---|---|
//! | `twoSidedPythagoras` | [`two_sided_angle`]'s certified generator |
//! | `twoSidedCosineAddition` | [`two_sided_addition`]'s certified `a₁` |
//! | `twoSidedSineAddition` | [`two_sided_addition`]'s certified `a₂` |
//! | `galileanPrincipalChartIsNotTheFibre` | `a_single_chart_wrongly_certifies_the_galilean_collapse` |
//! | `transferredLawOfSinesKillingPart` | [`helical_triple`]'s certified `E₁` |
//! | `transferredLawOfSinesReciprocalPart` | [`helical_triple`]'s certified `E₂` |
//!
//! The Lean owner is `Geometry/TwoSidedIdentityAtlas.lean`. Lean is exterior verification, never
//! the discovery: each theorem lowers to `field_simp; ring` or `ring`, and the denominator and
//! domain obligations travel as hypotheses.

use std::cmp::Ordering;
use std::collections::{BTreeMap, BTreeSet};
use std::time::Instant;

use num_bigint::BigInt;
use num_traits::{One, Zero};
use holonics::geometry::{Rat, RatVec3, ScrewGenerator};
use serde::Serialize;
use thiserror::Error;

use holonics::exact_linear::{ExactLinearError, ExactRatMatrix};

#[cfg(test)]
mod tests;

// ---------------------------------------------------------------------------------------------
// Declared sizes, bounded before the work they size.
// ---------------------------------------------------------------------------------------------

/// The largest declared monomial family this owner will evaluate.
///
/// This is an apparatus ceiling: the evaluation matrix is `N × |Mon|` and its reduction is cubic
/// in `|Mon|`. A family past it is refused before work begins; the refusal does not change the
/// mathematics of the declared family.
pub const MONOMIAL_CEILING: usize = 512;

/// The largest sample population a single walk will take.
pub const SAMPLE_CEILING: usize = 2048;

/// The largest parameter count a chart may declare.
pub const PARAMETER_CEILING: usize = 32;

/// How many times a walk may answer a refused basis vector by adding its counterexample point and
/// re-reading the kernel. Exceeding it returns an incomplete bounded-search refusal.
pub const RESAMPLE_CEILING: usize = 6;

/// The largest number of S-pairs a Buchberger completion will form.
pub const S_PAIR_CEILING: usize = 8192;

/// The largest number of single-term reductions one normal form may take.
pub const REDUCTION_STEP_CEILING: usize = 200_000;

/// The largest ground set handed to [`crate::matroid_chow::Matroid::from_rank_table`], whose
/// presentation is the complete rank function over `2^|E|` subsets.
pub const CHOW_GROUND_CEILING: usize = 10;

/// Typed refusals. Nothing below panics on an operand a caller can supply.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum IdentityAtlasError {
    #[error("a polynomial over {declared} variables met an exponent vector of length {found}")]
    VariableCountMismatch { declared: usize, found: usize },
    #[error("polynomial operations require matching variable counts ({left} and {right})")]
    PolynomialShapeMismatch { left: usize, right: usize },
    #[error("polynomial exponent overflow during {operation}")]
    ExponentOverflow { operation: &'static str },
    #[error("polynomial total degree overflow")]
    TotalDegreeOverflow,
    #[error("the declared monomial family has {found} members, past the ceiling of {ceiling}")]
    MonomialCeiling { found: usize, ceiling: usize },
    #[error("the walk asked for {found} samples, past the ceiling of {ceiling}")]
    SampleCeiling { found: usize, ceiling: usize },
    #[error("a chart declares {found} parameters, past the ceiling of {ceiling}")]
    ParameterCeiling { found: usize, ceiling: usize },
    #[error(
        "chart `{chart}` declares {declared} receiver numerators but the family names {named} receivers"
    )]
    ChartWidthMismatch {
        chart: String,
        declared: usize,
        named: usize,
    },
    #[error(
        "chart `{chart}` speaks {found} parameters where the configuration declares {declared}"
    )]
    ChartParameterMismatch {
        chart: String,
        declared: usize,
        found: usize,
    },
    #[error(
        "chart `{chart}` polynomial has {found} variables where the parameters declare {declared}"
    )]
    ChartVariableCountMismatch {
        chart: String,
        declared: usize,
        found: usize,
    },
    #[error("chart `{chart}` has a zero denominator")]
    ZeroChartDenominator { chart: String },
    #[error("sample refers to chart {found}, but the configuration has only {charts} charts")]
    ChartIndex { found: usize, charts: usize },
    #[error("grid span must be positive, found {found}")]
    InvalidGridSpan { found: i64 },
    #[error("grid span {span} overflows the integer candidate range")]
    GridSpanOverflow { span: i64 },
    #[error("configuration `{name}` declares no chart, so no component of V is covered")]
    NoChart { name: String },
    #[error(
        "chart `{chart}` has a vanishing denominator at the sample point, which its declared domain excludes"
    )]
    DenominatorVanishes { chart: String },
    #[error(
        "the declared candidate grid gave only {found} admissible points where {needed} were needed"
    )]
    GridExhausted { found: usize, needed: usize },
    #[error(
        "{refused} sampled kernel candidates were refused but no admissible counterexample was found"
    )]
    UnresolvedCertification { refused: usize },
    #[error(
        "after {taken} resamples a certified basis was still not reached within the declared search bound"
    )]
    ResampleCeiling { taken: usize },
    #[error("a Buchberger completion formed {formed} S-pairs, past the ceiling of {ceiling}")]
    SPairCeiling { formed: usize, ceiling: usize },
    #[error("a normal form took {taken} reduction steps, past the ceiling of {ceiling}")]
    ReductionCeiling { taken: usize, ceiling: usize },
    #[error("the exact linear carrier refused: {0}")]
    Linear(String),
}

impl From<ExactLinearError> for IdentityAtlasError {
    fn from(error: ExactLinearError) -> Self {
        Self::Linear(error.to_string())
    }
}

fn rational(value: i64) -> Rat {
    Rat::from_integer(BigInt::from(value))
}

// ---------------------------------------------------------------------------------------------
// I1/I2 substrate: an exact sparse multivariate polynomial over Q.
// ---------------------------------------------------------------------------------------------

/// **An exact sparse polynomial over `Q` in a declared number of variables.**
///
/// [source-audit 2026-09-20] `.agents/bin/prior-art
/// 'multivariate polynomial|monomial order|S.?pair|buchberger'` returns no Rust owner:
/// `rational_polynomial` is univariate and bivariate and states so in its own header, and the
/// Lean hits are prose. This is the minimum the face map needs and it is founded here rather than
/// generalized out of `rational_polynomial`, whose Sturm/resultant apparatus is a different object.
///
/// Exponent vectors are dense over the declared variable count, so `BTreeMap` iteration is
/// **lexicographic** and the graded-lex leading term is one linear scan. No `f32`/`f64` occurs.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize)]
pub struct ExactMultivariate {
    variables: usize,
    terms: BTreeMap<Vec<u32>, Rat>,
}

impl ExactMultivariate {
    /// The zero polynomial over a declared variable count.
    pub fn zero(variables: usize) -> Self {
        Self {
            variables,
            terms: BTreeMap::new(),
        }
    }

    /// A constant.
    pub fn constant(variables: usize, value: Rat) -> Self {
        let mut polynomial = Self::zero(variables);
        if !value.is_zero() {
            polynomial.terms.insert(vec![0; variables], value);
        }
        polynomial
    }

    /// The `index`-th variable.
    pub fn variable(variables: usize, index: usize) -> Result<Self, IdentityAtlasError> {
        if index >= variables {
            return Err(IdentityAtlasError::VariableCountMismatch {
                declared: variables,
                found: index + 1,
            });
        }
        let mut exponents = vec![0; variables];
        exponents[index] = 1;
        let mut polynomial = Self::zero(variables);
        polynomial.terms.insert(exponents, Rat::one());
        Ok(polynomial)
    }

    /// A single term.
    pub fn term(
        variables: usize,
        exponents: Vec<u32>,
        coefficient: Rat,
    ) -> Result<Self, IdentityAtlasError> {
        if exponents.len() != variables {
            return Err(IdentityAtlasError::VariableCountMismatch {
                declared: variables,
                found: exponents.len(),
            });
        }
        exponents.iter().try_fold(0u32, |sum, exponent| {
            sum.checked_add(*exponent)
                .ok_or(IdentityAtlasError::TotalDegreeOverflow)
        })?;
        let mut polynomial = Self::zero(variables);
        if !coefficient.is_zero() {
            polynomial.terms.insert(exponents, coefficient);
        }
        Ok(polynomial)
    }

    /// Build from integer-coefficient terms, the form every configuration below is written in.
    pub fn from_integer_terms(
        variables: usize,
        terms: &[(&[u32], i64)],
    ) -> Result<Self, IdentityAtlasError> {
        let mut polynomial = Self::zero(variables);
        for (exponents, coefficient) in terms {
            if exponents.len() != variables {
                return Err(IdentityAtlasError::VariableCountMismatch {
                    declared: variables,
                    found: exponents.len(),
                });
            }
            polynomial.add_term(exponents.to_vec(), rational(*coefficient))?;
        }
        Ok(polynomial)
    }

    fn add_term(
        &mut self,
        exponents: Vec<u32>,
        coefficient: Rat,
    ) -> Result<(), IdentityAtlasError> {
        if exponents.len() != self.variables {
            return Err(IdentityAtlasError::VariableCountMismatch {
                declared: self.variables,
                found: exponents.len(),
            });
        }
        if coefficient.is_zero() {
            return Ok(());
        }
        exponents.iter().try_fold(0u32, |sum, exponent| {
            sum.checked_add(*exponent)
                .ok_or(IdentityAtlasError::TotalDegreeOverflow)
        })?;
        match self.terms.get_mut(&exponents) {
            Some(existing) => {
                *existing += coefficient;
                if existing.is_zero() {
                    self.terms.remove(&exponents);
                }
            }
            None => {
                self.terms.insert(exponents, coefficient);
            }
        }
        Ok(())
    }

    /// The declared variable count.
    pub fn variables(&self) -> usize {
        self.variables
    }

    /// Whether this is the zero polynomial: the certification predicate.
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// The exact term population, never a count standing in for it.
    pub fn terms(&self) -> &BTreeMap<Vec<u32>, Rat> {
        &self.terms
    }

    /// How many terms the certificate carries — a measured **codec** cost, not a Hilbert function.
    pub fn term_count(&self) -> usize {
        self.terms.len()
    }

    /// The total degree, or `None` for the zero polynomial.
    pub fn total_degree(&self) -> Result<Option<u32>, IdentityAtlasError> {
        self.terms
            .keys()
            .map(|key| {
                key.iter().try_fold(0u32, |sum, exponent| {
                    sum.checked_add(*exponent)
                        .ok_or(IdentityAtlasError::TotalDegreeOverflow)
                })
            })
            .collect::<Result<Vec<_>, _>>()
            .map(|degrees| degrees.into_iter().max())
    }

    /// The sum of the bit lengths of every numerator and denominator: the certificate's size.
    pub fn coefficient_bits(&self) -> u64 {
        self.terms
            .values()
            .map(|value| {
                u64::from(value.numer().bits().max(1)) + u64::from(value.denom().bits().max(1))
            })
            .sum()
    }

    /// Sum.
    pub fn plus(&self, other: &Self) -> Result<Self, IdentityAtlasError> {
        if self.variables != other.variables {
            return Err(IdentityAtlasError::PolynomialShapeMismatch {
                left: self.variables,
                right: other.variables,
            });
        }
        let mut sum = self.clone();
        for (exponents, coefficient) in &other.terms {
            sum.add_term(exponents.clone(), coefficient.clone())?;
        }
        Ok(sum)
    }

    /// Difference.
    pub fn minus(&self, other: &Self) -> Result<Self, IdentityAtlasError> {
        if self.variables != other.variables {
            return Err(IdentityAtlasError::PolynomialShapeMismatch {
                left: self.variables,
                right: other.variables,
            });
        }
        let mut difference = self.clone();
        for (exponents, coefficient) in &other.terms {
            difference.add_term(exponents.clone(), -coefficient)?;
        }
        Ok(difference)
    }

    /// Scaling by an exact rational.
    pub fn scaled(&self, factor: &Rat) -> Self {
        let mut scaled = Self::zero(self.variables);
        if factor.is_zero() {
            return scaled;
        }
        for (exponents, coefficient) in &self.terms {
            scaled.terms.insert(exponents.clone(), coefficient * factor);
        }
        scaled
    }

    /// Product.
    pub fn times(&self, other: &Self) -> Result<Self, IdentityAtlasError> {
        if self.variables != other.variables {
            return Err(IdentityAtlasError::PolynomialShapeMismatch {
                left: self.variables,
                right: other.variables,
            });
        }
        let mut product = Self::zero(self.variables);
        for (left, left_coefficient) in &self.terms {
            for (right, right_coefficient) in &other.terms {
                let exponents: Vec<u32> = left
                    .iter()
                    .zip(right)
                    .map(|(a, b)| {
                        a.checked_add(*b)
                            .ok_or(IdentityAtlasError::ExponentOverflow {
                                operation: "multiplication",
                            })
                    })
                    .collect::<Result<_, _>>()?;
                product.add_term(exponents, left_coefficient * right_coefficient)?;
            }
        }
        Ok(product)
    }

    /// Repeated product; `powered(0)` is one.
    pub fn powered(&self, mut exponent: u32) -> Result<Self, IdentityAtlasError> {
        let mut result = Self::constant(self.variables, Rat::one());
        let mut base = self.clone();
        while exponent != 0 {
            if exponent & 1 == 1 {
                result = result.times(&base)?;
            }
            exponent >>= 1;
            if exponent != 0 {
                base = base.times(&base)?;
            }
        }
        Ok(result)
    }

    /// The exact value at a rational point.
    pub fn evaluate(&self, point: &[Rat]) -> Result<Rat, IdentityAtlasError> {
        if point.len() != self.variables {
            return Err(IdentityAtlasError::VariableCountMismatch {
                declared: self.variables,
                found: point.len(),
            });
        }
        let mut total = Rat::zero();
        for (exponents, coefficient) in &self.terms {
            let mut value = coefficient.clone();
            for (slot, exponent) in exponents.iter().enumerate() {
                value *= num_traits::Pow::pow(&point[slot], *exponent);
            }
            total += value;
        }
        Ok(total)
    }

    /// The graded-lexicographic leading exponent vector, with its coefficient.
    ///
    /// Graded lex: total degree first, then the lexicographic order on exponent vectors with
    /// variable 0 most significant. It is a monomial order, which is what completion needs.
    pub fn leading(&self) -> Option<(&Vec<u32>, &Rat)> {
        self.terms
            .iter()
            .max_by(|(left, _), (right, _)| graded_lex(left, right))
    }

    /// Substitute a value for some variables and re-index the rest.
    ///
    /// `assignment[i]` is the value variable `i` takes, or `None` to retain it; `retained` lists the
    /// retained variables in their new order. This is how a collapse transports a generic identity.
    pub fn specialized(
        &self,
        assignment: &[Option<Rat>],
        retained: &[usize],
    ) -> Result<Self, IdentityAtlasError> {
        if assignment.len() != self.variables {
            return Err(IdentityAtlasError::VariableCountMismatch {
                declared: self.variables,
                found: assignment.len(),
            });
        }
        let mut slot = BTreeMap::new();
        for (new, old) in retained.iter().enumerate() {
            slot.insert(*old, new);
        }
        let mut out = Self::zero(retained.len());
        for (exponents, coefficient) in &self.terms {
            let mut value = coefficient.clone();
            let mut kept = vec![0u32; retained.len()];
            for (index, exponent) in exponents.iter().enumerate() {
                match (&assignment[index], slot.get(&index)) {
                    (Some(number), _) => {
                        for _ in 0..*exponent {
                            value *= number;
                        }
                    }
                    (None, Some(position)) => kept[*position] = *exponent,
                    (None, None) => {
                        return Err(IdentityAtlasError::VariableCountMismatch {
                            declared: retained.len(),
                            found: index + 1,
                        });
                    }
                }
            }
            out.add_term(kept, value)?;
        }
        Ok(out)
    }

    /// The polynomial written against declared variable names, for a receipt a reader can check.
    pub fn written(&self, names: &[String]) -> String {
        if self.terms.is_empty() {
            return "0".to_owned();
        }
        let mut ordered: Vec<(&Vec<u32>, &Rat)> = self.terms.iter().collect();
        ordered.sort_by(|(left, _), (right, _)| graded_lex(right, left));
        let mut written = String::new();
        for (exponents, coefficient) in ordered {
            let negative = *coefficient < Rat::zero();
            let magnitude = if negative {
                -coefficient.clone()
            } else {
                coefficient.clone()
            };
            if written.is_empty() {
                if negative {
                    written.push('-');
                }
            } else {
                written.push_str(if negative { " - " } else { " + " });
            }
            let constant_term = exponents.iter().all(|exponent| *exponent == 0);
            if !magnitude.is_one() || constant_term {
                written.push_str(&format!("{}", magnitude));
                if !constant_term {
                    written.push('*');
                }
            }
            let mut first = true;
            for (index, exponent) in exponents.iter().enumerate() {
                if *exponent == 0 {
                    continue;
                }
                if !first {
                    written.push('*');
                }
                first = false;
                let name = names
                    .get(index)
                    .cloned()
                    .unwrap_or_else(|| format!("x{index}"));
                written.push_str(&name);
                if *exponent > 1 {
                    written.push_str(&format!("^{exponent}"));
                }
            }
        }
        written
    }
}

/// The graded-lexicographic order on exponent vectors: total degree, then lex.
fn graded_lex(left: &[u32], right: &[u32]) -> Ordering {
    let left_degree: u64 = left.iter().map(|value| u64::from(*value)).sum();
    let right_degree: u64 = right.iter().map(|value| u64::from(*value)).sum();
    left_degree.cmp(&right_degree).then_with(|| left.cmp(right))
}

// ---------------------------------------------------------------------------------------------
// I1: configurations with exact points, a declared domain, and a coverage statement.
// ---------------------------------------------------------------------------------------------

/// **A declared monomial family over a named receiver family.**
///
/// The contract's `Mon_d(F)`, generalized to the *declared* families the two-sided configurations
/// actually need: the curvature `k` is a receiver whose own degree is bounded separately, so an
/// identity uniform in `k` fits a family a fifth the size of the total-degree one.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ReceiverFamily {
    names: Vec<String>,
    head: usize,
    head_degree: u32,
    tail_degree: u32,
    monomials: Vec<Vec<u32>>,
}

impl ReceiverFamily {
    /// Every monomial of total degree at most `degree` in the named receivers.
    pub fn total_degree(names: &[&str], degree: u32) -> Result<Self, IdentityAtlasError> {
        Self::graded_with_tail(names, names.len(), degree, 0)
    }

    /// Monomials of degree at most `head_degree` over the first `head` receivers **and** at most
    /// `tail_degree` over the rest.
    ///
    /// The tail is the parameter side — the curvature `k` — and bounding it separately is what
    /// keeps `C² + k S² − 1` and the addition laws inside a family small enough to reduce quickly.
    pub fn graded_with_tail(
        names: &[&str],
        head: usize,
        head_degree: u32,
        tail_degree: u32,
    ) -> Result<Self, IdentityAtlasError> {
        let width = names.len();
        let mut monomials = Vec::new();
        let mut current = vec![0u32; width];
        loop {
            let head_sum: u32 = current[..head.min(width)].iter().sum();
            let tail_sum: u32 = current[head.min(width)..].iter().sum();
            if head_sum <= head_degree && tail_sum <= tail_degree {
                monomials.push(current.clone());
                if monomials.len() > MONOMIAL_CEILING {
                    return Err(IdentityAtlasError::MonomialCeiling {
                        found: monomials.len(),
                        ceiling: MONOMIAL_CEILING,
                    });
                }
            }
            // Odometer over the box each slot may reach.
            let mut slot = 0usize;
            loop {
                if slot == width {
                    monomials.sort_by(|left, right| graded_lex(left, right));
                    return Ok(Self {
                        names: names.iter().map(|name| (*name).to_owned()).collect(),
                        head,
                        head_degree,
                        tail_degree,
                        monomials,
                    });
                }
                let ceiling = if slot < head {
                    head_degree
                } else {
                    tail_degree
                };
                if current[slot] < ceiling {
                    current[slot] += 1;
                    break;
                }
                current[slot] = 0;
                slot += 1;
            }
        }
    }

    /// The receiver names, in the order the exponent vectors speak.
    pub fn names(&self) -> &[String] {
        &self.names
    }

    /// The receiver count.
    pub fn width(&self) -> usize {
        self.names.len()
    }

    /// The declared monomials, exhibited whole.
    pub fn monomials(&self) -> &[Vec<u32>] {
        &self.monomials
    }

    /// The maximum total degree any declared monomial reaches: the certification multiplier's
    /// exponent.
    pub fn maximum_total_degree(&self) -> u32 {
        self.monomials
            .iter()
            .map(|monomial| monomial.iter().sum::<u32>())
            .max()
            .unwrap_or(0)
    }

    /// How the family was declared, for the receipt.
    pub fn declaration(&self) -> String {
        if self.head >= self.width() {
            format!(
                "total degree <= {} in {} receivers",
                self.head_degree,
                self.width()
            )
        } else {
            format!(
                "degree <= {} over the first {} receivers and <= {} over the remaining {}",
                self.head_degree,
                self.head,
                self.tail_degree,
                self.width() - self.head
            )
        }
    }

    /// A vector over the declared monomials, read as a polynomial in the receiver variables.
    pub fn polynomial_of(&self, vector: &[Rat]) -> Result<ExactMultivariate, IdentityAtlasError> {
        if vector.len() != self.monomials.len() {
            return Err(IdentityAtlasError::VariableCountMismatch {
                declared: self.monomials.len(),
                found: vector.len(),
            });
        }
        let mut polynomial = ExactMultivariate::zero(self.width());
        for (monomial, coefficient) in self.monomials.iter().zip(vector) {
            polynomial.add_term(monomial.clone(), coefficient.clone())?;
        }
        Ok(polynomial)
    }
}

/// **A rational chart: exact sample points with a declared domain and one nonvanishing denominator.**
///
/// Every receiver is written over the **same** declared denominator, so the domain is the single
/// statement `denominator ≠ 0` and the certification multiplier is one power of it. A polynomial
/// chart declares the denominator `1` and has no domain exclusion at all.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RationalChart {
    name: String,
    parameters: Vec<String>,
    numerators: Vec<ExactMultivariate>,
    denominator: ExactMultivariate,
    domain: String,
}

impl RationalChart {
    /// Declare a chart. The numerator population is one per receiver, in the family's order.
    pub fn new(
        name: &str,
        parameters: &[&str],
        numerators: Vec<ExactMultivariate>,
        denominator: ExactMultivariate,
        domain: &str,
    ) -> Result<Self, IdentityAtlasError> {
        if parameters.len() > PARAMETER_CEILING {
            return Err(IdentityAtlasError::ParameterCeiling {
                found: parameters.len(),
                ceiling: PARAMETER_CEILING,
            });
        }
        let width = parameters.len();
        if denominator.variables() != width {
            return Err(IdentityAtlasError::ChartVariableCountMismatch {
                chart: name.to_owned(),
                declared: width,
                found: denominator.variables(),
            });
        }
        if denominator.is_zero() {
            return Err(IdentityAtlasError::ZeroChartDenominator {
                chart: name.to_owned(),
            });
        }
        if let Some(numerator) = numerators
            .iter()
            .find(|numerator| numerator.variables() != width)
        {
            return Err(IdentityAtlasError::ChartVariableCountMismatch {
                chart: name.to_owned(),
                declared: width,
                found: numerator.variables(),
            });
        }
        Ok(Self {
            name: name.to_owned(),
            parameters: parameters.iter().map(|slot| (*slot).to_owned()).collect(),
            numerators,
            denominator,
            domain: domain.to_owned(),
        })
    }

    /// A chart whose receivers are polynomial: denominator `1`, no excluded locus.
    pub fn polynomial(
        name: &str,
        parameters: &[&str],
        values: Vec<ExactMultivariate>,
    ) -> Result<Self, IdentityAtlasError> {
        let width = parameters.len();
        Self::new(
            name,
            parameters,
            values,
            ExactMultivariate::constant(width, Rat::one()),
            "the whole affine parameter space; the chart is polynomial and excludes nothing",
        )
    }

    /// The chart's declared name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The declared parameter names.
    pub fn parameters(&self) -> &[String] {
        &self.parameters
    }

    /// The declared domain statement.
    pub fn domain(&self) -> &str {
        &self.domain
    }

    /// The common denominator, declared nonvanishing on the domain.
    pub fn denominator(&self) -> &ExactMultivariate {
        &self.denominator
    }

    /// The receiver numerators over that denominator.
    pub fn numerators(&self) -> &[ExactMultivariate] {
        &self.numerators
    }

    /// The exact receiver values at a parameter point, or the refusal its domain declares.
    pub fn receivers_at(&self, point: &[Rat]) -> Result<Vec<Rat>, IdentityAtlasError> {
        let denominator = self.denominator.evaluate(point)?;
        if denominator.is_zero() {
            return Err(IdentityAtlasError::DenominatorVanishes {
                chart: self.name.clone(),
            });
        }
        self.numerators
            .iter()
            .map(|numerator| Ok(numerator.evaluate(point)? / &denominator))
            .collect()
    }
}

/// **A configuration: its receivers, its charts, and the coverage those charts claim.**
///
/// The coverage statement is carried, not inferred. `V(xy)` charted only on `y = 0` would certify
/// `y`; the statement is where a reader sees which components a chart family reaches, and
/// [`walk`] certifies every returned vector on **every** chart named here. The resulting identity is
/// scoped to the union of the supplied chart images; the coverage string is a declaration for that
/// scope, not a machine-proved statement about an ambient variety.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct Configuration {
    name: String,
    family: ReceiverFamily,
    charts: Vec<RationalChart>,
    coverage: String,
    grid_span: i64,
    grid_seed: u64,
}

impl Configuration {
    /// Declare a configuration, checking each chart against the receiver family it serves.
    pub fn new(
        name: &str,
        family: ReceiverFamily,
        charts: Vec<RationalChart>,
        coverage: &str,
        grid_span: i64,
        grid_seed: u64,
    ) -> Result<Self, IdentityAtlasError> {
        if charts.is_empty() {
            return Err(IdentityAtlasError::NoChart {
                name: name.to_owned(),
            });
        }
        if grid_span <= 0 {
            return Err(IdentityAtlasError::InvalidGridSpan { found: grid_span });
        }
        if grid_span
            .checked_mul(2)
            .and_then(|value| value.checked_add(1))
            .is_none()
        {
            return Err(IdentityAtlasError::GridSpanOverflow { span: grid_span });
        }
        let parameters = charts[0].parameters.len();
        for chart in &charts {
            if chart.numerators.len() != family.width() {
                return Err(IdentityAtlasError::ChartWidthMismatch {
                    chart: chart.name.clone(),
                    declared: chart.numerators.len(),
                    named: family.width(),
                });
            }
            if chart.parameters.len() != parameters {
                return Err(IdentityAtlasError::ChartParameterMismatch {
                    chart: chart.name.clone(),
                    declared: parameters,
                    found: chart.parameters.len(),
                });
            }
        }
        Ok(Self {
            name: name.to_owned(),
            family,
            charts,
            coverage: coverage.to_owned(),
            grid_span,
            grid_seed,
        })
    }

    /// The configuration's name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The declared receiver family.
    pub fn family(&self) -> &ReceiverFamily {
        &self.family
    }

    /// The declared charts. Certification runs on all of them.
    pub fn charts(&self) -> &[RationalChart] {
        &self.charts
    }

    /// The declared coverage statement, with its grade, as prose a reader can falsify.
    pub fn coverage(&self) -> &str {
        &self.coverage
    }

    /// The declared parameter count.
    pub fn parameters(&self) -> usize {
        self.charts[0].parameters.len()
    }

    /// The deterministic candidate parameter grid, as a stream of exact integer points.
    ///
    /// Integers, not arbitrary rationals: the evaluation matrix then carries integers of bounded
    /// height, and the reduction's rational growth is the elimination's own and not the sample's.
    pub fn candidate_points(&self, wanted: usize) -> Vec<Vec<Rat>> {
        let mut state = self.grid_seed;
        let mut points = Vec::with_capacity(wanted);
        let span = self.grid_span;
        for _ in 0..wanted {
            let mut point = Vec::with_capacity(self.parameters());
            for _ in 0..self.parameters() {
                state = state
                    .wrapping_mul(6_364_136_223_846_793_005)
                    .wrapping_add(1_442_695_040_888_963_407);
                let drawn = ((state >> 33) % ((2 * span + 1) as u64)) as i64 - span;
                point.push(rational(drawn));
            }
            points.push(point);
        }
        points
    }
}

// ---------------------------------------------------------------------------------------------
// I2: discovery by exact kernel. A candidate SPACE, and the rank is the SAMPLED rank.
// ---------------------------------------------------------------------------------------------

/// **The sampled evaluation and its kernel — a candidate space, not a return.**
///
/// `sampled_rank` is a lower bound on the dimension of the received filtration until every basis
/// vector is certified. One sample at `x = 0` gives rank 1 for `{1, x, x²}` whose filtered
/// dimension is 3.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct KernelReading {
    /// The declared monomial count: the evaluation matrix's column count.
    pub monomials: usize,
    /// How many exact sample points were evaluated, across all charts.
    pub samples: usize,
    /// The rank of `E` **on those samples**. A lower bound on the received filtration's dimension.
    pub sampled_rank: usize,
    /// One basis vector of `ker E` per free column. Candidates; some may be spurious.
    pub kernel: Vec<Vec<Rat>>,
    /// The wall time of the two reductions, measured separately from every algebraic quantity.
    pub elapsed_millis: u128,
}

/// **The evaluation matrix `E` of the face map at a declared sample population.**
///
/// Exposed so a caller can take [`ExactRatMatrix::rank`] as an **independent** reading of the
/// sampled rank; [`sample_kernel`] derives it by rank–nullity from the one reduction it runs, and
/// the two must agree.
pub fn evaluation_matrix(
    configuration: &Configuration,
    points: &[(usize, Vec<Rat>)],
) -> Result<ExactRatMatrix, IdentityAtlasError> {
    let family = configuration.family();
    let monomials = family.monomials();
    if monomials.len() > MONOMIAL_CEILING {
        return Err(IdentityAtlasError::MonomialCeiling {
            found: monomials.len(),
            ceiling: MONOMIAL_CEILING,
        });
    }
    if points.len() > SAMPLE_CEILING {
        return Err(IdentityAtlasError::SampleCeiling {
            found: points.len(),
            ceiling: SAMPLE_CEILING,
        });
    }
    let mut rows = Vec::with_capacity(points.len());
    for (chart, point) in points {
        if *chart >= configuration.charts().len() {
            return Err(IdentityAtlasError::ChartIndex {
                found: *chart,
                charts: configuration.charts().len(),
            });
        }
        let receivers = configuration.charts()[*chart].receivers_at(point)?;
        let mut row = Vec::with_capacity(monomials.len());
        for monomial in monomials {
            let mut value = Rat::one();
            for (slot, exponent) in monomial.iter().enumerate() {
                for _ in 0..*exponent {
                    value *= &receivers[slot];
                }
            }
            row.push(value);
        }
        rows.push(row);
    }
    Ok(ExactRatMatrix::shaped(rows.len(), monomials.len(), rows)?)
}

/// Evaluate the face map at a declared sample population and read its kernel.
///
/// The solve is [`ExactRatMatrix::kernel_basis`]; this function eliminates nothing itself. The
/// sampled rank is read by rank–nullity **from that same reduction** rather than by a second one,
/// because a second reduced row echelon form of the same matrix is the same elimination at twice
/// the cost. [`evaluation_matrix`] is public so [`ExactRatMatrix::rank`] can be taken independently
/// and compared, which this module's tests do.
pub fn sample_kernel(
    configuration: &Configuration,
    points: &[(usize, Vec<Rat>)],
) -> Result<KernelReading, IdentityAtlasError> {
    let monomials = configuration.family().monomials().len();
    let matrix = evaluation_matrix(configuration, points)?;
    let started = Instant::now();
    let kernel = matrix.kernel_basis()?;
    Ok(KernelReading {
        monomials,
        samples: points.len(),
        sampled_rank: monomials - kernel.len(),
        kernel,
        elapsed_millis: started.elapsed().as_millis(),
    })
}

// ---------------------------------------------------------------------------------------------
// I3: certification by exact substitution, on EVERY declared chart, with a counterexample.
// ---------------------------------------------------------------------------------------------

/// One chart's verdict on one candidate vector.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum ChartVerdict {
    /// The substituted numerator is the zero polynomial on this chart.
    Certified {
        /// The chart that certified it.
        chart: String,
        /// How many terms the substituted numerator passed through before cancelling.
        multiplier_degree: u32,
    },
    /// A nonzero remainder, with an admissible counterexample point sought from it.
    Refused {
        /// The chart that refused.
        chart: String,
        /// How many terms the nonzero remainder carries.
        remainder_terms: usize,
        /// A point of the declared domain at which the candidate is nonzero, when one was found.
        counterexample: Option<Vec<Rat>>,
        /// The nonzero value there.
        value: Option<Rat>,
    },
}

impl ChartVerdict {
    /// Whether this chart certified.
    pub fn certified(&self) -> bool {
        matches!(self, Self::Certified { .. })
    }
}

/// **A certified identity: the whole basis vector, proved on every declared chart.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CertifiedIdentity {
    /// The identity as a polynomial in the receiver variables.
    polynomial: ExactMultivariate,
    /// One verdict per declared chart. Every one is `Certified` for this type to be returned.
    verdicts: Vec<ChartVerdict>,
    /// The total term count of the substituted numerators: the certificate's measured size.
    certificate_terms: usize,
    /// The total coefficient bit length of those numerators.
    certificate_bits: u64,
}

impl CertifiedIdentity {
    pub fn polynomial(&self) -> &ExactMultivariate {
        &self.polynomial
    }
    pub fn verdicts(&self) -> &[ChartVerdict] {
        &self.verdicts
    }
    pub fn certificate_terms(&self) -> usize {
        self.certificate_terms
    }
    pub fn certificate_bits(&self) -> u64 {
        self.certificate_bits
    }
}

/// A refused candidate, kept rather than dropped: the counterexample is what makes the next sample.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RefusedCandidate {
    /// The candidate as a polynomial in the receiver variables.
    polynomial: ExactMultivariate,
    /// The chart verdicts, at least one of which refused.
    verdicts: Vec<ChartVerdict>,
}

impl RefusedCandidate {
    pub fn polynomial(&self) -> &ExactMultivariate {
        &self.polynomial
    }
    pub fn verdicts(&self) -> &[ChartVerdict] {
        &self.verdicts
    }
}

/// Certify one candidate vector by exact substitution on every declared chart.
///
/// With `D` the chart's declared denominator, `N_i` the receiver numerators over it, and `d` the
/// family's maximum total degree, the candidate `Σ c_α f^α` is certified when
/// `Σ_α c_α (Π N_i^{α_i}) D^{d − |α|}` is the **zero polynomial**. That is exact substitution, not
/// a test at points, and it proves the identity wherever `D ≠ 0`.
pub fn certify(
    configuration: &Configuration,
    vector: &[Rat],
    candidate_points: &[Vec<Rat>],
) -> Result<Result<CertifiedIdentity, RefusedCandidate>, IdentityAtlasError> {
    let family = configuration.family();
    let polynomial = family.polynomial_of(vector)?;
    let degree = family.maximum_total_degree();
    let mut verdicts = Vec::with_capacity(configuration.charts().len());
    let mut certificate_terms = 0usize;
    let mut certificate_bits = 0u64;
    let mut refused = false;
    for chart in configuration.charts() {
        let width = chart.parameters().len();
        let mut numerator = ExactMultivariate::zero(width);
        for (monomial, coefficient) in family.monomials().iter().zip(vector) {
            if coefficient.is_zero() {
                continue;
            }
            let mut term = ExactMultivariate::constant(width, coefficient.clone());
            let mut total = 0u32;
            for (slot, exponent) in monomial.iter().enumerate() {
                if *exponent == 0 {
                    continue;
                }
                total += *exponent;
                term = term.times(&chart.numerators()[slot].powered(*exponent)?)?;
            }
            if degree > total {
                term = term.times(&chart.denominator().powered(degree - total)?)?;
            }
            // The certificate's size is what the substitution **carried**, not what survived it: a
            // certified vector's numerator is the zero polynomial, and reporting zero terms would
            // report the answer instead of the cost.
            certificate_terms += term.term_count();
            certificate_bits += term.coefficient_bits();
            numerator = numerator.plus(&term)?;
        }
        if numerator.is_zero() {
            verdicts.push(ChartVerdict::Certified {
                chart: chart.name().to_owned(),
                multiplier_degree: degree,
            });
        } else {
            refused = true;
            let mut counterexample = None;
            let mut value = None;
            for point in candidate_points {
                if chart.denominator().evaluate(point)?.is_zero() {
                    continue;
                }
                let residue = numerator.evaluate(point)?;
                if !residue.is_zero() {
                    counterexample = Some(point.clone());
                    value = Some(residue);
                    break;
                }
            }
            verdicts.push(ChartVerdict::Refused {
                chart: chart.name().to_owned(),
                remainder_terms: numerator.term_count(),
                counterexample,
                value,
            });
        }
    }
    if refused {
        Ok(Err(RefusedCandidate {
            polynomial,
            verdicts,
        }))
    } else {
        Ok(Ok(CertifiedIdentity {
            polynomial,
            verdicts,
            certificate_terms,
            certificate_bits,
        }))
    }
}

// ---------------------------------------------------------------------------------------------
// I4: elementary generators and Buchberger closure of the ideal THEY generate.
// ---------------------------------------------------------------------------------------------

/// One S-pair reduction: a node-to-node edge of I5's graph, kept rather than counted.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SPairReduction {
    /// The two basis positions the pair came from.
    pub pair: (usize, usize),
    /// Whether the coprime-leading-monomial criterion (Buchberger's first) discharged it.
    pub coprime: bool,
    /// Whether the chain criterion (Buchberger's second) discharged it.
    pub chain: bool,
    /// Whether its normal form was zero.
    pub reduced_to_zero: bool,
    /// How many single-term reductions the normal form took.
    pub steps: usize,
}

/// **A Gröbner basis of the ideal supplied — and of nothing else.**
///
/// Buchberger's criterion certifies a basis *of the ideal it was given*. `{x}` is already a Gröbner
/// basis and does not generate `⟨x, y⟩`, so this type never asserts that its ideal is the face-map
/// kernel. That second inclusion is [`BoundedDegreeCompleteness`]'s subject and, for all degrees,
/// its named obligation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct GroebnerClosure {
    /// The declared monomial order.
    order: String,
    /// The completed basis.
    basis: Vec<ExactMultivariate>,
    /// Every S-pair the completion formed, with its verdict.
    reductions: Vec<SPairReduction>,
    /// The wall time of the completion, measured separately.
    elapsed_millis: u128,
}

impl GroebnerClosure {
    pub fn order(&self) -> &str {
        &self.order
    }
    pub fn basis(&self) -> &[ExactMultivariate] {
        &self.basis
    }
    pub fn reductions(&self) -> &[SPairReduction] {
        &self.reductions
    }
    pub fn elapsed_millis(&self) -> u128 {
        self.elapsed_millis
    }
}

/// The normal form of `polynomial` modulo `divisors` under graded lex, with its step count.
pub fn normal_form(
    polynomial: &ExactMultivariate,
    divisors: &[ExactMultivariate],
) -> Result<(ExactMultivariate, usize), IdentityAtlasError> {
    let variables = polynomial.variables();
    let mut working = polynomial.clone();
    let mut remainder = ExactMultivariate::zero(variables);
    let mut steps = 0usize;
    while let Some((exponents, coefficient)) = working.leading() {
        let exponents = exponents.clone();
        let coefficient = coefficient.clone();
        let mut divided = false;
        for divisor in divisors {
            let Some((lead, lead_coefficient)) = divisor.leading() else {
                continue;
            };
            if lead.iter().zip(&exponents).any(|(need, have)| need > have) {
                continue;
            }
            let quotient: Vec<u32> = exponents
                .iter()
                .zip(lead)
                .map(|(have, need)| have - need)
                .collect();
            let factor = &coefficient / lead_coefficient;
            let shift = ExactMultivariate::term(variables, quotient, factor)?;
            working = working.minus(&shift.times(divisor)?)?;
            divided = true;
            steps += 1;
            if steps > REDUCTION_STEP_CEILING {
                return Err(IdentityAtlasError::ReductionCeiling {
                    taken: steps,
                    ceiling: REDUCTION_STEP_CEILING,
                });
            }
            break;
        }
        if !divided {
            remainder.add_term(exponents.clone(), coefficient.clone())?;
            working =
                working.minus(&ExactMultivariate::term(variables, exponents, coefficient)?)?;
        }
    }
    Ok((remainder, steps))
}

fn s_polynomial(
    left: &ExactMultivariate,
    right: &ExactMultivariate,
) -> Result<Option<(ExactMultivariate, bool)>, IdentityAtlasError> {
    let (Some((left_lead, left_coefficient)), Some((right_lead, right_coefficient))) =
        (left.leading(), right.leading())
    else {
        return Ok(None);
    };
    let lcm: Vec<u32> = left_lead
        .iter()
        .zip(right_lead)
        .map(|(a, b)| *a.max(b))
        .collect();
    // Buchberger's first criterion: coprime leading monomials give an S-pair that reduces to zero.
    let coprime = left_lead
        .iter()
        .zip(right_lead)
        .all(|(a, b)| *a == 0 || *b == 0);
    if coprime {
        return Ok(Some((ExactMultivariate::zero(left.variables()), true)));
    }
    let left_shift = ExactMultivariate::term(
        left.variables(),
        lcm.iter().zip(left_lead).map(|(a, b)| a - b).collect(),
        Rat::one() / left_coefficient,
    )?;
    let right_shift = ExactMultivariate::term(
        right.variables(),
        lcm.iter().zip(right_lead).map(|(a, b)| a - b).collect(),
        Rat::one() / right_coefficient,
    )?;
    Ok(Some((
        left_shift.times(left)?.minus(&right_shift.times(right)?)?,
        false,
    )))
}

fn leading_monomial(polynomial: &ExactMultivariate) -> Option<Vec<u32>> {
    polynomial.leading().map(|(exponents, _)| exponents.clone())
}

fn lcm_of(left: &[u32], right: &[u32]) -> Vec<u32> {
    left.iter().zip(right).map(|(a, b)| *a.max(b)).collect()
}

fn divides(divisor: &[u32], dividend: &[u32]) -> bool {
    divisor
        .iter()
        .zip(dividend)
        .all(|(need, have)| need <= have)
}

/// Interreduce a generating set before completion.
///
/// A supplied generator that reduces to zero modulo the others is **redundant** and is dropped; one
/// that reduces to something smaller is replaced by that. This matters here because the generators
/// are kernel basis vectors of a reduced row echelon form — a perfectly good basis of the *space*
/// that is a poor presentation of the *ideal*, and an un-interreduced presentation is what makes a
/// completion explode.
pub fn interreduce(
    generators: &[ExactMultivariate],
) -> Result<Vec<ExactMultivariate>, IdentityAtlasError> {
    let mut ordered: Vec<ExactMultivariate> = generators
        .iter()
        .filter(|generator| !generator.is_zero())
        .cloned()
        .collect();
    ordered.sort_by(|left, right| match (left.leading(), right.leading()) {
        (Some((a, _)), Some((b, _))) => graded_lex(a, b),
        _ => Ordering::Equal,
    });
    let mut kept: Vec<ExactMultivariate> = Vec::new();
    for generator in ordered {
        let (remainder, _) = normal_form(&generator, &kept)?;
        if let Some((_, leading)) = remainder.leading() {
            let scale = Rat::one() / leading;
            kept.push(remainder.scaled(&scale));
        }
    }
    Ok(kept)
}

/// **Buchberger completion of the ideal generated by `generators`, under graded lex.**
///
/// The supplied set is interreduced first, pairs are selected by the **normal strategy** (smallest
/// lcm of leading monomials first), and both of Buchberger's criteria discharge pairs without a
/// reduction: the **product criterion** for coprime leading monomials and the **chain criterion**
/// for a pair whose lcm a third leading monomial divides when the two flanking pairs are already
/// done. Without those the LIFO completion of the Galilean special fibre passed eight thousand
/// S-pairs and refused; with them it is a few dozen.
///
/// This is implemented here. `Millennium/Border.lean` is about degeneration and receiver blindness
/// and supplies no completion engine; nothing about this algorithm is inferred from that filename.
pub fn buchberger(generators: &[ExactMultivariate]) -> Result<GroebnerClosure, IdentityAtlasError> {
    let started = Instant::now();
    let mut basis = interreduce(generators)?;
    let mut pending: BTreeSet<(usize, usize)> = BTreeSet::new();
    for left in 0..basis.len() {
        for right in (left + 1)..basis.len() {
            pending.insert((left, right));
        }
    }
    let mut reductions = Vec::new();
    let mut formed = 0usize;
    while !pending.is_empty() {
        let leads: Vec<Option<Vec<u32>>> = basis.iter().map(leading_monomial).collect();
        // The normal strategy: the pair whose lcm is smallest under the declared order.
        let chosen = pending
            .iter()
            .copied()
            .min_by(|(a_left, a_right), (b_left, b_right)| {
                match (
                    leads[*a_left].as_ref(),
                    leads[*a_right].as_ref(),
                    leads[*b_left].as_ref(),
                    leads[*b_right].as_ref(),
                ) {
                    (Some(al), Some(ar), Some(bl), Some(br)) => {
                        graded_lex(&lcm_of(al, ar), &lcm_of(bl, br))
                    }
                    _ => Ordering::Equal,
                }
            })
            .expect("a nonempty pending set has a minimum");
        pending.remove(&chosen);
        let (left, right) = chosen;
        formed += 1;
        if formed > S_PAIR_CEILING {
            return Err(IdentityAtlasError::SPairCeiling {
                formed,
                ceiling: S_PAIR_CEILING,
            });
        }
        let (Some(left_lead), Some(right_lead)) = (leads[left].as_ref(), leads[right].as_ref())
        else {
            continue;
        };
        // Buchberger's second criterion: a third leading monomial dividing the lcm, whose own two
        // pairs with this one are already processed, discharges this pair.
        let lcm = lcm_of(left_lead, right_lead);
        let chained = (0..basis.len()).any(|third| {
            if third == left || third == right {
                return false;
            }
            let Some(third_lead) = leads[third].as_ref() else {
                return false;
            };
            divides(third_lead, &lcm)
                && !pending.contains(&(left.min(third), left.max(third)))
                && !pending.contains(&(right.min(third), right.max(third)))
        });
        if chained {
            reductions.push(SPairReduction {
                pair: (left, right),
                coprime: false,
                chain: true,
                reduced_to_zero: true,
                steps: 0,
            });
            continue;
        }
        let Some((pair, coprime)) = s_polynomial(&basis[left], &basis[right])? else {
            continue;
        };
        if coprime {
            reductions.push(SPairReduction {
                pair: (left, right),
                coprime: true,
                chain: false,
                reduced_to_zero: true,
                steps: 0,
            });
            continue;
        }
        let (remainder, steps) = normal_form(&pair, &basis)?;
        let reduced_to_zero = remainder.is_zero();
        reductions.push(SPairReduction {
            pair: (left, right),
            coprime: false,
            chain: false,
            reduced_to_zero,
            steps,
        });
        if !reduced_to_zero {
            let scale = Rat::one() / remainder.leading().expect("a nonzero remainder leads").1;
            let position = basis.len();
            basis.push(remainder.scaled(&scale));
            for existing in 0..position {
                pending.insert((existing, position));
            }
        }
    }
    // Reduce to a minimal basis with monic leading coefficients. The declared order makes the
    // normal remainder deterministic for this returned basis; the basis itself need not be the
    // unique reduced Gröbner basis.
    let mut minimal: Vec<ExactMultivariate> = Vec::new();
    for (index, member) in basis.iter().enumerate() {
        let Some((lead, _)) = member.leading() else {
            continue;
        };
        let redundant = basis.iter().enumerate().any(|(other, candidate)| {
            if other == index {
                return false;
            }
            let Some((other_lead, _)) = candidate.leading() else {
                return false;
            };
            let divides = other_lead.iter().zip(lead).all(|(need, have)| need <= have);
            divides && (other_lead != lead || other < index)
        });
        if !redundant {
            let scale = Rat::one() / member.leading().expect("a nonzero member leads").1;
            minimal.push(member.scaled(&scale));
        }
    }
    Ok(GroebnerClosure {
        order: "graded lexicographic, variable 0 most significant".to_owned(),
        basis: minimal,
        reductions,
        elapsed_millis: started.elapsed().as_millis(),
    })
}

/// **I4's reduction step: which certified identities are new generators and which are consequences.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ElementaryReading {
    /// The certified identities that did **not** reduce to zero modulo the ideal generated by the
    /// lower-degree ones: the elementary generators of this configuration at this degree.
    generators: Vec<ExactMultivariate>,
    /// How many certified identities reduced to zero, i.e. are consequences of the generators.
    consequences: usize,
    /// The Gröbner closure of the generators alone — the ideal `J` every completeness claim is
    /// relative to.
    closure: GroebnerClosure,
    /// The reduction steps the reading took: a measured check cost.
    reduction_steps: usize,
}

impl ElementaryReading {
    pub fn generators(&self) -> &[ExactMultivariate] {
        &self.generators
    }
    pub fn consequences(&self) -> usize {
        self.consequences
    }
    pub fn closure(&self) -> &GroebnerClosure {
        &self.closure
    }
    pub fn reduction_steps(&self) -> usize {
        self.reduction_steps
    }
}

/// **Reduce the certified basis by degree and return the new generators.**
///
/// This is I4's first half, in a filtered chart: certified identities are taken in increasing total
/// degree and each is reduced modulo the ideal the earlier ones generate. What survives is new;
/// what reduces to zero is a consequence, and the reduction is its witness. The filtered case is
/// why this is a reduction and not an assumption that `F · Id_(d−1)` is complete — a degree-`d`
/// identity can be an ideal consequence of lower-degree ones without being a **monomial** multiple
/// of them, which is exactly what happens to `C₃² + k S₃² − 1` here.
pub fn elementary_generators(
    certified: &[CertifiedIdentity],
) -> Result<ElementaryReading, IdentityAtlasError> {
    let mut ordered: Vec<(&ExactMultivariate, u32)> = certified
        .iter()
        .map(|identity| {
            identity
                .polynomial()
                .total_degree()
                .map(|degree| (identity.polynomial(), degree.unwrap_or(0)))
        })
        .collect::<Result<_, _>>()?;
    ordered.sort_by_key(|(_, degree)| *degree);
    let mut generators: Vec<ExactMultivariate> = Vec::new();
    let mut closure = buchberger(&generators)?;
    let mut consequences = 0usize;
    let mut reduction_steps = 0usize;
    for (polynomial, _) in ordered {
        let (remainder, steps) = normal_form(polynomial, closure.basis())?;
        reduction_steps += steps;
        if remainder.is_zero() {
            consequences += 1;
        } else {
            generators.push(polynomial.clone());
            closure = buchberger(&generators)?;
        }
    }
    Ok(ElementaryReading {
        generators,
        consequences,
        closure,
        reduction_steps,
    })
}

/// **Bounded-degree completeness, and the all-degree obligation it does not discharge.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct BoundedDegreeCompleteness {
    /// Whether every certified kernel vector reduced to zero modulo the closure.
    every_certified_vector_reduces_to_zero: bool,
    /// The positions of any that did not, kept rather than counted.
    unreduced: Vec<usize>,
    /// The total reduction steps the check took: a measured check cost.
    reduction_steps: usize,
    /// The concrete absent object an all-degree claim would need.
    remaining_obligation: String,
}

impl BoundedDegreeCompleteness {
    pub fn every_certified_vector_reduces_to_zero(&self) -> bool {
        self.every_certified_vector_reduces_to_zero
    }
    pub fn unreduced(&self) -> &[usize] {
        &self.unreduced
    }
    pub fn reduction_steps(&self) -> usize {
        self.reduction_steps
    }
    pub fn remaining_obligation(&self) -> &str {
        &self.remaining_obligation
    }
}

/// Reduce every certified identity modulo the closure of the elementary generators.
///
/// A zero remainder everywhere gives `Id_d(V, F) = J ∩ Span(Mon)`, which is **bounded-degree**
/// completeness. It does not give `J = ker(face map)` in all degrees; that needs elimination from a
/// complete source presentation with denominator saturation, or an independently certified Hilbert
/// bound, and the obligation is returned rather than assumed.
pub fn bounded_degree_completeness(
    certified: &[CertifiedIdentity],
    closure: &GroebnerClosure,
) -> Result<BoundedDegreeCompleteness, IdentityAtlasError> {
    let mut unreduced = Vec::new();
    let mut reduction_steps = 0usize;
    for (index, identity) in certified.iter().enumerate() {
        let (remainder, steps) = normal_form(identity.polynomial(), closure.basis())?;
        reduction_steps += steps;
        if !remainder.is_zero() {
            unreduced.push(index);
        }
    }
    Ok(BoundedDegreeCompleteness {
        every_certified_vector_reduces_to_zero: unreduced.is_empty(),
        unreduced,
        reduction_steps,
        remaining_obligation: "J = ker(face map) in all degrees: elimination from the complete \
             source presentation with denominator saturation, or an independently certified \
             Hilbert bound. Buchberger's criterion certifies a basis of the ideal supplied only."
            .to_owned(),
    })
}

// ---------------------------------------------------------------------------------------------
// I5: the identity matroid, at the scope its owner supports.
// ---------------------------------------------------------------------------------------------

/// Whether the column matroid was admissible at [`crate::matroid_chow`]'s supported scope.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum ChowScope {
    /// The simple ground set is small enough and its characteristic polynomial was read.
    Admitted {
        /// The simple ground set's extent.
        ground: usize,
        /// The matroid's rank.
        rank: usize,
        /// The reduced characteristic polynomial's magnitudes.
        reduced_characteristic: Vec<String>,
    },
    /// The declared refusal, with the reason stated rather than the reading skipped.
    Refused {
        /// Why the owner cannot receive this matroid.
        reason: String,
    },
}

/// **The column matroid's simplification and the circuit of each certified identity.**
///
/// `matroid_chow::Matroid::from_rank_table` is presented by the complete rank function over
/// `2^|E|` subsets and accepts **simple** matroids only, so zero columns (loops) and proportional
/// columns (parallel pairs) must be named before anything is handed over, and a wide family is
/// refused by extent. Both readings are returned; neither is skipped.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ColumnMatroidReading {
    /// The full column count.
    pub ground: usize,
    /// Columns that are identically zero on the samples: the loops.
    pub loops: Vec<usize>,
    /// Proportional column classes of size at least two: the parallel classes.
    pub parallel_classes: Vec<Vec<usize>>,
    /// The simple ground set's extent after removing loops and collapsing parallel classes.
    pub simple_ground: usize,
    /// The support of each certified identity: a sampled dependency, an identity after I3.
    pub identity_supports: Vec<Vec<usize>>,
    /// Whether each such support is a **circuit** — minimally dependent among the sampled columns.
    pub support_is_circuit: Vec<bool>,
    /// The Chow-ring reading of the first identity circuit, or its declared refusal.
    pub chow: ChowScope,
    /// Why the **whole** column matroid is or is not admissible at that owner's scope. A wide
    /// family is refused here rather than mis-presented as something the owner accepts.
    pub full_matroid_scope: ChowScope,
}

/// Read the column matroid of the sampled evaluation at the scope its owners support.
pub fn read_column_matroid(
    configuration: &Configuration,
    points: &[(usize, Vec<Rat>)],
    certified: &[CertifiedIdentity],
) -> Result<ColumnMatroidReading, IdentityAtlasError> {
    let family = configuration.family();
    let monomials = family.monomials();
    let mut columns: Vec<Vec<Rat>> = vec![Vec::with_capacity(points.len()); monomials.len()];
    for (chart, point) in points {
        if *chart >= configuration.charts().len() {
            return Err(IdentityAtlasError::ChartIndex {
                found: *chart,
                charts: configuration.charts().len(),
            });
        }
        let receivers = configuration.charts()[*chart].receivers_at(point)?;
        for (index, monomial) in monomials.iter().enumerate() {
            let mut value = Rat::one();
            for (slot, exponent) in monomial.iter().enumerate() {
                for _ in 0..*exponent {
                    value *= &receivers[slot];
                }
            }
            columns[index].push(value);
        }
    }
    let loops: Vec<usize> = columns
        .iter()
        .enumerate()
        .filter(|(_, column)| column.iter().all(Rat::is_zero))
        .map(|(index, _)| index)
        .collect();
    let mut parallel_classes: Vec<Vec<usize>> = Vec::new();
    let mut assigned: BTreeSet<usize> = loops.iter().copied().collect();
    for left in 0..columns.len() {
        if assigned.contains(&left) {
            continue;
        }
        let mut class = vec![left];
        for right in (left + 1)..columns.len() {
            if assigned.contains(&right) {
                continue;
            }
            if proportional(&columns[left], &columns[right]) {
                class.push(right);
                assigned.insert(right);
            }
        }
        assigned.insert(left);
        if class.len() > 1 {
            parallel_classes.push(class);
        }
    }
    let collapsed: usize = parallel_classes
        .iter()
        .map(|class| class.len() - 1)
        .sum::<usize>();
    let simple_ground = columns.len() - loops.len() - collapsed;

    let mut identity_supports = Vec::new();
    let mut support_is_circuit = Vec::new();
    for identity in certified {
        let mut support: Vec<usize> = Vec::new();
        for (index, monomial) in monomials.iter().enumerate() {
            if identity
                .polynomial()
                .terms()
                .get(monomial)
                .is_some_and(|coefficient| !coefficient.is_zero())
            {
                support.push(index);
            }
        }
        let circuit = support_is_minimal_dependency(&columns, &support)?;
        identity_supports.push(support);
        support_is_circuit.push(circuit);
    }

    let full_matroid_scope = if simple_ground > CHOW_GROUND_CEILING
        || !loops.is_empty()
        || !parallel_classes.is_empty()
    {
        ChowScope::Refused {
            reason: format!(
                "matroid_chow::Matroid::from_rank_table is presented by the complete rank function \
                 over 2^|E| subsets and accepts simple matroids only; this column matroid has \
                 {} elements, {} of them loops, {} parallel class(es), and a simple ground set of \
                 {} against the declared ceiling of {}. The simplification and the identity circuits \
                are returned instead.",
                columns.len(),
                loops.len(),
                parallel_classes.len(),
                simple_ground,
                CHOW_GROUND_CEILING
            ),
        }
    } else {
        ChowScope::Admitted {
            ground: simple_ground,
            rank: rank_of_columns(&columns, &(0..columns.len()).collect::<Vec<_>>())?,
            reduced_characteristic: Vec::new(),
        }
    };
    let chow = chow_reading_of_first_circuit(&identity_supports, &support_is_circuit, &columns)?;

    Ok(ColumnMatroidReading {
        ground: columns.len(),
        loops,
        parallel_classes,
        simple_ground,
        identity_supports,
        support_is_circuit,
        chow,
        full_matroid_scope,
    })
}

fn proportional(left: &[Rat], right: &[Rat]) -> bool {
    let mut ratio: Option<Rat> = None;
    for (a, b) in left.iter().zip(right) {
        match (a.is_zero(), b.is_zero()) {
            (true, true) => continue,
            (true, false) | (false, true) => return false,
            (false, false) => {
                let candidate = b / a;
                match &ratio {
                    Some(fixed) if *fixed != candidate => return false,
                    Some(_) => {}
                    None => ratio = Some(candidate),
                }
            }
        }
    }
    ratio.is_some()
}

fn rank_of_columns(columns: &[Vec<Rat>], subset: &[usize]) -> Result<usize, IdentityAtlasError> {
    if subset.is_empty() {
        return Ok(0);
    }
    let rows = columns[subset[0]].len();
    let entries: Vec<Vec<Rat>> = (0..rows)
        .map(|row| {
            subset
                .iter()
                .map(|index| columns[*index][row].clone())
                .collect()
        })
        .collect();
    let matrix = ExactRatMatrix::shaped(rows, subset.len(), entries)?;
    Ok(matrix.rank()?)
}

fn support_is_minimal_dependency(
    columns: &[Vec<Rat>],
    support: &[usize],
) -> Result<bool, IdentityAtlasError> {
    if support.is_empty() {
        return Ok(false);
    }
    if rank_of_columns(columns, support)? != support.len() - 1 {
        return Ok(false);
    }
    for dropped in 0..support.len() {
        let mut smaller = support.to_vec();
        smaller.remove(dropped);
        if rank_of_columns(columns, &smaller)? != smaller.len() {
            return Ok(false);
        }
    }
    Ok(true)
}

fn chow_reading_of_first_circuit(
    supports: &[Vec<usize>],
    support_is_circuit: &[bool],
    columns: &[Vec<Rat>],
) -> Result<ChowScope, IdentityAtlasError> {
    let Some(support) = supports
        .iter()
        .zip(support_is_circuit)
        .find_map(|(support, is_circuit)| (*is_circuit && support.len() >= 3).then_some(support))
    else {
        return Ok(ChowScope::Refused {
            reason: "no certified identity has a support of three or more columns, so no rank-two \
                     or higher simple matroid is presented"
                .to_owned(),
        });
    };
    let rank = rank_of_columns(columns, support)?;
    // The support of a certified identity whose columns are pairwise non-proportional and
    // spanning is the uniform matroid U(rank, |support|) exactly when every proper subset of that
    // size is independent, which is what `support_is_minimal_dependency` established.
    let matroid = crate::matroid_chow::Matroid::uniform(rank, support.len());
    match matroid {
        Ok(matroid) => {
            let reduced = matroid
                .reduced_characteristic_magnitudes()
                .map_err(|error| IdentityAtlasError::Linear(error.to_string()))?;
            Ok(ChowScope::Admitted {
                ground: support.len(),
                rank,
                reduced_characteristic: reduced
                    .iter()
                    .map(std::string::ToString::to_string)
                    .collect(),
            })
        }
        Err(error) => Ok(ChowScope::Refused {
            reason: format!("matroid_chow refused the identity circuit: {error}"),
        }),
    }
}

// ---------------------------------------------------------------------------------------------
// The walk: discovery, certification with a counterexample-fed resample, and the closure.
// ---------------------------------------------------------------------------------------------

/// **What one configuration returns.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AtlasReturn {
    /// The configuration's name.
    configuration: String,
    /// The declared monomial family's extent and declaration.
    monomials: usize,
    /// How the family was declared.
    declaration: String,
    /// The final sample population.
    samples: usize,
    /// How many times a refused vector's counterexample was fed back as a sample.
    resamples: usize,
    /// The sampled rank. Equal to the filtered dimension **because** every vector certified.
    sampled_rank: usize,
    /// `|Mon| − dim ker`, the cumulative Hilbert function of the received filtration through the
    /// declared degree — independent algebraic faces, not bits and not runtime.
    filtered_dimension: usize,
    /// `dim ker`: the algebraic redundancy of the declared family.
    redundancy: usize,
    /// Every certified identity, exhibited whole.
    identities: Vec<CertifiedIdentity>,
    /// Every candidate that stayed refused, with its counterexample.
    refusals: Vec<RefusedCandidate>,
    /// The total certificate term count: a separately measured codec cost.
    certificate_terms: usize,
    /// The total certificate coefficient bit length.
    certificate_bits: u64,
    /// The wall time of the whole walk, measured separately from every algebraic quantity.
    elapsed_millis: u128,
}

impl AtlasReturn {
    fn from_walk(
        configuration: &Configuration,
        declaration: &str,
        reading: &KernelReading,
        samples: usize,
        resamples: usize,
        identities: Vec<CertifiedIdentity>,
        refusals: Vec<RefusedCandidate>,
        certificate_terms: usize,
        certificate_bits: u64,
        elapsed_millis: u128,
    ) -> Self {
        Self {
            configuration: configuration.name().to_owned(),
            monomials: reading.monomials,
            declaration: declaration.to_owned(),
            samples,
            resamples,
            sampled_rank: reading.sampled_rank,
            filtered_dimension: reading.monomials - reading.kernel.len(),
            redundancy: reading.kernel.len(),
            identities,
            refusals,
            certificate_terms,
            certificate_bits,
            elapsed_millis,
        }
    }
    pub fn configuration(&self) -> &str {
        &self.configuration
    }
    pub fn monomials(&self) -> usize {
        self.monomials
    }
    pub fn declaration(&self) -> &str {
        &self.declaration
    }
    pub fn samples(&self) -> usize {
        self.samples
    }
    pub fn resamples(&self) -> usize {
        self.resamples
    }
    pub fn sampled_rank(&self) -> usize {
        self.sampled_rank
    }
    pub fn filtered_dimension(&self) -> usize {
        self.filtered_dimension
    }
    pub fn redundancy(&self) -> usize {
        self.redundancy
    }
    pub fn identities(&self) -> &[CertifiedIdentity] {
        &self.identities
    }
    pub fn refusals(&self) -> &[RefusedCandidate] {
        &self.refusals
    }
    pub fn certificate_terms(&self) -> usize {
        self.certificate_terms
    }
    pub fn certificate_bits(&self) -> u64 {
        self.certificate_bits
    }
    pub fn elapsed_millis(&self) -> u128 {
        self.elapsed_millis
    }
}

/// Walk one configuration: discover, certify on every chart, and re-sample from counterexamples.
///
/// The loop is the contract's, made mechanical: a refused basis vector returns a nonzero remainder,
/// an admissible counterexample point is sought from it, and **that point becomes a sample**. A
/// spurious direction therefore removes itself. Exceeding [`RESAMPLE_CEILING`] is a contradiction
/// between sampling and certification and is refused as one.
pub fn walk(configuration: &Configuration) -> Result<AtlasReturn, IdentityAtlasError> {
    let started = Instant::now();
    let family = configuration.family();
    let wanted = family.monomials().len() + 16;
    if wanted > SAMPLE_CEILING {
        return Err(IdentityAtlasError::SampleCeiling {
            found: wanted,
            ceiling: SAMPLE_CEILING,
        });
    }
    let candidates = configuration.candidate_points(wanted * 3 + 64);
    let mut points: Vec<(usize, Vec<Rat>)> = Vec::new();
    let charts = configuration.charts().len();
    for (index, point) in candidates.iter().enumerate() {
        let chart = index % charts;
        if configuration.charts()[chart]
            .denominator()
            .evaluate(point)?
            .is_zero()
        {
            continue;
        }
        points.push((chart, point.clone()));
        if points.len() == wanted {
            break;
        }
    }
    if points.len() < wanted {
        return Err(IdentityAtlasError::GridExhausted {
            found: points.len(),
            needed: wanted,
        });
    }

    let mut resamples = 0usize;
    loop {
        let reading = sample_kernel(configuration, &points)?;
        let mut identities = Vec::new();
        let mut refusals = Vec::new();
        let mut new_points: Vec<(usize, Vec<Rat>)> = Vec::new();
        for vector in &reading.kernel {
            match certify(configuration, vector, &candidates)? {
                Ok(identity) => identities.push(identity),
                Err(refused) => {
                    for (chart, verdict) in refused.verdicts().iter().enumerate() {
                        if let ChartVerdict::Refused {
                            counterexample: Some(point),
                            ..
                        } = verdict
                        {
                            new_points.push((chart, point.clone()));
                        }
                    }
                    refusals.push(refused);
                }
            }
        }
        if refusals.is_empty() {
            let certificate_terms = identities
                .iter()
                .map(|identity| identity.certificate_terms())
                .sum();
            let certificate_bits = identities
                .iter()
                .map(|identity| identity.certificate_bits())
                .sum();
            return Ok(AtlasReturn::from_walk(
                configuration,
                &family.declaration(),
                &reading,
                points.len(),
                resamples,
                identities,
                refusals,
                certificate_terms,
                certificate_bits,
                started.elapsed().as_millis(),
            ));
        }
        if new_points.is_empty() {
            return Err(IdentityAtlasError::UnresolvedCertification {
                refused: refusals.len(),
            });
        }
        if resamples == RESAMPLE_CEILING {
            return Err(IdentityAtlasError::ResampleCeiling { taken: resamples });
        }
        points.extend(new_points);
        if points.len() > SAMPLE_CEILING {
            return Err(IdentityAtlasError::SampleCeiling {
                found: points.len(),
                ceiling: SAMPLE_CEILING,
            });
        }
        resamples += 1;
    }
}

// ---------------------------------------------------------------------------------------------
// I6: collapses. A collapse transports identities and CAN CREATE MORE.
// ---------------------------------------------------------------------------------------------

/// **A collapse comparison: the specialized kernel against the transported generic ideal.**
///
/// `u ↦ δx` has zero generic kernel and kernel `⟨u⟩` at `δ = 0`. The specialized kernel is
/// therefore computed **independently** and reduced against the transported ideal; the
/// non-vanishing remainders are the relations the collapse created.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct CollapseComparison {
    /// The collapse's name, including which chart family the specialized configuration declares.
    collapse: String,
    /// The dimension of the independently certified specialized kernel.
    specialized_dimension: usize,
    /// The transported generic identities, specialized into the collapsed receiver family.
    transported: Vec<ExactMultivariate>,
    /// The relations the collapse created: certified specialized identities with nonzero normal
    /// form modulo the transported ideal.
    extra_relations: Vec<ExactMultivariate>,
    /// Whether the specialized kernel is contained in the transported ideal at this degree.
    specialized_lies_in_transported: bool,
}

impl CollapseComparison {
    pub fn collapse(&self) -> &str {
        &self.collapse
    }
    pub fn specialized_dimension(&self) -> usize {
        self.specialized_dimension
    }
    pub fn transported(&self) -> &[ExactMultivariate] {
        &self.transported
    }
    pub fn extra_relations(&self) -> &[ExactMultivariate] {
        &self.extra_relations
    }
    pub fn specialized_lies_in_transported(&self) -> bool {
        self.specialized_lies_in_transported
    }
}

/// Transport the generic identities through a collapse and compare with the specialized kernel.
pub fn compare_collapse(
    collapse: &str,
    generic: &[CertifiedIdentity],
    assignment: &[Option<Rat>],
    retained: &[usize],
    specialized: &AtlasReturn,
) -> Result<CollapseComparison, IdentityAtlasError> {
    let mut transported = Vec::new();
    for identity in generic {
        let moved = identity.polynomial().specialized(assignment, retained)?;
        if !moved.is_zero() {
            transported.push(moved);
        }
    }
    let closure = buchberger(&transported)?;
    let mut extra_relations = Vec::new();
    for identity in specialized.identities() {
        let (remainder, _) = normal_form(identity.polynomial(), closure.basis())?;
        if !remainder.is_zero() {
            extra_relations.push(remainder);
        }
    }
    Ok(CollapseComparison {
        collapse: collapse.to_owned(),
        specialized_dimension: specialized.identities().len(),
        transported,
        specialized_lies_in_transported: extra_relations.is_empty(),
        extra_relations,
    })
}

// ---------------------------------------------------------------------------------------------
// The declared configurations: T0, T1 and T2.
// ---------------------------------------------------------------------------------------------

/// The parameters of the one-angle configuration: the half-angle parameter and the curvature.
const ONE_ANGLE_PARAMETERS: [&str; 2] = ["t", "k"];

/// The receiver names of the one-angle configuration.
pub const ONE_ANGLE_RECEIVERS: [&str; 3] = ["C", "S", "Curv"];

fn one_angle_chart(winding: i64) -> Result<RationalChart, IdentityAtlasError> {
    // D = 1 + k t²; C = ε(1 − k t²)/D; S = ε·2t/D; Curv = k = k·D/D.
    let denominator = ExactMultivariate::from_integer_terms(2, &[(&[0, 0], 1), (&[2, 1], 1)])?;
    let cosine =
        ExactMultivariate::from_integer_terms(2, &[(&[0, 0], winding), (&[2, 1], -winding)])?;
    let sine = ExactMultivariate::from_integer_terms(2, &[(&[1, 0], 2 * winding)])?;
    let curvature = ExactMultivariate::from_integer_terms(2, &[(&[0, 1], 1), (&[2, 2], 1)])?;
    RationalChart::new(
        if winding > 0 {
            "principal winding"
        } else {
            "half-turn winding (-1 = e^{i pi})"
        },
        &ONE_ANGLE_PARAMETERS,
        vec![cosine, sine, curvature],
        denominator,
        "all rational (t, k) with 1 + k t^2 != 0; for k = -1 this excludes t = +-1",
    )
}

/// **T0 — one angle with `k` a variable.**
///
/// The two-sided circle `C² + k S² = 1` over the curvature line, charted by the half-angle
/// parameter in both windings. `head_degree` bounds the degree in `(C, S)` and `tail_degree` the
/// degree in the curvature receiver, so the generator sits at `(2, 1)` and its bounded-degree
/// consequences at `(4, 2)`.
///
/// **Coverage.** For `k ≠ 0` the principal winding already misses only the single point
/// `(C, S) = (−1, 0)`, a codimension-one section of the surface, so its image is dense. At `k = 0`
/// the missed set is the whole line `C = −1`, which is a **component** of the fibre — the half-turn
/// winding is what covers it, and without it `C − 1` would be wrongly certified.
pub fn two_sided_angle(
    head_degree: u32,
    tail_degree: u32,
) -> Result<Configuration, IdentityAtlasError> {
    let family =
        ReceiverFamily::graded_with_tail(&ONE_ANGLE_RECEIVERS, 2, head_degree, tail_degree)?;
    Configuration::new(
        "T0 the two-sided circle over a variable curvature",
        family,
        vec![one_angle_chart(1)?, one_angle_chart(-1)?],
        "[proved-standard] The surface C^2 + k S^2 - 1 = 0 is irreducible over Q (it is linear in \
         k with unit content), and the two half-angle windings cover it minus the codimension-one \
         locus {t -> infinity}. Every component of every fibre k = c is met: the principal winding \
         covers the sheet through (1, 0) and the half-turn winding the sheet through (-1, 0), \
         which at k = 0 are the two distinct components C = +1 and C = -1.",
        7,
        0x5eed_0f7,
    )
}

/// The parameters of the addition configuration.
const ADDITION_PARAMETERS: [&str; 3] = ["t1", "t2", "k"];

/// The receiver names of the generic addition configuration.
pub const ADDITION_RECEIVERS: [&str; 7] = ["C1", "S1", "C2", "S2", "C3", "S3", "Curv"];

/// The receiver names of a collapsed addition configuration, where `k` is a declared constant.
pub const COLLAPSED_ADDITION_RECEIVERS: [&str; 6] = ["C1", "S1", "C2", "S2", "C3", "S3"];

/// `A = 1 + k t1^2` and `B = 1 + k t2^2` over the three addition parameters.
fn addition_denominators() -> Result<(ExactMultivariate, ExactMultivariate), IdentityAtlasError> {
    let a = ExactMultivariate::from_integer_terms(3, &[(&[0, 0, 0], 1), (&[2, 0, 1], 1)])?;
    let b = ExactMultivariate::from_integer_terms(3, &[(&[0, 0, 0], 1), (&[0, 2, 1], 1)])?;
    Ok((a, b))
}

fn addition_chart(
    first_winding: i64,
    second_winding: i64,
) -> Result<RationalChart, IdentityAtlasError> {
    let (a, b) = addition_denominators()?;
    let lower_a = ExactMultivariate::from_integer_terms(3, &[(&[0, 0, 0], 1), (&[2, 0, 1], -1)])?;
    let lower_b = ExactMultivariate::from_integer_terms(3, &[(&[0, 0, 0], 1), (&[0, 2, 1], -1)])?;
    let two_t1 = ExactMultivariate::from_integer_terms(3, &[(&[1, 0, 0], 2)])?;
    let two_t2 = ExactMultivariate::from_integer_terms(3, &[(&[0, 1, 0], 2)])?;
    let curvature = ExactMultivariate::from_integer_terms(3, &[(&[0, 0, 1], 1)])?;
    let denominator = a.times(&b)?;
    let third = first_winding * second_winding;
    let scale = |polynomial: Result<ExactMultivariate, IdentityAtlasError>, winding: i64| {
        polynomial.map(|polynomial| polynomial.scaled(&rational(winding)))
    };

    // C3 = (a b - 4 k t1 t2) / (A B); S3 = 2 (t1 + t2) (1 - k t1 t2) / (A B).
    let four_k_t1_t2 = ExactMultivariate::from_integer_terms(3, &[(&[1, 1, 1], 4)])?;
    let cosine_three = lower_a.times(&lower_b)?.minus(&four_k_t1_t2)?;
    let sum = ExactMultivariate::from_integer_terms(3, &[(&[1, 0, 0], 2), (&[0, 1, 0], 2)])?;
    let one_minus = ExactMultivariate::from_integer_terms(3, &[(&[0, 0, 0], 1), (&[1, 1, 1], -1)])?;
    let sine_three = sum.times(&one_minus)?;

    RationalChart::new(
        &format!("winding ({first_winding}, {second_winding})"),
        &ADDITION_PARAMETERS,
        vec![
            scale(lower_a.times(&b), first_winding)?,
            scale(two_t1.times(&b), first_winding)?,
            scale(lower_b.times(&a), second_winding)?,
            scale(two_t2.times(&a), second_winding)?,
            scale(Ok(cosine_three), third)?,
            scale(Ok(sine_three), third)?,
            curvature.times(&denominator)?,
        ],
        denominator,
        "all rational (t1, t2, k) with (1 + k t1^2)(1 + k t2^2) != 0",
    )
}

/// **T1 — two angles and their sum, uniformly in `k`.**
///
/// The receivers are the two-sided cosine and sine of `θ₁`, `θ₂` and `θ₁ ⊕_k θ₂`, with the
/// curvature as a receiver of its own bounded degree, so the addition laws
/// `C₃ = C₁C₂ − k S₁S₂` and `S₃ = S₁C₂ + C₁S₂` are recovered **uniformly in `k`** rather than one
/// geometry at a time. All four windings `(ε₁, ε₂) ∈ {±1}²` are charted; `ε₃ = ε₁ε₂` is forced by
/// the group law, and naming the windings is what the half-turn `−1 = e^{iπ}` is here.
pub fn two_sided_addition(
    head_degree: u32,
    tail_degree: u32,
) -> Result<Configuration, IdentityAtlasError> {
    let family =
        ReceiverFamily::graded_with_tail(&ADDITION_RECEIVERS, 6, head_degree, tail_degree)?;
    Configuration::new(
        "T1 two two-sided angles and their sum, uniformly in k",
        family,
        vec![
            addition_chart(1, 1)?,
            addition_chart(1, -1)?,
            addition_chart(-1, 1)?,
            addition_chart(-1, -1)?,
        ],
        "[proved-standard] The half-angle chart covers each two-sided circle minus one point, and \
         the four windings cover all four components of the k = 0 fibre, where each of C1 and C2 \
         degenerates to the two lines C = +-1. The sum's winding is not free: eps3 = eps1 eps2 is \
         forced by the group law, so four charts cover the whole configuration.",
        6,
        0x1dea_77,
    )
}

fn collapsed_addition_chart(
    curvature: i64,
    first_winding: i64,
    second_winding: i64,
) -> Result<RationalChart, IdentityAtlasError> {
    // Two parameters (t1, t2); the curvature is a declared constant.
    let k = curvature;
    let a = ExactMultivariate::from_integer_terms(2, &[(&[0, 0], 1), (&[2, 0], k)])?;
    let b = ExactMultivariate::from_integer_terms(2, &[(&[0, 0], 1), (&[0, 2], k)])?;
    let lower_a = ExactMultivariate::from_integer_terms(2, &[(&[0, 0], 1), (&[2, 0], -k)])?;
    let lower_b = ExactMultivariate::from_integer_terms(2, &[(&[0, 0], 1), (&[0, 2], -k)])?;
    let two_t1 = ExactMultivariate::from_integer_terms(2, &[(&[1, 0], 2)])?;
    let two_t2 = ExactMultivariate::from_integer_terms(2, &[(&[0, 1], 2)])?;
    let denominator = a.times(&b)?;
    let third = first_winding * second_winding;
    let four_k_t1_t2 = ExactMultivariate::from_integer_terms(2, &[(&[1, 1], 4 * k)])?;
    let cosine_three = lower_a.times(&lower_b)?.minus(&four_k_t1_t2)?;
    let sum = ExactMultivariate::from_integer_terms(2, &[(&[1, 0], 2), (&[0, 1], 2)])?;
    let one_minus = ExactMultivariate::from_integer_terms(2, &[(&[0, 0], 1), (&[1, 1], -k)])?;
    let sine_three = sum.times(&one_minus)?;
    let scale = |polynomial: Result<ExactMultivariate, IdentityAtlasError>, winding: i64| {
        polynomial.map(|polynomial| polynomial.scaled(&rational(winding)))
    };
    RationalChart::new(
        &format!("k = {curvature}, winding ({first_winding}, {second_winding})"),
        &["t1", "t2"],
        vec![
            scale(lower_a.times(&b), first_winding)?,
            scale(two_t1.times(&b), first_winding)?,
            scale(lower_b.times(&a), second_winding)?,
            scale(two_t2.times(&a), second_winding)?,
            scale(Ok(cosine_three), third)?,
            scale(Ok(sine_three), third)?,
        ],
        denominator,
        "all rational (t1, t2) with (1 + k t1^2)(1 + k t2^2) != 0 at the declared curvature",
    )
}

/// **A collapse of T1 at a declared integer curvature, with a declared winding family.**
///
/// `windings` names which of the four charts the collapsed configuration declares. Declaring only
/// `[(1, 1)]` at `k = 0` is the falsifier: that chart family covers one component of the Galilean
/// fibre and wrongly certifies `C₁ − 1`.
pub fn collapsed_addition(
    curvature: i64,
    windings: &[(i64, i64)],
    head_degree: u32,
) -> Result<Configuration, IdentityAtlasError> {
    let family =
        ReceiverFamily::graded_with_tail(&COLLAPSED_ADDITION_RECEIVERS, 6, head_degree, 0)?;
    let charts = windings
        .iter()
        .map(|(first, second)| collapsed_addition_chart(curvature, *first, *second))
        .collect::<Result<Vec<_>, _>>()?;
    let name = match curvature {
        1 => "circular",
        0 => "Galilean",
        -1 => "hyperbolic",
        _ => "declared",
    };
    Configuration::new(
        &format!(
            "T1 collapse: {name} (k = {curvature}), {} winding chart(s)",
            charts.len()
        ),
        family,
        charts,
        "[definition] The coverage of this collapse is exactly the declared winding family. With \
         all four windings the k = 0 fibre's four components are met; with the principal winding \
         alone only the component C1 = C2 = +1 is met, and the kernel is correspondingly larger.",
        6,
        0x600d_5eed,
    )
}

/// The parameters of the helical-triple configuration: the two-sided Gram and the curvature.
const HELICAL_PARAMETERS: [&str; 13] = [
    "K11", "K12", "K13", "K22", "K23", "K33", "R11", "R12", "R13", "R22", "R23", "R33", "k",
];

/// The receiver names of the helical-triple configuration.
pub const HELICAL_RECEIVERS: [&str; 11] = [
    "Qua1", "Pit1", "SpQ12K", "SpQ12R", "SpQ13K", "SpQ13R", "CrossK", "CrossR", "GramK", "GramR",
    "Curv",
];

/// The receiver names of a helical triple at a **declared constant** curvature: the same family
/// without the curvature receiver, which is what makes the `k = 0` screw instance small.
pub const HELICAL_RECEIVERS_AT: [&str; 10] = [
    "Qua1", "Pit1", "SpQ12K", "SpQ12R", "SpQ13K", "SpQ13R", "CrossK", "CrossR", "GramK", "GramR",
];

/// **T2 — three helical axes, their Killing and reciprocal forms, pitches, spreads and quadrances.**
///
/// For screws `ξ_i = (u_i, v_i)` the **Killing form** is `K_ij = u_i · u_j` and the **reciprocal
/// (Klein) form** is `R_ij = u_i · v_j + v_i · u_j`, and the two-sided Gram is `G = K + ι R` with
/// `ι² = k`. The declared receivers are
///
/// ```text
///   Qua1 = G11              quadrance of axis 1        (K-part K11, R-part R11 = 2 h1 Q1)
///   SpQ1j = G11 Gjj − G1j²  quadrance × spread of the pair (1, j)
///   Cross = G11 G23 − G12 G13   the cross at axis 1, the law of cosines' numerator
///   Gram  = det G
/// ```
///
/// each split into its `1`-part and its `ι`-part. Jacobi's adjugate theorem
/// `SpQ12 · SpQ13 − Cross² = G11 · det G` holds over any commutative ring, so it holds over
/// `A_k = Q[k][ι]/(ι² − k)`, and its two components are the **transferred law of cosines and the
/// transferred law of sines** for the helical triple, uniformly in `k`. At `k = 0` this is Study's
/// spatial law for three lines; the `ι`-component is the one that carries the pitches and moments.
///
/// **Coverage.** The supplied chart is polynomial on the whole affine space of two-sided Gram data,
/// so every certified relation is an identity of `Q[K, R, k]` and holds for **every** helical triple
/// whose forms are those. Equality with the full screw identity kernel additionally needs dominance
/// of the screw-to-Gram map; the rational screw checks below establish soundness points only.
pub fn helical_triple(
    head_degree: u32,
    tail_degree: u32,
) -> Result<Configuration, IdentityAtlasError> {
    helical_configuration(None, head_degree, tail_degree)
}

/// **T2 at a declared constant curvature**: the same three helical axes with `k` fixed.
///
/// `k = 0` is the Euclidean screw instance — dual numbers, Study's spatial law for three lines —
/// and drops the curvature receiver, so the declared family is a quarter the size of the uniform
/// one and the evaluation returns in a fraction of the time. `k = 1` and `k = -1` are the elliptic
/// and hyperbolic instances of the same transfer.
pub fn helical_triple_at(
    curvature: i64,
    head_degree: u32,
) -> Result<Configuration, IdentityAtlasError> {
    helical_configuration(Some(curvature), head_degree, 0)
}

fn helical_configuration(
    constant_curvature: Option<i64>,
    head_degree: u32,
    tail_degree: u32,
) -> Result<Configuration, IdentityAtlasError> {
    let width = if constant_curvature.is_some() { 12 } else { 13 };
    let variable = |index: usize| ExactMultivariate::variable(width, index);
    let k11 = variable(0)?;
    let k12 = variable(1)?;
    let k13 = variable(2)?;
    let k22 = variable(3)?;
    let k23 = variable(4)?;
    let k33 = variable(5)?;
    let r11 = variable(6)?;
    let r12 = variable(7)?;
    let r13 = variable(8)?;
    let r22 = variable(9)?;
    let r23 = variable(10)?;
    let r33 = variable(11)?;
    let curvature = match constant_curvature {
        Some(value) => ExactMultivariate::constant(width, rational(value)),
        None => variable(12)?,
    };
    let two = ExactMultivariate::constant(width, rational(2));

    // SpQ1j = K11 Kjj + k R11 Rjj − K1j² − k R1j²  (1-part), K11 Rjj + R11 Kjj − 2 K1j R1j (ι-part).
    let spq = |kjj: &ExactMultivariate,
               rjj: &ExactMultivariate,
               k1j: &ExactMultivariate,
               r1j: &ExactMultivariate|
     -> Result<_, IdentityAtlasError> {
        let real = k11
            .times(kjj)?
            .plus(&curvature.times(&r11.times(rjj)?)?)?
            .minus(&k1j.times(k1j)?)?
            .minus(&curvature.times(&r1j.times(r1j)?)?)?;
        let imaginary = k11
            .times(rjj)?
            .plus(&r11.times(kjj)?)?
            .minus(&two.times(&k1j.times(r1j)?)?)?;
        Ok((real, imaginary))
    };
    let (spq12k, spq12r) = spq(&k22, &r22, &k12, &r12)?;
    let (spq13k, spq13r) = spq(&k33, &r33, &k13, &r13)?;

    // Cross = G11 G23 − G12 G13.
    let cross_real = k11
        .times(&k23)?
        .plus(&curvature.times(&r11.times(&r23)?)?)?
        .minus(&k12.times(&k13)?)?
        .minus(&curvature.times(&r12.times(&r13)?)?)?;
    let cross_imaginary = k11
        .times(&r23)?
        .plus(&r11.times(&k23)?)?
        .minus(&k12.times(&r13)?)?
        .minus(&r12.times(&k13)?)?;

    // det(K + x R) = det K + x tr(adj(K) R) + x² tr(adj(R) K) + x³ det R, then x = ι, ι² = k.
    let determinant = |a11: &ExactMultivariate,
                       a12: &ExactMultivariate,
                       a13: &ExactMultivariate,
                       a22: &ExactMultivariate,
                       a23: &ExactMultivariate,
                       a33: &ExactMultivariate|
     -> Result<ExactMultivariate, IdentityAtlasError> {
        let first = a22.times(a33)?.minus(&a23.times(a23)?)?;
        let second = a12.times(a33)?.minus(&a23.times(a13)?)?;
        let third = a12.times(a23)?.minus(&a22.times(a13)?)?;
        Ok(a11
            .times(&first)?
            .minus(&a12.times(&second)?)?
            .plus(&a13.times(&third)?)?)
    };
    let adjugate_pairing = |a11: &ExactMultivariate,
                            a12: &ExactMultivariate,
                            a13: &ExactMultivariate,
                            a22: &ExactMultivariate,
                            a23: &ExactMultivariate,
                            a33: &ExactMultivariate,
                            b11: &ExactMultivariate,
                            b12: &ExactMultivariate,
                            b13: &ExactMultivariate,
                            b22: &ExactMultivariate,
                            b23: &ExactMultivariate,
                            b33: &ExactMultivariate|
     -> Result<ExactMultivariate, IdentityAtlasError> {
        // tr(adj(A) B) for symmetric A, B.
        let adj11 = a22.times(a33)?.minus(&a23.times(a23)?)?;
        let adj22 = a11.times(a33)?.minus(&a13.times(a13)?)?;
        let adj33 = a11.times(a22)?.minus(&a12.times(a12)?)?;
        let adj12 = a13.times(a23)?.minus(&a12.times(a33)?)?;
        let adj13 = a12.times(a23)?.minus(&a13.times(a22)?)?;
        let adj23 = a12.times(a13)?.minus(&a11.times(a23)?)?;
        Ok(adj11
            .times(b11)?
            .plus(&adj22.times(b22)?)?
            .plus(&adj33.times(b33)?)?
            .plus(&two.times(&adj12.times(b12)?)?)?
            .plus(&two.times(&adj13.times(b13)?)?)?
            .plus(&two.times(&adj23.times(b23)?)?)?)
    };
    let det_k = determinant(&k11, &k12, &k13, &k22, &k23, &k33)?;
    let det_r = determinant(&r11, &r12, &r13, &r22, &r23, &r33)?;
    let adj_k_r = adjugate_pairing(
        &k11, &k12, &k13, &k22, &k23, &k33, &r11, &r12, &r13, &r22, &r23, &r33,
    )?;
    let adj_r_k = adjugate_pairing(
        &r11, &r12, &r13, &r22, &r23, &r33, &k11, &k12, &k13, &k22, &k23, &k33,
    )?;
    let gram_real = det_k.plus(&curvature.times(&adj_r_k)?)?;
    let gram_imaginary = adj_k_r.plus(&curvature.times(&det_r)?)?;

    let parameters: &[&str] = if constant_curvature.is_some() {
        &HELICAL_PARAMETERS[..12]
    } else {
        &HELICAL_PARAMETERS
    };
    let mut values = vec![
        k11.clone(),
        r11.clone(),
        spq12k,
        spq12r,
        spq13k,
        spq13r,
        cross_real,
        cross_imaginary,
        gram_real,
        gram_imaginary,
    ];
    let receivers: &[&str] = if constant_curvature.is_some() {
        &HELICAL_RECEIVERS_AT
    } else {
        values.push(curvature.clone());
        &HELICAL_RECEIVERS
    };
    let chart = RationalChart::polynomial("the two-sided Gram of the triple", parameters, values)?;
    let family = ReceiverFamily::graded_with_tail(receivers, 10, head_degree, tail_degree)?;
    Configuration::new(
        &match constant_curvature {
            Some(value) => format!("T2 three helical axes at curvature k = {value}"),
            None => "T2 three helical axes over a two-sided angle".to_owned(),
        },
        family,
        vec![chart],
        "[proved-standard for soundness] The supplied chart is polynomial on the whole affine space of \
         two-sided Gram data, so every certified relation is an identity of Q[K, R, k] and holds \
         for every helical triple. [agent-inferred for completeness] The reverse inclusion needs \
         the screw-to-Gram map (u_i, v_i) |-> (u_i . u_j, u_i . v_j + v_i . u_j) to be dominant \
         onto Sym_3 (+) Sym_3. The differential at U = I, V = 0 is \
         (dU^T + dU, dV + dV^T), of rank 12 in characteristic zero; this is the dominance \
         certificate. The generic fibre also carries the three-dimensional skew part of U^T V, \
         in addition to the orthogonal U freedom. Rational screw tests provide soundness points, \
         not the dominance proof.",
        4,
        0x5c_2e_77,
    )
}

/// **The Killing and reciprocal forms of a rational screw triple, for the realization check.**
///
/// `screws` are `(u_i, v_i)` as exact rational triples. The return is the thirteen chart
/// parameters in [`HELICAL_PARAMETERS`]' order at the declared curvature: a real configuration
/// point, so a certified identity can be checked against actual helical axes rather than against
/// the Gram chart alone.
pub fn screw_gram_point(screws: &[([Rat; 3], [Rat; 3]); 3], curvature: Rat) -> Vec<Rat> {
    let generator = |(angular, advance): &([Rat; 3], [Rat; 3])| {
        ScrewGenerator::new(
            RatVec3::new(angular[0].clone(), angular[1].clone(), angular[2].clone()),
            RatVec3::new(advance[0].clone(), advance[1].clone(), advance[2].clone()),
        )
    };
    let generators = screws.iter().map(generator).collect::<Vec<_>>();
    let killing = |i: usize, j: usize| generators[i].angular_pairing(&generators[j]);
    let reciprocal = |i: usize, j: usize| generators[i].reciprocal_pairing(&generators[j]);
    vec![
        killing(0, 0),
        killing(0, 1),
        killing(0, 2),
        killing(1, 1),
        killing(1, 2),
        killing(2, 2),
        reciprocal(0, 0),
        reciprocal(0, 1),
        reciprocal(0, 2),
        reciprocal(1, 1),
        reciprocal(1, 2),
        reciprocal(2, 2),
        curvature,
    ]
}
