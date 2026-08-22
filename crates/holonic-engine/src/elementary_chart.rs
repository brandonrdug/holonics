//! Whether `∫ R(x) e^{g(x)} dx` closes in the elementary chart, decided exactly.
//!
//! # The mechanism, and why it is a transport question rather than a difficulty
//!
//! Liouville's theorem says that `∫ R e^g` is elementary **exactly when** there
//! is a rational `a` with
//!
//! ```text
//! a' + a·g' = R
//! ```
//!
//! because then `(a e^g)' = (a' + a g') e^g = R e^g` and the antiderivative is
//! `a e^g`. So the question *is not* a search through integration techniques.
//! It is one linear condition on `a`, and `a` ranges over a space this module
//! bounds a priori. That bound is the whole content: it makes the candidate
//! population **finite and exhaustible**, so the answer is a decision rather
//! than a failure to find something.
//!
//! Two structures decide it, and they refuse for different reasons.
//!
//! ## The pole structure decides first, and it decides before any arithmetic
//!
//! If `a` has a pole of order `m ≥ 1` at a point, then `a'` has a pole of order
//! `m + 1` there while `a g'` has order `m` — `g` is a polynomial, so `g'`
//! contributes no pole. The orders cannot cancel, so `a' + a g'` has a pole of
//! order exactly `m + 1 ≥ 2`.
//!
//! **A pole of `R` of order `k` therefore requires a pole of `a` of order
//! `k − 1`, and a SIMPLE pole of `R` requires a pole of `a` of order zero —
//! which is no pole, which produces no pole in `a' + a g'`.** A simple pole in
//! `R` is thus an absolute obstruction, carrying no linear system at all.
//!
//! That is why `∫ e^x / x` is not elementary: `1/x` has a simple pole. The
//! integral is `Ei(x)`, and the obstruction is visible in the denominator
//! before a single coefficient is computed.
//!
//! ## Then the degree bound, and it is exact
//!
//! With no poles left, `a` is a polynomial and
//! `deg(a' + a g') = deg a + deg g − 1`, because `a g'` outranks `a'` whenever
//! `deg g ≥ 1`. So
//!
//! ```text
//! deg a = deg R − deg g + 1
//! ```
//!
//! One degree. Not a bound to search under — a single value, which is why the
//! candidate space is one finite-dimensional vector space and the decision is
//! one linear system over `ℚ`.
//!
//! ## What each species of refusal is, holonically
//!
//! - A **pole obstruction** is the declared chart refusing the object outright:
//!   no `a` of any degree exists.
//! - An **inconsistent system** is a *compression with a certified remainder*.
//!   The obstruction returned is a genuine left null combination — a weighting
//!   of the monomial equations that annihilates every unknown while leaving the
//!   response standing. That combination is the exhibited remainder, and it
//!   names which monomial could not be paid for.
//!
//! `∫ e^{−x²}` is the second species, and this module returns the row: the
//! constant term demands `0 = 1`. Non-elementarity is a **rank deficiency with
//! an exhibited witness**, not a difficulty.
//!
//! # The declared aperture, and what falls outside it
//!
//! `R = P/Q` with `Q` **squarefree**, and `g` a non-constant polynomial. Under a
//! squarefree `Q` every pole of `R` is simple, so the pole analysis above is
//! complete: either `Q` divides `P` and `R` is a polynomial, or the integral is
//! obstructed.
//!
//! A repeated factor in `Q` admits poles in `a` and needs the full Risch
//! machinery. **This module refuses that case by name rather than returning a
//! reading it cannot support.** An organ used past its declared aperture is a
//! defect even when it appears to return.

use std::collections::BTreeMap;

use num_traits::{One, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    InverseTransportError,
    inverse_transport::{AffineObstruction, ExactAffineVersionFiber},
    rational_polynomial::RationalPolynomial,
};

/// `R(x) e^{g(x)}`, with `R = numerator / denominator`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExponentialIntegrand {
    pub numerator: RationalPolynomial,
    pub denominator: RationalPolynomial,
    pub exponent: RationalPolynomial,
}

impl ExponentialIntegrand {
    /// `R` a polynomial: the denominator is `1`.
    pub fn polynomial_coefficient(
        numerator: RationalPolynomial,
        exponent: RationalPolynomial,
    ) -> Self {
        Self {
            numerator,
            denominator: RationalPolynomial::new(vec![Rat::one()]),
            exponent,
        }
    }

    pub fn rational_coefficient(
        numerator: RationalPolynomial,
        denominator: RationalPolynomial,
        exponent: RationalPolynomial,
    ) -> Self {
        Self {
            numerator,
            denominator,
            exponent,
        }
    }

    /// How the integrand presents itself, before anything is solved.
    ///
    /// Everything here is read off the object. Nothing is searched for, and no
    /// candidate is constructed — which is what makes the prediction below a
    /// recognition rather than a summary of a computation already done.
    pub fn signature(&self) -> Result<IntegrandSignature, ElementaryChartError> {
        let exponent_degree = self
            .exponent
            .degree()
            .ok_or(ElementaryChartError::ConstantExponent)?;
        if exponent_degree == 0 {
            return Err(ElementaryChartError::ConstantExponent);
        }
        let denominator_degree = self
            .denominator
            .degree()
            .ok_or(ElementaryChartError::ZeroDenominator)?;

        let denominator_is_squarefree = if denominator_degree == 0 {
            true
        } else {
            let common = self
                .denominator
                .monic_gcd(&self.denominator.derivative())
                .map_err(|_| ElementaryChartError::ZeroDenominator)?;
            common.degree() == Some(0)
        };

        let (quotient, remainder) = self
            .numerator
            .divided_by(&self.denominator)
            .map_err(|_| ElementaryChartError::ZeroDenominator)?;
        let denominator_divides_numerator = remainder.degree().is_none();

        let coefficient_degree = if denominator_divides_numerator {
            quotient.degree()
        } else {
            None
        };

        let predicted_realizer_degree = coefficient_degree
            .map(|degree| degree as isize - exponent_degree as isize + 1)
            .filter(|_| denominator_divides_numerator);

        Ok(IntegrandSignature {
            coefficient_degree,
            denominator_degree,
            exponent_degree,
            denominator_is_squarefree,
            denominator_divides_numerator,
            predicted_realizer_degree,
        })
    }
}

/// What is legible on the face of the integrand.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IntegrandSignature {
    /// `deg R` once the denominator has divided out, when it does.
    pub coefficient_degree: Option<usize>,
    pub denominator_degree: usize,
    pub exponent_degree: usize,
    pub denominator_is_squarefree: bool,
    pub denominator_divides_numerator: bool,
    /// `deg R − deg g + 1`, the exact degree any polynomial realizer must have.
    /// Negative means no polynomial realizer of any degree can carry `R`.
    pub predicted_realizer_degree: Option<isize>,
}

/// The reading the signature alone commits to, before the system is built.
///
/// This exists so recognition can be graded separately from computation. A
/// recognition that merely reported what the solver returned would be a
/// tautology; this one is written down first and can be wrong.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum Recognition {
    /// The denominator carries a repeated factor: outside the declared aperture.
    OutsideAperture,
    /// A simple pole survives, so no realizer exists at any degree.
    PoleObstructed,
    /// `deg R < deg g − 1`, so only the zero realizer is available and it can
    /// only carry the zero integrand.
    RealizerDegreeNegative,
    /// A realizer of exactly this degree is the only candidate. Whether it
    /// exists is decided by the linear system and not by this reading.
    CandidateAtDegree(usize),
}

impl IntegrandSignature {
    pub fn recognise(&self) -> Recognition {
        if !self.denominator_is_squarefree {
            return Recognition::OutsideAperture;
        }
        if !self.denominator_divides_numerator {
            return Recognition::PoleObstructed;
        }
        match self.predicted_realizer_degree {
            None => Recognition::RealizerDegreeNegative,
            Some(degree) if degree < 0 => Recognition::RealizerDegreeNegative,
            Some(degree) => Recognition::CandidateAtDegree(degree as usize),
        }
    }
}

/// The exhibited reason one monomial could not be paid for.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct MonomialObstruction {
    /// The left null combination over the monomial equations, admission-ordinal
    /// keyed. Under this module's admission order the ordinal IS the monomial
    /// degree, so the map reads directly as a statement about powers of `x`.
    pub combination: BTreeMap<usize, Rat>,
    /// What that combination of the right-hand sides returns. Never zero.
    pub response: Rat,
    /// The lowest monomial the combination consults.
    pub lowest_monomial: usize,
}

/// What the chart returned.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ElementaryReading {
    /// `∫ R e^g = realizer · e^g`, exactly.
    Admits {
        realizer: RationalPolynomial,
        /// `realizer' + realizer·g'`, recomputed and compared against `R`. This
        /// is the second frame: the system's answer is differentiated back
        /// rather than trusted.
        returned_coefficient: RationalPolynomial,
    },
    /// A simple pole survives; no realizer exists at any degree.
    PoleObstructed {
        /// The part of the numerator the denominator could not carry.
        remainder: RationalPolynomial,
    },
    /// The linear system is inconsistent, with the annihilating combination
    /// exhibited.
    SystemInconsistent { obstruction: MonomialObstruction },
}

impl ElementaryReading {
    pub fn is_elementary(&self) -> bool {
        matches!(self, Self::Admits { .. })
    }
}

/// How far the signature alone got, measured against what the system returned.
///
/// This is the instrument. A recognition that merely restated the solver's
/// answer would be a check whose material cannot vary the property under test;
/// this one commits before the system runs and can therefore be graded.
///
/// **The two structural refusals are decisive and the admission is not**, and
/// that asymmetry is the finding rather than a limitation. A simple pole and a
/// negative realizer degree are read off the object and no linear system can
/// overturn them. A satisfied degree bound is **necessary and not sufficient**:
/// it says where the only candidate lives, never that the candidate exists.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum RecognitionOutcome {
    /// The signature settled it alone; the system could not have disagreed.
    Decisive,
    /// The signature located the only candidate and left its existence open;
    /// the system then found it, at the degree the signature named.
    OpenedAndFound { predicted_degree: usize },
    /// The signature located the only candidate and the system found no such
    /// realizer. The prediction was necessary and turned out insufficient —
    /// **this is the outcome that makes the recognition falsifiable.**
    OpenedAndRefused { predicted_degree: usize },
    /// The signature committed to a reading the system contradicted. Reaching
    /// this means the recognition law itself is wrong.
    Contradicted,
}

impl RecognitionOutcome {
    /// Whether the signature alone was enough, without the linear system.
    pub fn settled_without_the_system(&self) -> bool {
        matches!(self, Self::Decisive)
    }
}

fn grade_recognition(recognised: Recognition, reading: &ElementaryReading) -> RecognitionOutcome {
    match (recognised, reading) {
        // Structural refusals: read off the object, and no system overturns them.
        (Recognition::PoleObstructed, ElementaryReading::PoleObstructed { .. }) => {
            RecognitionOutcome::Decisive
        }
        (Recognition::RealizerDegreeNegative, ElementaryReading::SystemInconsistent { .. }) => {
            RecognitionOutcome::Decisive
        }
        // The degree bound is necessary, never sufficient. Both continuations
        // are lawful and the instrument records which one happened.
        (Recognition::CandidateAtDegree(degree), ElementaryReading::Admits { realizer, .. }) => {
            if realizer.degree().unwrap_or(0) <= degree {
                RecognitionOutcome::OpenedAndFound {
                    predicted_degree: degree,
                }
            } else {
                RecognitionOutcome::Contradicted
            }
        }
        (Recognition::CandidateAtDegree(degree), ElementaryReading::SystemInconsistent { .. }) => {
            RecognitionOutcome::OpenedAndRefused {
                predicted_degree: degree,
            }
        }
        _ => RecognitionOutcome::Contradicted,
    }
}

/// The whole decision, with its work and its two frames.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ElementaryChartReading {
    pub schema: String,
    pub signature: IntegrandSignature,
    pub recognised: Recognition,
    /// How the signature's commitment fared against what the system returned.
    pub recognition_outcome: RecognitionOutcome,
    pub reading: ElementaryReading,
    /// Rows admitted into the exact affine fiber; one per monomial equation.
    pub monomial_equations: usize,
    /// Rank of the admitted system.
    pub rank: usize,
    /// Unknowns declared: the coefficients of the candidate realizer.
    pub unknowns: usize,
    /// Whether the second frame agreed — the produced realizer differentiated
    /// back to the declared coefficient exactly.
    pub returns_under_differentiation: bool,
}

/// Decide whether the integrand closes in the elementary chart.
pub fn read_elementary_chart(
    integrand: &ExponentialIntegrand,
) -> Result<ElementaryChartReading, ElementaryChartError> {
    let signature = integrand.signature()?;
    let recognised = signature.recognise();

    if !signature.denominator_is_squarefree {
        return Err(ElementaryChartError::DenominatorNotSquarefree {
            degree: signature.denominator_degree,
        });
    }

    // The pole obstruction is structural and carries no linear system.
    let (coefficient, remainder) = integrand
        .numerator
        .divided_by(&integrand.denominator)
        .map_err(|_| ElementaryChartError::ZeroDenominator)?;
    if remainder.degree().is_some() {
        return Ok(ElementaryChartReading {
            schema: SCHEMA.to_owned(),
            signature,
            recognised,
            recognition_outcome: grade_recognition(
                recognised,
                &ElementaryReading::PoleObstructed {
                    remainder: remainder.clone(),
                },
            ),
            reading: ElementaryReading::PoleObstructed { remainder },
            monomial_equations: 0,
            rank: 0,
            unknowns: 0,
            returns_under_differentiation: false,
        });
    }

    // The candidate space. The tight degree is `deg R − deg g + 1`; the system
    // is built one degree wider than the tight prediction when that prediction
    // is negative, so an impossible case still returns an EXHIBITED
    // inconsistency rather than an empty search. Widening cannot admit a
    // spurious realizer — the extra coefficient is decided by the same system.
    let realizer_extent = match signature.predicted_realizer_degree {
        Some(degree) if degree >= 0 => degree as usize + 1,
        _ => 1,
    };

    let exponent_derivative = integrand.exponent.derivative();
    let coefficient_degree = coefficient.degree();

    // Equations run over every monomial either side can reach.
    let highest_monomial = realizer_extent + signature.exponent_degree;
    let equation_extent = highest_monomial.max(coefficient_degree.unwrap_or(0) + 1);

    let mut fiber = ExactAffineVersionFiber::new(realizer_extent)?;
    let mut obstruction: Option<AffineObstruction> = None;

    // Admission ordinal == monomial degree, which is what lets the returned
    // combination be read as a statement about powers of x.
    for monomial in 0..equation_extent {
        let mut row = vec![Rat::zero(); realizer_extent];
        for (power, cell) in row.iter_mut().enumerate() {
            // d/dx of c_power x^power contributes at monomial == power - 1.
            if power > 0 && power - 1 == monomial {
                *cell += Rat::from_integer(power.into());
            }
            // c_power x^power * g' contributes g'_{monomial - power}.
            if monomial >= power {
                *cell += exponent_derivative.coefficient(monomial - power);
            }
        }
        let response = coefficient.coefficient(monomial);
        match fiber.admit(row, response) {
            Ok(_) => {}
            Err(InverseTransportError::AffineFiberObstructed) => {
                obstruction = fiber.obstruction().cloned();
                break;
            }
            Err(error) => return Err(error.into()),
        }
    }

    if let Some(witness) = obstruction {
        let lowest_monomial = witness.combination.keys().copied().next().unwrap_or(0);
        let reading = ElementaryReading::SystemInconsistent {
            obstruction: MonomialObstruction {
                combination: witness.combination,
                response: witness.response,
                lowest_monomial,
            },
        };
        return Ok(ElementaryChartReading {
            schema: SCHEMA.to_owned(),
            signature,
            recognised,
            recognition_outcome: grade_recognition(recognised, &reading),
            reading,
            monomial_equations: fiber.admitted_equations(),
            rank: fiber.rank(),
            unknowns: realizer_extent,
            returns_under_differentiation: false,
        });
    }

    let Some(solution) = fiber.unique_solution()? else {
        return Err(ElementaryChartError::RealizerUnderdetermined {
            unknowns: realizer_extent,
            rank: fiber.rank(),
        });
    };

    let realizer = RationalPolynomial::new(solution);
    // The second frame. Differentiate the produced antiderivative back and
    // compare against the declared coefficient. Nothing here consults the
    // system that produced it.
    let returned_coefficient = realizer
        .derivative()
        .plus(&realizer.times(&exponent_derivative));
    let returns_under_differentiation = returned_coefficient == coefficient;

    let reading = ElementaryReading::Admits {
        realizer,
        returned_coefficient,
    };
    Ok(ElementaryChartReading {
        schema: SCHEMA.to_owned(),
        signature,
        recognised,
        recognition_outcome: grade_recognition(recognised, &reading),
        reading,
        monomial_equations: fiber.admitted_equations(),
        rank: fiber.rank(),
        unknowns: realizer_extent,
        returns_under_differentiation,
    })
}

const SCHEMA: &str = "holonic-engine.elementary-chart.v1";

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ElementaryChartError {
    #[error("an exponential integrand needs a non-constant exponent")]
    ConstantExponent,
    #[error("an integrand cannot have a zero denominator")]
    ZeroDenominator,
    #[error(
        "a denominator of degree {degree} carries a repeated factor, which admits poles in the \
         realizer and lies outside this chart's declared aperture"
    )]
    DenominatorNotSquarefree { degree: usize },
    #[error(
        "the realizer system left {unknowns} unknowns at rank {rank}, so the chart would be \
         choosing among realizers rather than returning one"
    )]
    RealizerUnderdetermined { unknowns: usize, rank: usize },
    #[error("the exact affine fiber refused: {0}")]
    Fiber(#[from] InverseTransportError),
}

#[cfg(test)]
mod tests {
    use super::*;
    use relational_geometry::exact::rat;

    fn polynomial(coefficients: &[i64]) -> RationalPolynomial {
        RationalPolynomial::new(coefficients.iter().map(|value| rat(*value, 1)).collect())
    }

    #[test]
    fn the_classical_admission_returns_the_realizer_and_differentiates_back() {
        // ∫ 2x e^{x²} dx = e^{x²}, so the realizer is the constant 1.
        let integrand = ExponentialIntegrand::polynomial_coefficient(
            polynomial(&[0, 2]),
            polynomial(&[0, 0, 1]),
        );
        let reading =
            read_elementary_chart(&integrand).expect("the fixture is inside the aperture");
        assert_eq!(reading.recognised, Recognition::CandidateAtDegree(0));
        assert!(reading.reading.is_elementary());
        assert!(reading.returns_under_differentiation);
        let ElementaryReading::Admits { realizer, .. } = &reading.reading else {
            panic!("the reading admitted");
        };
        assert_eq!(realizer, &polynomial(&[1]));
    }

    #[test]
    fn a_rational_realizer_is_returned_exactly_and_is_not_an_integer() {
        // ∫ x e^{x²} dx = e^{x²}/2. The realizer is 1/2, which no float-free
        // integer carrier could return.
        let integrand = ExponentialIntegrand::polynomial_coefficient(
            polynomial(&[0, 1]),
            polynomial(&[0, 0, 1]),
        );
        let reading =
            read_elementary_chart(&integrand).expect("the fixture is inside the aperture");
        let ElementaryReading::Admits { realizer, .. } = &reading.reading else {
            panic!("the reading admitted");
        };
        assert_eq!(realizer.coefficient(0), rat(1, 2));
        assert!(reading.returns_under_differentiation);
    }

    #[test]
    fn the_gaussian_refuses_by_an_exhibited_row_not_by_an_empty_search() {
        // ∫ e^{−x²} dx. The constant monomial demands 0 = 1.
        let integrand =
            ExponentialIntegrand::polynomial_coefficient(polynomial(&[1]), polynomial(&[0, 0, -1]));
        let reading =
            read_elementary_chart(&integrand).expect("the fixture is inside the aperture");
        assert_eq!(reading.recognised, Recognition::RealizerDegreeNegative);
        assert!(!reading.reading.is_elementary());
        let ElementaryReading::SystemInconsistent { obstruction } = &reading.reading else {
            panic!("the system was inconsistent");
        };
        assert_eq!(obstruction.lowest_monomial, 0);
        assert!(!obstruction.response.is_zero());
    }

    #[test]
    fn the_sum_of_an_elementary_and_a_refused_integrand_refuses_and_names_the_refused_part() {
        // ∫ (1 + x) e^{x²} dx. The x term is elementary on its own; the constant
        // is not, and the witness must consult the constant monomial.
        let integrand = ExponentialIntegrand::polynomial_coefficient(
            polynomial(&[1, 1]),
            polynomial(&[0, 0, 1]),
        );
        let reading =
            read_elementary_chart(&integrand).expect("the fixture is inside the aperture");
        assert!(!reading.reading.is_elementary());
        let ElementaryReading::SystemInconsistent { obstruction } = &reading.reading else {
            panic!("the system was inconsistent");
        };
        assert_eq!(obstruction.lowest_monomial, 0);
    }

    #[test]
    fn a_simple_pole_obstructs_structurally_and_builds_no_system_at_all() {
        // ∫ e^x / x dx is Ei(x). The refusal is read off the denominator.
        let integrand = ExponentialIntegrand::rational_coefficient(
            polynomial(&[1]),
            polynomial(&[0, 1]),
            polynomial(&[0, 1]),
        );
        let reading =
            read_elementary_chart(&integrand).expect("the fixture is inside the aperture");
        assert_eq!(reading.recognised, Recognition::PoleObstructed);
        assert!(matches!(
            reading.reading,
            ElementaryReading::PoleObstructed { .. }
        ));
        assert_eq!(reading.monomial_equations, 0);
        assert_eq!(reading.unknowns, 0);
    }

    #[test]
    fn the_two_refusals_are_different_species_and_not_one_species_twice() {
        let gaussian =
            ExponentialIntegrand::polynomial_coefficient(polynomial(&[1]), polynomial(&[0, 0, -1]));
        let pole = ExponentialIntegrand::rational_coefficient(
            polynomial(&[1]),
            polynomial(&[0, 1]),
            polynomial(&[0, 1]),
        );
        let first = read_elementary_chart(&gaussian).expect("inside the aperture");
        let second = read_elementary_chart(&pole).expect("inside the aperture");
        assert!(!first.reading.is_elementary());
        assert!(!second.reading.is_elementary());
        assert_ne!(
            std::mem::discriminant(&first.reading),
            std::mem::discriminant(&second.reading),
            "two integrands refuse for two reasons; collapsing them would delete the mechanism"
        );
    }

    #[test]
    fn a_repeated_denominator_factor_is_refused_by_name_rather_than_answered() {
        // 1/x², whose realizer may itself carry a pole. Outside the aperture.
        let integrand = ExponentialIntegrand::rational_coefficient(
            polynomial(&[1]),
            polynomial(&[0, 0, 1]),
            polynomial(&[0, 1]),
        );
        let signature = integrand.signature().expect("the signature is legible");
        assert!(!signature.denominator_is_squarefree);
        assert_eq!(signature.recognise(), Recognition::OutsideAperture);
        assert!(matches!(
            read_elementary_chart(&integrand),
            Err(ElementaryChartError::DenominatorNotSquarefree { .. })
        ));
    }

    #[test]
    fn the_recognition_law_is_never_contradicted_on_the_declared_material() {
        for integrand in declared_material() {
            let reading = read_elementary_chart(&integrand).expect("inside the aperture");
            assert_ne!(
                reading.recognition_outcome,
                RecognitionOutcome::Contradicted,
                "the signature committed to a reading the system overturned: {:?}",
                reading.signature
            );
        }
    }

    /// The instrument is only an instrument if every outcome it can report is
    /// reachable on real material. A recognition that is decisive everywhere
    /// would be a solver in disguise; one that is open everywhere would decide
    /// nothing. Both occur, and the split is the finding.
    #[test]
    fn recognition_is_decisive_on_refusal_and_open_on_admission_and_both_occur() {
        let mut decisive = 0;
        let mut opened_and_found = 0;
        let mut opened_and_refused = 0;
        for integrand in declared_material() {
            let reading = read_elementary_chart(&integrand).expect("inside the aperture");
            match reading.recognition_outcome {
                RecognitionOutcome::Decisive => decisive += 1,
                RecognitionOutcome::OpenedAndFound { .. } => opened_and_found += 1,
                RecognitionOutcome::OpenedAndRefused { .. } => opened_and_refused += 1,
                RecognitionOutcome::Contradicted => panic!("the recognition law is wrong"),
            }
        }
        assert!(
            decisive > 0,
            "no refusal was settled by the signature alone"
        );
        assert!(opened_and_found > 0, "no admission was located and found");
        assert!(
            opened_and_refused > 0,
            "the degree bound was never merely necessary, so this material cannot tell a \
             necessary condition from a sufficient one"
        );
    }

    /// `∫(1+x)e^{x²}` is the separating case: its degree bound is satisfied, so
    /// the signature cannot refuse it, and the system refuses it anyway.
    #[test]
    fn a_satisfied_degree_bound_does_not_imply_a_realizer_exists() {
        let integrand = ExponentialIntegrand::polynomial_coefficient(
            polynomial(&[1, 1]),
            polynomial(&[0, 0, 1]),
        );
        let reading = read_elementary_chart(&integrand).expect("inside the aperture");
        assert_eq!(reading.recognised, Recognition::CandidateAtDegree(0));
        assert_eq!(
            reading.recognition_outcome,
            RecognitionOutcome::OpenedAndRefused {
                predicted_degree: 0
            }
        );
        assert!(!reading.recognition_outcome.settled_without_the_system());
    }

    /// The witness must be a genuine COMBINATION, not always one row.
    ///
    /// `∫(1 + x + x²)e^{x²}` fixes `c₁ = 1` from the constant monomial and
    /// `2c₁ = 1` from the quadratic one. Neither equation is inconsistent by
    /// itself; the contradiction lives only in `equation₂ − 2·equation₀`, so a
    /// witness that could not span two rows would have nothing to report here.
    #[test]
    fn the_witness_spans_several_equations_when_no_single_equation_is_inconsistent() {
        let integrand = ExponentialIntegrand::polynomial_coefficient(
            polynomial(&[1, 1, 1]),
            polynomial(&[0, 0, 1]),
        );
        let reading = read_elementary_chart(&integrand).expect("inside the aperture");
        let ElementaryReading::SystemInconsistent { obstruction } = &reading.reading else {
            panic!("the system was inconsistent");
        };
        assert!(
            obstruction.combination.len() >= 2,
            "the witness collapsed to one row and cannot be exhibiting a combination: {:?}",
            obstruction.combination
        );
        assert_eq!(obstruction.combination.get(&0), Some(&rat(-2, 1)));
        assert_eq!(obstruction.combination.get(&2), Some(&rat(1, 1)));
        assert_eq!(obstruction.response, rat(-1, 1));
    }

    fn declared_material() -> Vec<ExponentialIntegrand> {
        vec![
            // Admits, realizer 1.
            ExponentialIntegrand::polynomial_coefficient(
                polynomial(&[0, 2]),
                polynomial(&[0, 0, 1]),
            ),
            // Admits, realizer 1/2.
            ExponentialIntegrand::polynomial_coefficient(
                polynomial(&[0, 1]),
                polynomial(&[0, 0, 1]),
            ),
            // Admits at degree 1: ∫(2x² + 1)e^{x²}... realizer x.
            ExponentialIntegrand::polynomial_coefficient(
                polynomial(&[1, 0, 2]),
                polynomial(&[0, 0, 1]),
            ),
            // Refused, degree bound negative.
            ExponentialIntegrand::polynomial_coefficient(polynomial(&[1]), polynomial(&[0, 0, -1])),
            // Refused, degree bound SATISFIED.
            ExponentialIntegrand::polynomial_coefficient(
                polynomial(&[1, 1]),
                polynomial(&[0, 0, 1]),
            ),
            // Refused structurally on a simple pole.
            ExponentialIntegrand::rational_coefficient(
                polynomial(&[1]),
                polynomial(&[0, 1]),
                polynomial(&[0, 1]),
            ),
        ]
    }

    #[test]
    fn a_constant_exponent_is_refused_because_it_is_not_this_chart_at_all() {
        let integrand =
            ExponentialIntegrand::polynomial_coefficient(polynomial(&[1]), polynomial(&[3]));
        assert_eq!(
            read_elementary_chart(&integrand),
            Err(ElementaryChartError::ConstantExponent)
        );
    }
}
