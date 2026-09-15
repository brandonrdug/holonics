//! Source-driven analytic navigation over certified complex receiver boxes.

use super::{ComplexInterval, ComplexJet2, ExactAnalysisError, Rat, RatComplex, RatInterval};
use num_traits::{One, Signed, Zero};
use serde::{Deserialize, Serialize};
use thiserror::Error;

/// A square receiver box in the complex source chart.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ComplexSquare {
    pub center: RatComplex,
    pub radius: Rat,
}

impl ComplexSquare {
    pub fn new(center: RatComplex, radius: Rat) -> Result<Self, NavigationError> {
        if radius.is_negative() {
            return Err(NavigationError::InvalidRadius);
        }
        Ok(Self { center, radius })
    }

    pub fn interval(&self) -> ComplexInterval {
        ComplexInterval::new(
            RatInterval::new(
                &self.center.re - &self.radius,
                &self.center.re + &self.radius,
            ),
            RatInterval::new(
                &self.center.im - &self.radius,
                &self.center.im + &self.radius,
            ),
        )
    }

    pub fn contains(&self, value: &ComplexInterval) -> bool {
        value.re.lower >= &self.center.re - &self.radius
            && value.re.upper <= &self.center.re + &self.radius
            && value.im.lower >= &self.center.im - &self.radius
            && value.im.upper <= &self.center.im + &self.radius
    }
}

#[derive(Debug, Error)]
pub enum NavigationError {
    #[error(transparent)]
    Analysis(#[from] ExactAnalysisError),
    #[error("navigation square radius is negative")]
    InvalidRadius,
    #[error("the source derivative does not certify a contraction: q={q}")]
    NonContractive { q: Rat },
    #[error("the certified anchor capture does not fit: beta={beta}, q={q}, radius={radius}")]
    CaptureMiss { beta: Rat, q: Rat, radius: Rat },
    #[error("the propagation horizon ended with an unresolved source box")]
    HorizonExhausted,
}

/// Certified capture data for a source callback on `B∞(center,radius)`. The callback is evaluated
/// on the whole square for the derivative bound and at the explicit anchor for the displacement;
/// no midpoint is substituted for either source or propagated interval.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CaptureCertificate {
    pub square: ComplexSquare,
    pub lambda: Rat,
    pub derivative: ComplexInterval,
    pub q: Rat,
    pub anchor_displacement: Rat,
    pub contraction_margin: Rat,
}

pub fn certify_capture<F>(
    source: F,
    center: &RatComplex,
    radius: &Rat,
    lambda: &Rat,
) -> Result<CaptureCertificate, NavigationError>
where
    F: Fn(&ComplexInterval) -> Result<ComplexJet2, ExactAnalysisError>,
{
    let square = ComplexSquare::new(center.clone(), radius.clone())?;
    let domain_jet = source(&square.interval())?;
    let derivative = domain_jet.relaxed_release_derivative(lambda)?;
    let q = derivative.re.abs_upper() + derivative.im.abs_upper();
    if q >= Rat::one() {
        return Err(NavigationError::NonContractive { q });
    }
    let anchor = ComplexInterval::point(center.clone());
    let anchor_jet = source(&anchor)?;
    let displacement = anchor_jet
        .relaxed_release(&anchor, lambda)?
        .subtract(&anchor);
    let beta = displacement.re.abs_upper().max(displacement.im.abs_upper());
    let margin = radius - (&beta + &q * radius);
    if margin <= Rat::zero() {
        return Err(NavigationError::CaptureMiss {
            beta,
            q,
            radius: radius.clone(),
        });
    }
    Ok(CaptureCertificate {
        square,
        lambda: lambda.clone(),
        derivative,
        q,
        anchor_displacement: beta,
        contraction_margin: margin,
    })
}

/// A propagation outcome. The source callback and release law are supplied by the caller; equal
/// regions or equal callbacks do not establish that two certificates describe the same source.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum PropagationStatus {
    Captured { index: usize },
    HorizonExhausted,
    Obstructed { reason: String },
}

/// Propagate a complete source box through relaxed release until it lies in one supplied capture
/// square. The finite horizon and rounding grain are receiver apparatus, while every remaining
/// interval is retained as the returned source face, including obstruction and exhaustion.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PropagationReturn {
    pub steps: u32,
    pub remaining: ComplexInterval,
    pub status: PropagationStatus,
}

/// One centered mean-value release inclusion. `current.midpoint()` is an explicit proof anchor;
/// the source is evaluated at that point and over the whole box, so the source box is never
/// replaced by its midpoint.
pub fn mean_value_release<F>(
    source: F,
    current: &ComplexInterval,
    lambda: &Rat,
    bits: u32,
) -> Result<ComplexInterval, ExactAnalysisError>
where
    F: Fn(&ComplexInterval) -> Result<ComplexJet2, ExactAnalysisError>,
{
    let anchor = ComplexInterval::point(current.midpoint());
    let anchor_image = source(&anchor)?.relaxed_release(&anchor, lambda)?;
    let derivative = source(current)?.relaxed_release_derivative(lambda)?;
    Ok(anchor_image
        .add(&derivative.multiply(&current.subtract(&anchor)))
        .round_out(bits))
}

pub fn propagate_to_capture<F>(
    source: F,
    mut current: ComplexInterval,
    lambda: &Rat,
    captures: &[CaptureCertificate],
    horizon: u32,
    bits: u32,
) -> PropagationReturn
where
    F: Fn(&ComplexInterval) -> Result<ComplexJet2, ExactAnalysisError>,
{
    for (capture, certificate) in captures.iter().enumerate() {
        if certificate.lambda == *lambda && certificate.square.contains(&current) {
            return PropagationReturn {
                steps: 0,
                remaining: current,
                status: PropagationStatus::Captured { index: capture },
            };
        }
    }
    for steps in 1..=horizon {
        let next = match mean_value_release(&source, &current, lambda, bits) {
            Ok(next) => next,
            Err(error) => {
                return PropagationReturn {
                    steps: steps - 1,
                    remaining: current,
                    status: PropagationStatus::Obstructed {
                        reason: error.to_string(),
                    },
                };
            }
        };
        current = next;
        for (capture, certificate) in captures.iter().enumerate() {
            if certificate.lambda == *lambda && certificate.square.contains(&current) {
                return PropagationReturn {
                    steps,
                    remaining: current,
                    status: PropagationStatus::Captured { index: capture },
                };
            }
        }
    }
    PropagationReturn {
        steps: horizon,
        remaining: current,
        status: PropagationStatus::HorizonExhausted,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::exact::rat;

    fn point(real: i64, imaginary: i64) -> ComplexInterval {
        ComplexInterval::point(RatComplex::new(rat(real, 1), rat(imaginary, 1)))
    }

    fn quadratic(source: &ComplexInterval) -> Result<ComplexJet2, ExactAnalysisError> {
        Ok(ComplexJet2 {
            value: source.multiply(source).subtract(&point(2, 0)),
            first: source.scale(&rat(2, 1)),
            second: point(2, 0),
        })
    }

    #[test]
    fn quadratic_capture_and_family_propagation_are_exact() {
        let center = RatComplex::new(rat(7, 5), rat(0, 1));
        let radius = rat(1, 8);
        let lambda = rat(1, 1);
        let certificate = certify_capture(quadratic, &center, &radius, &lambda).unwrap();
        assert!(certificate.q < rat(1, 1));
        assert!(certificate.anchor_displacement.clone() + &certificate.q * &radius < radius);

        let initial = ComplexInterval::new(
            RatInterval::new(rat(5, 4), rat(3, 2)),
            RatInterval::point(rat(0, 1)),
        );
        let result = propagate_to_capture(
            quadratic,
            initial,
            &lambda,
            std::slice::from_ref(&certificate),
            4,
            32,
        );
        assert!(result.steps > 0);
        assert!(matches!(result.status, PropagationStatus::Captured { .. }));
        assert!(certificate.square.contains(&result.remaining));
    }

    #[test]
    fn critical_derivative_is_an_explicit_navigation_obstruction() {
        let source = |_: &ComplexInterval| {
            Ok(ComplexJet2 {
                value: point(1, 0),
                first: ComplexInterval::zero(),
                second: point(2, 0),
            })
        };
        assert!(matches!(
            certify_capture(source, &RatComplex::zero(), &rat(1, 4), &rat(1, 1)),
            Err(NavigationError::Analysis(
                ExactAnalysisError::DivisionByIntervalContainingZero
            ))
        ));
    }

    #[test]
    fn propagation_retains_box_on_exhaustion_and_obstruction() {
        let initial = ComplexInterval::new(
            RatInterval::new(rat(1, 1), rat(2, 1)),
            RatInterval::point(rat(0, 1)),
        );
        let exhausted = propagate_to_capture(quadratic, initial.clone(), &rat(1, 1), &[], 0, 16);
        assert_eq!(exhausted.remaining, initial);
        assert!(matches!(
            exhausted.status,
            PropagationStatus::HorizonExhausted
        ));

        let obstructed_source =
            |_: &ComplexInterval| Err(ExactAnalysisError::DivisionByIntervalContainingZero);
        let obstructed =
            propagate_to_capture(obstructed_source, initial.clone(), &rat(1, 1), &[], 2, 16);
        assert_eq!(obstructed.steps, 0);
        assert_eq!(obstructed.remaining, initial);
        assert!(matches!(
            obstructed.status,
            PropagationStatus::Obstructed { .. }
        ));
    }

    #[test]
    fn mean_value_release_contains_quadratic_corner_releases() {
        let current = ComplexInterval::new(
            RatInterval::new(rat(5, 4), rat(3, 2)),
            RatInterval::new(rat(-1, 8), rat(1, 8)),
        );
        let enclosure = mean_value_release(quadratic, &current, &rat(1, 1), 32).unwrap();
        for real in [rat(5, 4), rat(3, 2)] {
            for imaginary in [rat(-1, 8), rat(1, 8)] {
                let corner = ComplexInterval::point(RatComplex::new(real.clone(), imaginary));
                let image = quadratic(&corner)
                    .unwrap()
                    .relaxed_release(&corner, &rat(1, 1))
                    .unwrap();
                assert!(image.re.lower >= enclosure.re.lower);
                assert!(image.re.upper <= enclosure.re.upper);
                assert!(image.im.lower >= enclosure.im.lower);
                assert!(image.im.upper <= enclosure.im.upper);
            }
        }
    }

    #[test]
    fn negative_square_radius_is_refused_by_name() {
        assert!(matches!(
            ComplexSquare::new(RatComplex::zero(), rat(-1, 1)),
            Err(NavigationError::InvalidRadius)
        ));
    }
}
