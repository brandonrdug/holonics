//! The class return of one complete full-fibre receiving section.
//!
//! With the producing tree schedule and population held, its probability is
//! P = (1-rho) product q_t + rho product r_t. Every station uses the SAME final
//! responsibility beta = rho product r_t / P. A rational representative is an
//! explicitly certified return chart, never an exact-irrational-to-rational cast.
//! Its logit-space certificate authorizes no material publication: the actual
//! producing Word and complete finite candidate comparison still govern that.

use super::*;
use num_traits::Signed;

#[derive(Clone, Debug, PartialEq, Eq)]
/// Rational return carrier and finite certified observations of its defining relation.
/// `gradient` is an admitted rational direction, not a completed irrational source value.
pub struct RetainedStationReturn {
    pub target: usize,
    pub normalized_representative: Vec<Rat>,
    pub gradient: Vec<Rat>,
    pub component_bounds: Vec<ExactInterval>,
    pub component_error: Vec<Rat>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// The shared population operand stays an interval. `beta_representative` belongs only
/// to the executable rational return chart; component errors and the descent inequality
/// certify its use. Refining an enclosure never changes the symbolic source identity.
pub struct RetainedSectionReturn {
    pub rho: ExactInterval,
    pub beta: ExactInterval,
    pub beta_representative: Rat,
    pub stations: Vec<RetainedStationReturn>,
    pub norm_squared: Rat,
    pub error_pairing: Rat,
    pub exact_zero: bool,
    pub reading_bits: u32,
}

fn fail(reason: &'static str) -> HnnError {
    HnnError::Unadmitted { reason }
}

impl RetainedSectionReturn {
    /// Only the native section owner supplies these producing operands. No posterior is
    /// reset or collapsed to a midpoint; rho stays one shared retained interval throughout.
    pub(crate) fn at(
        population: &PortPopulation,
        ring: usize,
        combined: &Faces,
        trees: &[LandmarkFace],
        targets: &[usize],
    ) -> Result<Self, HnnError> {
        let rho = population.weight(COMBINED).map_err(population_refusal)?;
        if population.description(2).is_some() {
            return Err(fail(
                "this aligned return names the declared tree and combined families",
            ));
        }
        for bits in cells::demand_ladder() {
            let scored = score_at_law(
                ReceivingLaw::RetainedFibreV1,
                population,
                ring,
                combined,
                trees,
                targets,
                bits,
            )?;
            let mut reads = Vec::with_capacity(targets.len());
            let mut q = Rat::one();
            let mut r_lo = Rat::one();
            let mut r_hi = Rat::one();
            for (at, reading) in scored.face_readings.iter().enumerate() {
                let SelectedFaceReading::Retained(reading) = reading else {
                    return Err(fail(
                        "an aligned section retains its selected receiving law",
                    ));
                };
                let masses = reading.combined_masses_at(bits)?;
                let target = targets[at];
                q *= &reading.tree_probabilities[target];
                r_lo *= &masses[target].lower;
                r_hi *= &masses[target].upper;
                reads.push((reading, masses));
            }
            let beta_at = |rho: &Rat, r: &Rat| -> Result<Rat, HnnError> {
                let numerator = rho * r;
                let denominator = (Rat::one() - rho) * &q + &numerator;
                if denominator <= Rat::zero() {
                    return Err(fail(
                        "an aligned section has positive total target probability",
                    ));
                }
                Ok(numerator / denominator)
            };
            let beta =
                ExactInterval::new(beta_at(&rho.lower, &r_lo)?, beta_at(&rho.upper, &r_hi)?)?;
            let beta_hat = (&beta.lower + &beta.upper) / integer(2);
            let mut stations = Vec::with_capacity(reads.len());
            let mut norm_squared = Rat::zero();
            let mut error_pairing = Rat::zero();
            let mut exact_zero = true;
            for (at, (reading, masses)) in reads.into_iter().enumerate() {
                let weights = reading.receiver.weights_at(&reading.read, bits)?;
                let representatives: Vec<_> = weights
                    .iter()
                    .map(|w| (&w.lower + &w.upper) / integer(2))
                    .collect();
                let z: Rat = representatives.iter().cloned().sum();
                if z <= Rat::zero() {
                    return Err(fail(
                        "a rational return chart normalizes joint positive weights",
                    ));
                }
                let normalized_representative: Vec<_> =
                    representatives.into_iter().map(|x| x / &z).collect();
                let target = targets[at];
                let mut gradient = Vec::with_capacity(masses.len());
                let mut component_bounds = Vec::with_capacity(masses.len());
                let mut component_error = Vec::with_capacity(masses.len());
                for (class, mass) in masses.iter().enumerate() {
                    let indicator = if class == target {
                        Rat::one()
                    } else {
                        Rat::zero()
                    };
                    let g = &beta_hat * (&normalized_representative[class] - &indicator);
                    let low = &mass.lower - &indicator;
                    let high = &mass.upper - &indicator;
                    let corners = [
                        &beta.lower * &low,
                        &beta.lower * &high,
                        &beta.upper * &low,
                        &beta.upper * &high,
                    ];
                    let bounds = ExactInterval::new(
                        corners.iter().min().unwrap().clone(),
                        corners.iter().max().unwrap().clone(),
                    )?;
                    let error = (&bounds.lower - &g).abs().max((&bounds.upper - &g).abs());
                    exact_zero &= bounds.lower.is_zero() && bounds.upper.is_zero();
                    norm_squared += &g * &g;
                    error_pairing += &error * g.abs();
                    gradient.push(g);
                    component_bounds.push(bounds);
                    component_error.push(error);
                }
                if gradient.iter().cloned().sum::<Rat>() != Rat::zero() {
                    return Err(fail(
                        "a jointly normalized class return is common-shift neutral",
                    ));
                }
                stations.push(RetainedStationReturn {
                    target,
                    normalized_representative,
                    gradient,
                    component_bounds,
                    component_error,
                });
            }
            if exact_zero || norm_squared > error_pairing {
                return Ok(Self {
                    rho,
                    beta,
                    beta_representative: beta_hat,
                    stations,
                    norm_squared,
                    error_pairing,
                    exact_zero,
                    reading_bits: bits,
                });
            }
        }
        Err(fail(
            "the full-section rational class return is unresolved on the native demand ladder",
        ))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::rat;

    fn section(
        waves: Vec<Vec<Rat>>,
        targets: &[usize],
        population: &PortPopulation,
    ) -> RetainedSectionReturn {
        let tree = LandmarkFace {
            grain: 4,
            probabilities: vec![rat(1, 2), rat(1, 2)],
            exponents: vec![(-4).into(), (-4).into()],
        };
        let trees = vec![tree; waves.len()];
        let reads = waves
            .into_iter()
            .zip(&trees)
            .map(|(w, q)| ReceivingRead::combined(w, q, 4).unwrap())
            .collect::<Vec<_>>();
        let faces = Faces::of_reads(&reads, 4).unwrap();
        RetainedSectionReturn::at(population, 2, &faces, &trees, targets).unwrap()
    }

    #[test]
    fn aligned_return_zero_wave_keeps_half_responsibility_and_nonzero_class_sensitivity() {
        let read = section(vec![vec![integer(0); 4]], &[0], &receiving_population());
        assert_eq!(read.beta, ExactInterval::point(rat(1, 2)));
        assert_eq!(read.stations[0].gradient, vec![rat(-1, 4), rat(1, 4)]);
        assert!(read.norm_squared > read.error_pairing);
    }

    #[test]
    fn aligned_return_uses_one_final_section_responsibility_not_local_alpha() {
        let read = section(
            vec![vec![integer(1), integer(0), integer(-1), integer(0)]; 2],
            &[0, 0],
            &receiving_population(),
        );
        assert!(read.beta.lower <= rat(64, 89) && read.beta.upper >= rat(64, 89));
        for station in &read.stations {
            assert_eq!(station.gradient.iter().cloned().sum::<Rat>(), Rat::zero());
            assert!(station.component_bounds[0].lower <= rat(-64, 445));
            assert!(station.component_bounds[0].upper >= rat(-64, 445));
        }
    }

    #[test]
    fn aligned_return_dead_family_is_exact_zero_without_reset() {
        let mut population = receiving_population();
        population
            .receive(&[
                ExactInterval::point(rat(1, 2)),
                ExactInterval::point(integer(0)),
            ])
            .unwrap();
        let original = population.clone();
        let read = section(vec![vec![integer(0); 4]], &[0], &population);
        assert!(read.exact_zero);
        assert_eq!(read.stations[0].gradient, vec![integer(0); 2]);
        assert_eq!(population, original);
    }
}
