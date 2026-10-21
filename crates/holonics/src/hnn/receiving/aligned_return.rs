//! The class return of one complete full-fibre receiving section.
//!
//! With the producing tree schedule and population held, its probability is
//! P = (1-rho) product q_t + rho product r_t. Every station uses the SAME final
//! responsibility beta = rho product r_t / P. A rational representative is an
//! explicitly certified return chart, never an exact-irrational-to-rational cast.
//! Its logit-space certificate authorizes no material publication: the actual
//! producing Word and the explicitly selected publication policy still govern that.
//! The certified reference requests a complete finite candidate comparison; an opt-in
//! local receiving response retains its NormalLaw guards without that additional veto.

use super::*;
use num_bigint::BigInt;
use num_traits::{Signed, ToPrimitive};

#[derive(Clone, Debug, PartialEq, Eq)]
/// Rational return carrier and finite certified observations of its defining relation.
/// `gradient` is a certified dyadic return chart, not an exact source gradient or a publication certificate.
pub struct RetainedStationReturn {
    pub target: usize,
    pub normalized_representative: Vec<Rat>,
    /// Actual dyadic simplex foil of the return chart; distinct from the true face/masses.
    pub packed_foil: Vec<Rat>,
    pub packing_bits: u32,
    pub gradient: Vec<Rat>,
    pub component_bounds: Vec<ExactInterval>,
    pub component_error: Vec<Rat>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
/// The shared population operand stays an interval. `beta_representative` belongs only
/// to the rational simplex anchor of the executable return chart; component errors and the descent inequality
/// certify its use. Refining an enclosure never changes the symbolic source identity.
pub struct RetainedSectionReturn {
    // Issued only with the actual immutable producing section. Public reading
    // fields cannot be substituted into a material certificate without this owner.
    origin: std::sync::Arc<RetainedSectionOrigin>,
    pub rho: ExactInterval,
    pub beta: ExactInterval,
    pub beta_representative: Rat,
    pub stations: Vec<RetainedStationReturn>,
    pub norm_squared: Rat,
    pub error_pairing: Rat,
    pub exact_zero: bool,
    pub reading_bits: u32,
    /// Actual completed return-construction owner calls across its demand ladder.
    /// These exclude the epoch's initial chronological score and all exterior diagnostics;
    /// they do not infer internal root/log, kernel, transfer or synchronization counts.
    pub section_score_evaluations: u64,
    pub station_mass_evaluations: u64,
    pub station_weight_evaluations: u64,
}

#[derive(Clone, PartialEq, Eq)]
pub(crate) struct RetainedSectionOrigin {
    pub(crate) population: PortPopulation,
    pub(crate) ring: usize,
    pub(crate) combined: Option<Faces>,
    pub(crate) waves: Vec<Vec<Rat>>,
    pub(crate) trees: Vec<LandmarkFace>,
    pub(crate) targets: Vec<usize>,
    pub(crate) rho: ExactInterval,
    pub(crate) beta: ExactInterval,
    pub(crate) stations: Vec<RetainedStationReturn>,
    pub(crate) bits: u32,
    _issued: (),
}
impl std::fmt::Debug for RetainedSectionOrigin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("OwnerBoundRetainedSection")
            .field("ring", &self.ring)
            .field("targets", &self.targets)
            .field("bits", &self.bits)
            .finish_non_exhaustive()
    }
}

/// Exterior failure evidence, not an admitting constructor or a Word tape.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RetainedSectionSourceReading {
    pub population: PortPopulation,
    pub ring: usize,
    pub waves: Vec<Vec<Rat>>,
    pub trees: Vec<LandmarkFace>,
    pub targets: Vec<usize>,
    pub rho: ExactInterval,
    pub beta: ExactInterval,
    pub stations: Vec<RetainedStationReturn>,
    pub bits: u32,
}
impl RetainedSectionOrigin {
    pub(crate) fn reading(&self) -> RetainedSectionSourceReading {
        RetainedSectionSourceReading {
            population: self.population.clone(),
            ring: self.ring,
            waves: self.waves.clone(),
            trees: self.trees.clone(),
            targets: self.targets.clone(),
            rho: self.rho.clone(),
            beta: self.beta.clone(),
            stations: self.stations.clone(),
            bits: self.bits,
        }
    }
}

fn fail(reason: &'static str) -> HnnError {
    HnnError::Unadmitted { reason }
}

/// Largest exact remainder on the existing finite row precision. No rounded-sum division.
fn pack_simplex(anchor: &[Rat], bits: u32) -> Result<Vec<Rat>, HnnError> {
    if u64::from(bits) > crate::receiver::population::PRECISION
        || anchor.is_empty()
        || anchor.iter().any(|x| x < &Rat::zero() || x > &Rat::one())
        || anchor.iter().cloned().sum::<Rat>() != Rat::one()
    {
        return Err(fail(
            "a dyadic return packs one simplex within the existing precision range",
        ));
    }
    let denominator = BigInt::from(1) << bits as usize;
    let scale = Rat::from_integer(denominator.clone());
    let mut numerators = Vec::with_capacity(anchor.len());
    let mut remainders = Vec::with_capacity(anchor.len());
    for value in anchor {
        let scaled = value * &scale;
        // Nonnegative rational: integer division is the exact floor.
        let floor = scaled.numer() / scaled.denom();
        remainders.push(scaled - Rat::from_integer(floor.clone()));
        numerators.push(floor);
    }
    let remaining = (&denominator - numerators.iter().cloned().sum::<BigInt>())
        .to_usize()
        .ok_or_else(|| fail("simplex remainder count fits its declared class count"))?;
    if remaining >= anchor.len() {
        return Err(fail(
            "simplex floor deficit is smaller than the class count",
        ));
    }
    let mut order: Vec<_> = (0..anchor.len()).collect();
    order.sort_by(|&a, &b| remainders[b].cmp(&remainders[a]).then_with(|| a.cmp(&b)));
    for &class in order.iter().take(remaining) {
        numerators[class] += 1;
    }
    let packed: Vec<_> = numerators
        .into_iter()
        .map(|n| Rat::new(n, denominator.clone()))
        .collect();
    let unit = Rat::new(BigInt::from(1), denominator);
    if packed.iter().cloned().sum::<Rat>() != Rat::one()
        || packed
            .iter()
            .zip(anchor)
            .any(|(p, a)| p < &Rat::zero() || p > &Rat::one() || (p - a).abs() > unit)
    {
        return Err(fail(
            "joint dyadic foil retains normalization, range and one-cell error",
        ));
    }
    Ok(packed)
}

fn true_foil_bounds(
    beta: &ExactInterval,
    mass: &ExactInterval,
    target: bool,
) -> Result<ExactInterval, HnnError> {
    let lower = mass.lower.clone().max(Rat::zero());
    let upper = mass.upper.clone().min(Rat::one());
    if target {
        Ok(ExactInterval::new(
            Rat::one() - &beta.upper * (Rat::one() - lower),
            Rat::one() - &beta.lower * (Rat::one() - upper),
        )?)
    } else {
        Ok(ExactInterval::new(
            &beta.lower * lower,
            &beta.upper * upper,
        )?)
    }
}

impl RetainedSectionReturn {
    #[cfg(test)]
    pub(crate) fn source_reading(&self) -> RetainedSectionSourceReading { self.origin.reading() }
    pub(crate) fn certificate_origin(
        &self,
        population: &PortPopulation,
        ring: usize,
        combined: &Faces,
        trees: &[LandmarkFace],
        targets: &[usize],
    ) -> Result<std::sync::Arc<RetainedSectionOrigin>, HnnError> {
        let o = &self.origin;
        if &o.population != population
            || o.ring != ring
            || o.combined.as_ref() != Some(combined)
            || o.waves != combined.logits
            || o.trees != trees
            || o.targets != targets
            || o.rho != self.rho
            || o.beta != self.beta
            || o.stations != self.stations
            || o.bits != self.reading_bits
        {
            return Err(fail(
                "retained certificate uses its immutable producing source/target/population/return",
            ));
        }
        Ok(std::sync::Arc::clone(o))
    }
    /// Only the native section owner supplies these producing operands. No posterior is
    /// reset or collapsed to a midpoint; rho stays one shared retained interval throughout.
    pub(crate) fn at(
        population: &PortPopulation,
        ring: usize,
        combined: &Faces,
        trees: &[LandmarkFace],
        targets: &[usize],
    ) -> Result<Self, HnnError> {
        Self::at_using(population, ring, Some(combined), &combined.logits, trees, targets, None)
    }
    pub(super) fn at_produced(
        population: &PortPopulation,
        ring: usize,
        combined: &Faces,
        trees: &[LandmarkFace],
        targets: &[usize],
        producer: &super::selected::ProducedRetainedSection,
    ) -> Result<Self, HnnError> {
        producer.validate(population, ring, combined, trees, targets)?;
        Self::at_using(population, ring, Some(combined), &combined.logits, trees, targets, Some(producer))
    }
    pub(crate) fn certificate_origin_raw(&self,population:&PortPopulation,ring:usize,waves:&[Vec<Rat>],trees:&[LandmarkFace],targets:&[usize]) -> Result<std::sync::Arc<RetainedSectionOrigin>,HnnError> {
        let o=&self.origin;
        if &o.population!=population || o.ring!=ring || o.waves!=waves || o.trees!=trees || o.targets!=targets || o.rho!=self.rho || o.beta!=self.beta || o.stations!=self.stations || o.bits!=self.reading_bits {
            return Err(fail("retained certificate binds immutable raw source/target/population/return"));
        }
        Ok(std::sync::Arc::clone(o))
    }
    pub(super) fn at_native_produced(population:&PortPopulation,ring:usize,waves:&[Vec<Rat>],trees:&[LandmarkFace],targets:&[usize],producer:&super::selected::ProducedRetainedSection) -> Result<Self,HnnError> {
        producer.validate_raw(population,ring,waves,trees,targets)?;
        Self::at_using(population,ring,None,waves,trees,targets,Some(producer))
    }
    fn at_using(
        population: &PortPopulation,
        ring: usize,
        combined: Option<&Faces>,
        waves: &[Vec<Rat>],
        trees: &[LandmarkFace],
        targets: &[usize],
        producer: Option<&super::selected::ProducedRetainedSection>,
    ) -> Result<Self, HnnError> {
        let rho = population.weight(COMBINED).map_err(population_refusal)?;
        if population.description(2).is_some() {
            return Err(fail(
                "this aligned return names the declared tree and combined families",
            ));
        }
        let mut section_score_evaluations = 0;
        let mut station_mass_evaluations = 0;
        let mut station_weight_evaluations = 0;
        for bits in cells::demand_ladder() {
            let scored = match producer {
                Some(p) => p.scored().clone(),
                None => {
                    let scored = score_at_law(
                        ReceivingLaw::RetainedFibreV1,
                        population,
                        ring,
                        combined.ok_or_else(|| fail("uncached retained scoring has genuine coarse operands"))?,
                        trees,
                        targets,
                        bits,
                    )?;
                    section_score_evaluations += 1;
                    scored
                }
            };
            let observations = producer.map(|p| p.observations_at(bits)).transpose()?;
            if let Some(p) = producer {
                if p.bits() != bits {
                    station_mass_evaluations += targets.len() as u64;
                    station_weight_evaluations += targets.len() as u64;
                }
            }
            let mut reads = Vec::with_capacity(targets.len());
            let mut q = Rat::one();
            let mut r_lo = Rat::one();
            let mut r_hi = Rat::one();
            for (at, reading) in scored.face_readings.iter().enumerate() {

                let masses = match &observations {
                    Some(rows) => rows[at].masses().to_vec(),
                    None => {
                        station_mass_evaluations += 1;
                        reading.retained_observation(bits)?.masses().to_vec()
                    }
                };
                let target = targets[at];
                q *= &reading.tree_probabilities()?[target];
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
                let weights = match &observations {
                    Some(rows) => rows[at].weights().to_vec(),
                    None => {
                        station_weight_evaluations += 1;
                        reading.retained_weights_at(bits)?
                    }
                };
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
                let anchor: Vec<_> = normalized_representative
                    .iter()
                    .enumerate()
                    .map(|(class, r)| {
                        let indicator = if class == target {
                            Rat::one()
                        } else {
                            Rat::zero()
                        };
                        &indicator + &beta_hat * (r - &indicator)
                    })
                    .collect();
                // Only the executable effective-foil chart is packed. The actual shared
                // rho/beta, full-fibre face, normalized masses and true score are unchanged.
                let packed_foil = pack_simplex(&anchor, bits)?;
                let mut gradient = Vec::with_capacity(masses.len());
                let mut component_bounds = Vec::with_capacity(masses.len());
                let mut component_error = Vec::with_capacity(masses.len());
                for (class, mass) in masses.iter().enumerate() {
                    let indicator = if class == target {
                        Rat::one()
                    } else {
                        Rat::zero()
                    };
                    let g = &packed_foil[class] - &indicator;
                    let foil_bounds = true_foil_bounds(&beta, mass, class == target)?;
                    let bounds = ExactInterval::new(
                        foil_bounds.lower - &indicator,
                        foil_bounds.upper - &indicator,
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
                    packed_foil,
                    packing_bits: bits,
                    gradient,
                    component_bounds,
                    component_error,
                });
            }
            if exact_zero || norm_squared > error_pairing {
                let origin = std::sync::Arc::new(RetainedSectionOrigin {
                    population: population.clone(),
                    ring,
                    combined: combined.cloned(),
                    waves: waves.to_vec(),
                    trees: trees.to_vec(),
                    targets: targets.to_vec(),
                    rho: rho.clone(),
                    beta: beta.clone(),
                    stations: stations.clone(),
                    bits,
                    _issued: (),
                });
                return Ok(Self {
                    origin,
                    rho,
                    beta,
                    beta_representative: beta_hat,
                    stations,
                    norm_squared,
                    error_pairing,
                    exact_zero,
                    reading_bits: bits,
                    section_score_evaluations,
                    station_mass_evaluations,
                    station_weight_evaluations,
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

    #[test]
    fn dyadic_foil_singleton_beta_and_shared_interval_keep_true_error_certificate() {
        let packed = pack_simplex(&[rat(5, 6), rat(1, 6)], 3).unwrap();
        assert_eq!(packed, vec![rat(7, 8), rat(1, 8)]);
        let beta = ExactInterval::point(rat(1, 3));
        let mass = ExactInterval::point(rat(1, 2));
        let mut norm = Rat::zero();
        let mut error_pair = Rat::zero();
        for (class, p) in packed.iter().enumerate() {
            let h = true_foil_bounds(&beta, &mass, class == 0).unwrap();
            let error = (p - &h.lower).abs().max((p - &h.upper).abs());
            assert_eq!(error, rat(1, 24));
            let g = p - if class == 0 { Rat::one() } else { Rat::zero() };
            norm += &g * &g;
            error_pair += error * g.abs();
        }
        assert_eq!(norm - error_pair, rat(1, 48));
        assert_eq!(beta, ExactInterval::point(rat(1, 3)));
        let interval = ExactInterval::new(rat(1, 4), rat(1, 2)).unwrap();
        let packed = pack_simplex(&[rat(13, 16), rat(3, 16)], 4).unwrap();
        let mut margin = Rat::zero();
        for (class, p) in packed.iter().enumerate() {
            let h = true_foil_bounds(&interval, &mass, class == 0).unwrap();
            let error = (p - &h.lower).abs().max((p - &h.upper).abs());
            let g = p - if class == 0 { Rat::one() } else { Rat::zero() };
            margin += &g * &g - error * g.abs();
        }
        assert_eq!(margin, rat(3, 64));
        assert_eq!(interval, ExactInterval::new(rat(1, 4), rat(1, 2)).unwrap());
    }

    #[test]
    fn dyadic_foil_exact_simplex_ties_zero_and_resolution_limit() {
        assert_eq!(
            pack_simplex(&vec![rat(1, 3); 3], 3).unwrap(),
            vec![rat(3, 8), rat(3, 8), rat(1, 4)]
        );
        assert_eq!(
            pack_simplex(&[Rat::one(), Rat::zero()], 0).unwrap(),
            vec![Rat::one(), Rat::zero()]
        );
        let tiny = Rat::new(BigInt::from(1), BigInt::from(1) << 100usize);
        let packed = pack_simplex(&[Rat::one() - &tiny, tiny], 32).unwrap();
        assert_eq!(packed, vec![Rat::one(), Rat::zero()]); // zero represented return, not strict gain
        for p in packed {
            assert_eq!(
                p.denom() >> p.denom().trailing_zeros().unwrap() as usize,
                BigInt::from(1)
            );
        }
    }

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
