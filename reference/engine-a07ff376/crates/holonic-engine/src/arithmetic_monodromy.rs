//! Exact transport from an integral quintic through prime-place monodromy and Euler receivers.
//!
//! This is one production mathematical world, not a Galois-group lookup table or a rendered
//! polynomial fixture. An inherited degree-five integral polynomial is changed by an exact
//! rational root-scale into the monic integer probe accepted by [`crate::PrimeEcologyLaw`].
//! Every subsequently founded prime receives that same probe. The emitted finite-field
//! factorization is transported, without re-factorization here, into:
//!
//! - an unramified Frobenius cycle section;
//! - an exact conditional fiber of transitive quintic Galois groups;
//! - a formal permutation-Euler denominator; and
//! - every already-open exact integer-sigma Euler receiver.
//!
//! The transitive-group catalogue is inherited mathematics. Observed cycle types may restrict
//! it, and one irreducible reduction certifies rational irreducibility, but absence of an
//! unobserved cycle type never excludes a group. A repeated reduction is retained as an open
//! polynomial-discriminant place; this law does not pretend that the chosen power basis supplies
//! a ramified number-field Euler factor.
//!
//! The accompanying atlas is an exact local-chart receipt. It carries no screen coordinates and
//! makes no canonical identification between root sheets at different prime receivers.

use std::collections::{BTreeMap, BTreeSet, VecDeque};

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::{
    ArithmeticFiberEvent, CausalMaterialKind, DEFAULT_HORN_LOCAL_SECTION_LIMIT, EventId,
    EventSuccessor, ExactEventLaw, IntegerPolynomialProbe, PolynomialFiberSignature,
    PolynomialPrimeFiber, PolynomialProbeId, PrimeEcologyError, PrimeEcologyEvent,
    PrimeEcologyGeometryReceipt, PrimeEcologyLaw, PrimeEcologyRadiation, PrimeEcologyStanding,
};

const QUINTIC_DEGREE: usize = 5;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct QuinticProblemId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct EulerReceiverId(pub u64);

/// One inherited integral quintic, coefficient-first.
///
/// The leading coefficient may be any nonzero integer. Scalar content is not erased: it remains
/// visible in the inherited presentation even though it does not change the root population.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct IntegralQuinticProblem {
    pub schema: String,
    pub id: QuinticProblemId,
    pub name: String,
    pub coefficients: Vec<BigInt>,
}

impl IntegralQuinticProblem {
    pub fn new(
        id: QuinticProblemId,
        name: impl Into<String>,
        coefficients: Vec<BigInt>,
    ) -> Result<Self, ArithmeticMonodromyError> {
        let problem = Self {
            schema: "holonic-engine.integral-quintic-problem.v1".to_owned(),
            id,
            name: name.into(),
            coefficients,
        };
        problem.validate()?;
        Ok(problem)
    }

    pub fn validate(&self) -> Result<(), ArithmeticMonodromyError> {
        if self.schema != "holonic-engine.integral-quintic-problem.v1"
            || self.name.is_empty()
            || self.coefficients.len() != QUINTIC_DEGREE + 1
            || self.coefficients[QUINTIC_DEGREE].is_zero()
        {
            return Err(ArithmeticMonodromyError::MalformedQuintic(self.id));
        }
        Ok(())
    }

    /// Change `f(x)` into the monic integral polynomial
    ///
    /// `g(y) = a_5^4 f(y/a_5)`, with `y = a_5 x`.
    ///
    /// This preserves the splitting field over `Q`; it is not a numerical normalization.
    pub fn normalize(&self) -> Result<NormalizedQuintic, ArithmeticMonodromyError> {
        self.validate()?;
        let root_scale = self.coefficients[QUINTIC_DEGREE].clone();
        let mut normalized_coefficients = Vec::with_capacity(QUINTIC_DEGREE + 1);
        for (degree, coefficient) in self.coefficients[..QUINTIC_DEGREE].iter().enumerate() {
            let exponent = u32::try_from(QUINTIC_DEGREE - 1 - degree)
                .map_err(|_| ArithmeticMonodromyError::CarrierOverflow)?;
            normalized_coefficients.push(coefficient * root_scale.pow(exponent));
        }
        normalized_coefficients.push(BigInt::one());
        let probe = IntegerPolynomialProbe::new(
            PolynomialProbeId(self.id.0),
            format!("quintic[{}]", self.name),
            normalized_coefficients.clone(),
        )?;
        let discriminant = monic_polynomial_discriminant(&normalized_coefficients)?;
        let discriminant_square_root = rational_integer_square_root(&discriminant);
        Ok(NormalizedQuintic {
            schema: "holonic-engine.normalized-quintic.v1".to_owned(),
            problem: self.id,
            root_scale,
            coefficients: normalized_coefficients,
            discriminant,
            discriminant_square_root,
            probe,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NormalizedQuintic {
    pub schema: String,
    pub problem: QuinticProblemId,
    /// `normalized_root = root_scale * inherited_root`.
    pub root_scale: BigInt,
    pub coefficients: Vec<BigInt>,
    pub discriminant: BigInt,
    /// Present exactly when the discriminant is a square in `Q`.
    pub discriminant_square_root: Option<BigInt>,
    pub probe: IntegerPolynomialProbe,
}

impl NormalizedQuintic {
    fn validate(&self, inherited: &IntegralQuinticProblem) -> Result<(), ArithmeticMonodromyError> {
        if self.schema != "holonic-engine.normalized-quintic.v1"
            || self.problem != inherited.id
            || self.probe.id != PolynomialProbeId(inherited.id.0)
            || self.coefficients.len() != QUINTIC_DEGREE + 1
            || self.coefficients.last() != Some(&BigInt::one())
            || self.probe.coefficients != self.coefficients
            || self.discriminant != monic_polynomial_discriminant(&self.coefficients)?
            || self.discriminant_square_root != rational_integer_square_root(&self.discriminant)
        {
            return Err(ArithmeticMonodromyError::MalformedNormalization(
                inherited.id,
            ));
        }
        let expected = inherited.normalize()?;
        if *self != expected {
            return Err(ArithmeticMonodromyError::MalformedNormalization(
                inherited.id,
            ));
        }
        Ok(())
    }
}

/// The five transitive subgroups of `S_5`, in their natural degree-five actions.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum QuinticTransitiveGroup {
    Cyclic5,
    Dihedral5,
    Frobenius20,
    Alternating5,
    Symmetric5,
}

impl QuinticTransitiveGroup {
    pub fn order(self) -> u32 {
        match self {
            Self::Cyclic5 => 5,
            Self::Dihedral5 => 10,
            Self::Frobenius20 => 20,
            Self::Alternating5 => 60,
            Self::Symmetric5 => 120,
        }
    }

    pub fn solvable_by_radicals(self) -> bool {
        matches!(self, Self::Cyclic5 | Self::Dihedral5 | Self::Frobenius20)
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum QuinticIrreducibility {
    Open,
    /// One monic reduction remained irreducible of degree five, so Gauss reduction certifies
    /// irreducibility over `Q`.
    CertifiedByPrime {
        prime: u64,
        source_events: BTreeSet<EventId>,
    },
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QuinticGaloisFiber {
    pub schema: String,
    pub discriminant: BigInt,
    pub discriminant_square_root: Option<BigInt>,
    pub irreducibility: QuinticIrreducibility,
    /// Cycle type -> every prime receiver which returned that exact type.
    pub cycle_witnesses: BTreeMap<Vec<u32>, BTreeSet<u64>>,
    /// Conditional until `irreducibility` closes. Empty means that the transitive catalogue was
    /// obstructed by the received sections; it does not classify a reducible polynomial.
    pub transitive_candidates: BTreeSet<QuinticTransitiveGroup>,
}

impl QuinticGaloisFiber {
    pub fn unique_certified_group(&self) -> Option<QuinticTransitiveGroup> {
        if matches!(
            self.irreducibility,
            QuinticIrreducibility::CertifiedByPrime { .. }
        ) && self.transitive_candidates.len() == 1
        {
            self.transitive_candidates.iter().copied().next()
        } else {
            None
        }
    }

    pub fn admitted_future_cycle_types(
        &self,
    ) -> Result<BTreeSet<Vec<u32>>, ArithmeticMonodromyError> {
        let catalogue = quintic_group_catalogue()?;
        Ok(self
            .transitive_candidates
            .iter()
            .flat_map(|group| catalogue[group].cycle_types.iter().cloned())
            .collect())
    }
}

/// One exact local receiver section transported from `PolynomialPrimeFiber`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QuinticPrimeSection {
    pub schema: String,
    pub problem: QuinticProblemId,
    pub probe: PolynomialProbeId,
    pub prime: u64,
    pub source_events: BTreeSet<EventId>,
    pub signature: PolynomialFiberSignature,
    /// Absent when the reduction has repeated factors.
    pub cycle_type: Option<Vec<u32>>,
    pub frobenius_order: Option<u32>,
    pub permutation_is_even: Option<bool>,
    /// `det(I - T Frobenius)` in the degree-five permutation representation,
    /// coefficient-first. Absent at a repeated polynomial-discriminant place.
    pub euler_denominator: Option<Vec<BigInt>>,
}

impl QuinticPrimeSection {
    pub fn is_unramified_power_basis_place(&self) -> bool {
        self.cycle_type.is_some()
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EulerLocalSection {
    pub prime: u64,
    pub cycle_type: Vec<u32>,
    pub denominator_polynomial: Vec<BigInt>,
    /// `det(I - p^(-sigma) Frobenius)^(-1)`.
    pub exact_value: Rat,
    pub source_events: BTreeSet<EventId>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExactEulerReceiverStanding {
    pub schema: String,
    pub id: EulerReceiverId,
    pub problem: QuinticProblemId,
    pub sigma: u32,
    pub opened_at: EventId,
    pub local_sections: BTreeMap<u64, EulerLocalSection>,
    /// Repeated reductions whose field-local factor is not supplied by this power-basis law.
    pub open_places: BTreeMap<u64, BTreeSet<EventId>>,
    pub exact_product: Rat,
}

impl ExactEulerReceiverStanding {
    fn new(
        id: EulerReceiverId,
        problem: QuinticProblemId,
        sigma: u32,
        opened_at: EventId,
    ) -> Result<Self, ArithmeticMonodromyError> {
        if sigma <= 1 {
            return Err(ArithmeticMonodromyError::InvalidEulerSigma(sigma));
        }
        Ok(Self {
            schema: "holonic-engine.exact-quintic-euler-receiver-standing.v1".to_owned(),
            id,
            problem,
            sigma,
            opened_at,
            local_sections: BTreeMap::new(),
            open_places: BTreeMap::new(),
            exact_product: Rat::one(),
        })
    }

    fn receive(
        &mut self,
        section: &QuinticPrimeSection,
    ) -> Result<EulerTransportDelta, ArithmeticMonodromyError> {
        if section.problem != self.problem {
            return Err(ArithmeticMonodromyError::ReceiverProblemMismatch {
                receiver: self.id,
                problem: section.problem,
            });
        }
        if self.local_sections.contains_key(&section.prime)
            || self.open_places.contains_key(&section.prime)
        {
            return Err(ArithmeticMonodromyError::RepeatedPrimeTransport {
                receiver: self.id,
                prime: section.prime,
            });
        }
        let local_section = if let Some((cycle_type, denominator)) = section
            .cycle_type
            .as_ref()
            .zip(section.euler_denominator.as_ref())
        {
            Some(EulerLocalSection {
                prime: section.prime,
                cycle_type: cycle_type.clone(),
                denominator_polynomial: denominator.clone(),
                exact_value: evaluate_euler_local_factor(section.prime, self.sigma, cycle_type)?,
                source_events: section.source_events.clone(),
            })
        } else {
            None
        };
        let admitted = local_section.is_some();
        if let Some(local_section) = local_section {
            self.exact_product *= &local_section.exact_value;
            self.local_sections.insert(section.prime, local_section);
        } else {
            self.open_places
                .insert(section.prime, section.source_events.clone());
        }
        Ok(EulerTransportDelta {
            receiver: self.id,
            problem: self.problem,
            prime: section.prime,
            admitted,
            product_after: self.exact_product.clone(),
        })
    }

    fn validate(&self, problem: &QuinticProblemStanding) -> Result<(), ArithmeticMonodromyError> {
        if self.schema != "holonic-engine.exact-quintic-euler-receiver-standing.v1"
            || self.problem != problem.problem.id
            || self.sigma <= 1
        {
            return Err(ArithmeticMonodromyError::MalformedEulerReceiver(self.id));
        }
        let mut expected = Self::new(self.id, self.problem, self.sigma, self.opened_at)?;
        for section in problem.prime_sections.values() {
            expected.receive(section)?;
        }
        if *self != expected {
            return Err(ArithmeticMonodromyError::MalformedEulerReceiver(self.id));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QuinticProblemStanding {
    pub schema: String,
    pub problem: IntegralQuinticProblem,
    pub inherited_at: EventId,
    pub normalized: NormalizedQuintic,
    pub prime_sections: BTreeMap<u64, QuinticPrimeSection>,
    pub galois: QuinticGaloisFiber,
}

impl QuinticProblemStanding {
    fn new(
        problem: IntegralQuinticProblem,
        inherited_at: EventId,
    ) -> Result<Self, ArithmeticMonodromyError> {
        let normalized = problem.normalize()?;
        let galois = initial_galois_fiber(&normalized)?;
        Ok(Self {
            schema: "holonic-engine.quintic-problem-standing.v1".to_owned(),
            problem,
            inherited_at,
            normalized,
            prime_sections: BTreeMap::new(),
            galois,
        })
    }

    fn receive(
        &mut self,
        fiber: &PolynomialPrimeFiber,
    ) -> Result<(QuinticPrimeSection, GaloisTransportDelta), ArithmeticMonodromyError> {
        if fiber.probe != self.normalized.probe.id {
            return Err(ArithmeticMonodromyError::FiberProbeMismatch {
                problem: self.problem.id,
                probe: fiber.probe,
            });
        }
        if self.prime_sections.contains_key(&fiber.prime) {
            return Err(ArithmeticMonodromyError::RepeatedPrimeSection {
                problem: self.problem.id,
                prime: fiber.prime,
            });
        }
        let section = derive_prime_section(self.problem.id, fiber)?;
        let before_candidates = self.galois.transitive_candidates.clone();
        let before_irreducibility = self.galois.irreducibility.clone();
        transport_section_into_galois(&mut self.galois, &section)?;
        let delta = GaloisTransportDelta {
            problem: self.problem.id,
            prime: fiber.prime,
            candidates_before: before_candidates,
            candidates_after: self.galois.transitive_candidates.clone(),
            irreducibility_before: before_irreducibility,
            irreducibility_after: self.galois.irreducibility.clone(),
            unique_group_after: self.galois.unique_certified_group(),
        };
        self.prime_sections.insert(fiber.prime, section.clone());
        Ok((section, delta))
    }

    fn validate(&self, ecology: &PrimeEcologyStanding) -> Result<(), ArithmeticMonodromyError> {
        if self.schema != "holonic-engine.quintic-problem-standing.v1" {
            return Err(ArithmeticMonodromyError::MalformedProblemStanding(
                self.problem.id,
            ));
        }
        self.problem.validate()?;
        self.normalized.validate(&self.problem)?;
        let inherited = ecology.probes().get(&self.normalized.probe.id).ok_or(
            ArithmeticMonodromyError::MissingPrimeProbe(self.normalized.probe.id),
        )?;
        if inherited.probe != self.normalized.probe || inherited.inherited_at != self.inherited_at {
            return Err(ArithmeticMonodromyError::MalformedProblemStanding(
                self.problem.id,
            ));
        }
        let mut expected = Self::new(self.problem.clone(), self.inherited_at)?;
        for ((_, probe), fiber) in ecology
            .fibers()
            .iter()
            .filter(|((_, probe), _)| *probe == self.normalized.probe.id)
        {
            if *probe != self.normalized.probe.id {
                return Err(ArithmeticMonodromyError::FiberProbeMismatch {
                    problem: self.problem.id,
                    probe: *probe,
                });
            }
            expected.receive(fiber)?;
        }
        if *self != expected {
            return Err(ArithmeticMonodromyError::MalformedProblemStanding(
                self.problem.id,
            ));
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArithmeticMonodromyStanding {
    pub schema: String,
    pub max_phase_grade: u32,
    pub max_horn_local_sections: u64,
    prime_ecology: PrimeEcologyStanding,
    problems: BTreeMap<QuinticProblemId, QuinticProblemStanding>,
    euler_receivers: BTreeMap<EulerReceiverId, ExactEulerReceiverStanding>,
    /// Production propagation incidence. Validation and inspection may scan standing; a new
    /// prime section reaches only the receivers already incident to its problem.
    receiver_incidence: BTreeMap<QuinticProblemId, BTreeSet<EulerReceiverId>>,
    used_events: BTreeSet<EventId>,
}

impl ArithmeticMonodromyStanding {
    pub fn new(max_phase_grade: u32) -> Result<Self, ArithmeticMonodromyError> {
        Self::with_horn_local_section_limit(max_phase_grade, DEFAULT_HORN_LOCAL_SECTION_LIMIT)
    }

    pub fn with_horn_local_section_limit(
        max_phase_grade: u32,
        max_horn_local_sections: u64,
    ) -> Result<Self, ArithmeticMonodromyError> {
        Ok(Self {
            schema: "holonic-engine.arithmetic-monodromy-standing.v1".to_owned(),
            max_phase_grade,
            max_horn_local_sections,
            prime_ecology: PrimeEcologyStanding::with_horn_local_section_limit(
                max_phase_grade,
                max_horn_local_sections,
            )?,
            problems: BTreeMap::new(),
            euler_receivers: BTreeMap::new(),
            receiver_incidence: BTreeMap::new(),
            used_events: BTreeSet::new(),
        })
    }

    pub fn prime_ecology(&self) -> &PrimeEcologyStanding {
        &self.prime_ecology
    }

    pub fn problems(&self) -> &BTreeMap<QuinticProblemId, QuinticProblemStanding> {
        &self.problems
    }

    pub fn euler_receivers(&self) -> &BTreeMap<EulerReceiverId, ExactEulerReceiverStanding> {
        &self.euler_receivers
    }

    pub fn geometry_receipt(&self) -> ArithmeticMonodromyGeometryReceipt {
        ArithmeticMonodromyGeometryReceipt {
            schema: "holonic-engine.arithmetic-monodromy-geometry-receipt.v1".to_owned(),
            prime_ecology: self.prime_ecology.geometry_receipt(),
            problems: self
                .problems
                .iter()
                .map(|(id, problem)| (*id, QuinticGeometryReceipt::from(problem)))
                .collect(),
            euler_receivers: self
                .euler_receivers
                .iter()
                .map(|(id, receiver)| (*id, EulerGeometryReceipt::from(receiver)))
                .collect(),
        }
    }

    pub fn atlas_receipt(
        &self,
        problem: QuinticProblemId,
    ) -> Result<ArithmeticMonodromyAtlasReceipt, ArithmeticMonodromyError> {
        self.validate()?;
        let standing = self
            .problems
            .get(&problem)
            .ok_or(ArithmeticMonodromyError::MissingProblem(problem))?;
        let prime_charts = standing
            .prime_sections
            .values()
            .map(|section| PrimeMonodromyChart {
                prime: section.prime,
                source_events: section.source_events.clone(),
                local_orbit_periods: section.cycle_type.clone(),
                euler_denominator: section.euler_denominator.clone(),
                polynomial_discriminant_place_open: section.cycle_type.is_none(),
            })
            .collect::<Vec<_>>();
        let transport_cells = standing
            .prime_sections
            .values()
            .map(|section| ArithmeticMonodromyTransportCell {
                problem,
                prime: section.prime,
                source_events: section.source_events.clone(),
                faces: BTreeSet::from([
                    ArithmeticMonodromyFace::CoefficientCover(problem),
                    ArithmeticMonodromyFace::PrimePlace(section.prime),
                    ArithmeticMonodromyFace::FrobeniusOrbit(section.prime),
                    ArithmeticMonodromyFace::EulerRecurrence(section.prime),
                ]),
                glued: section.cycle_type.is_some(),
            })
            .collect();
        Ok(ArithmeticMonodromyAtlasReceipt {
            schema: "holonic-engine.arithmetic-monodromy-atlas-receipt.v1".to_owned(),
            problem,
            inherited_coefficient_count: QUINTIC_DEGREE + 1,
            normalized_projective_free_rank: QUINTIC_DEGREE,
            root_scale: standing.normalized.root_scale.clone(),
            prime_charts,
            transport_cells,
            galois_fiber: standing.galois.clone(),
            cross_prime_root_sheet_gluing: CrossPrimeRootSheetGluing::OpenWithoutTransportWitness,
        })
    }

    pub fn validate(&self) -> Result<(), ArithmeticMonodromyError> {
        if self.schema != "holonic-engine.arithmetic-monodromy-standing.v1"
            || self.max_phase_grade == 0
            || self.max_horn_local_sections == 0
            || self.prime_ecology.max_phase_grade != self.max_phase_grade
            || self.prime_ecology.max_horn_local_sections != self.max_horn_local_sections
        {
            return Err(ArithmeticMonodromyError::MalformedStanding);
        }
        self.prime_ecology.validate()?;
        let expected_probe_ids = self
            .problems
            .keys()
            .map(|id| PolynomialProbeId(id.0))
            .collect::<BTreeSet<_>>();
        if self
            .prime_ecology
            .probes()
            .keys()
            .copied()
            .collect::<BTreeSet<_>>()
            != expected_probe_ids
        {
            return Err(ArithmeticMonodromyError::ProblemProbePopulationMismatch);
        }
        for problem in self.problems.values() {
            problem.validate(&self.prime_ecology)?;
        }
        for receiver in self.euler_receivers.values() {
            let problem = self
                .problems
                .get(&receiver.problem)
                .ok_or(ArithmeticMonodromyError::MissingProblem(receiver.problem))?;
            receiver.validate(problem)?;
        }
        let expected_receiver_incidence = self.euler_receivers.values().fold(
            BTreeMap::<QuinticProblemId, BTreeSet<EulerReceiverId>>::new(),
            |mut incidence, receiver| {
                incidence
                    .entry(receiver.problem)
                    .or_default()
                    .insert(receiver.id);
                incidence
            },
        );
        if self.receiver_incidence != expected_receiver_incidence {
            return Err(ArithmeticMonodromyError::ReceiverIncidenceMismatch);
        }
        let arithmetic_events = self
            .prime_ecology
            .arithmetic()
            .occurrences()
            .values()
            .map(|occurrence| occurrence.event);
        let problem_events = self.problems.values().map(|problem| problem.inherited_at);
        let receiver_events = self
            .euler_receivers
            .values()
            .map(|receiver| receiver.opened_at);
        let expected_events = arithmetic_events
            .chain(problem_events)
            .chain(receiver_events)
            .collect::<BTreeSet<_>>();
        if self.used_events != expected_events {
            return Err(ArithmeticMonodromyError::EventPopulationMismatch);
        }
        Ok(())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ArithmeticMonodromyEvent {
    AdmitInteger(ArithmeticFiberEvent),
    InheritQuintic {
        event: EventId,
        problem: IntegralQuinticProblem,
    },
    OpenEulerReceiver {
        event: EventId,
        id: EulerReceiverId,
        problem: QuinticProblemId,
        sigma: u32,
    },
}

impl ArithmeticMonodromyEvent {
    fn event_id(&self) -> EventId {
        match self {
            Self::AdmitInteger(event) => event.event,
            Self::InheritQuintic { event, .. } | Self::OpenEulerReceiver { event, .. } => *event,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GaloisTransportDelta {
    pub problem: QuinticProblemId,
    pub prime: u64,
    pub candidates_before: BTreeSet<QuinticTransitiveGroup>,
    pub candidates_after: BTreeSet<QuinticTransitiveGroup>,
    pub irreducibility_before: QuinticIrreducibility,
    pub irreducibility_after: QuinticIrreducibility,
    pub unique_group_after: Option<QuinticTransitiveGroup>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EulerTransportDelta {
    pub receiver: EulerReceiverId,
    pub problem: QuinticProblemId,
    pub prime: u64,
    pub admitted: bool,
    pub product_after: Rat,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArithmeticMonodromyRadiation {
    pub schema: String,
    pub event: EventId,
    pub prime_ecology: Option<PrimeEcologyRadiation>,
    pub inherited_problem: Option<QuinticProblemStanding>,
    pub transported_sections: Vec<QuinticPrimeSection>,
    pub galois_deltas: Vec<GaloisTransportDelta>,
    pub euler_deltas: Vec<EulerTransportDelta>,
    pub opened_receiver: Option<ExactEulerReceiverStanding>,
}

impl ArithmeticMonodromyRadiation {
    fn empty(event: EventId) -> Self {
        Self {
            schema: "holonic-engine.arithmetic-monodromy-radiation.v1".to_owned(),
            event,
            prime_ecology: None,
            inherited_problem: None,
            transported_sections: Vec::new(),
            galois_deltas: Vec::new(),
            euler_deltas: Vec::new(),
            opened_receiver: None,
        }
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ArithmeticMonodromyLaw {
    max_phase_grade: u32,
    max_horn_local_sections: u64,
}

impl ArithmeticMonodromyLaw {
    pub fn new(max_phase_grade: u32) -> Result<Self, ArithmeticMonodromyError> {
        Self::with_horn_local_section_limit(max_phase_grade, DEFAULT_HORN_LOCAL_SECTION_LIMIT)
    }

    pub fn with_horn_local_section_limit(
        max_phase_grade: u32,
        max_horn_local_sections: u64,
    ) -> Result<Self, ArithmeticMonodromyError> {
        // Let the owned production law validate the declaration.
        PrimeEcologyLaw::with_horn_local_section_limit(max_phase_grade, max_horn_local_sections)?;
        Ok(Self {
            max_phase_grade,
            max_horn_local_sections,
        })
    }

    fn prime_law(self) -> Result<PrimeEcologyLaw, PrimeEcologyError> {
        PrimeEcologyLaw::with_horn_local_section_limit(
            self.max_phase_grade,
            self.max_horn_local_sections,
        )
    }
}

impl ExactEventLaw for ArithmeticMonodromyLaw {
    type Standing = ArithmeticMonodromyStanding;
    type Event = ArithmeticMonodromyEvent;
    type Radiation = ArithmeticMonodromyRadiation;
    type Error = ArithmeticMonodromyError;

    fn enact(
        &self,
        standing_before: &Self::Standing,
        event: &Self::Event,
    ) -> Result<EventSuccessor<Self::Standing, Self::Radiation>, Self::Error> {
        standing_before.validate()?;
        if standing_before.max_phase_grade != self.max_phase_grade
            || standing_before.max_horn_local_sections != self.max_horn_local_sections
        {
            return Err(ArithmeticMonodromyError::LawStandingMismatch);
        }
        let event_id = event.event_id();
        if standing_before.used_events.contains(&event_id) {
            return Err(ArithmeticMonodromyError::RepeatedEvent(event_id));
        }
        let mut standing_after = standing_before.clone();
        let mut radiation = ArithmeticMonodromyRadiation::empty(event_id);

        match event {
            ArithmeticMonodromyEvent::AdmitInteger(arithmetic_event) => {
                let successor = self.prime_law()?.enact(
                    &standing_after.prime_ecology,
                    &PrimeEcologyEvent::AdmitInteger(arithmetic_event.clone()),
                )?;
                let prime_radiation = successor
                    .radiation
                    .into_iter()
                    .next()
                    .ok_or(ArithmeticMonodromyError::MissingPrimeRadiation)?;
                standing_after.prime_ecology = successor.standing_after;
                transport_emitted_fibers(
                    &mut standing_after,
                    &prime_radiation.enacted_fibers,
                    &mut radiation,
                )?;
                radiation.prime_ecology = Some(prime_radiation);
            }
            ArithmeticMonodromyEvent::InheritQuintic { event, problem } => {
                problem.validate()?;
                if standing_after.problems.contains_key(&problem.id) {
                    return Err(ArithmeticMonodromyError::RepeatedProblem(problem.id));
                }
                let mut problem_standing = QuinticProblemStanding::new(problem.clone(), *event)?;
                let successor = self.prime_law()?.enact(
                    &standing_after.prime_ecology,
                    &PrimeEcologyEvent::InheritPolynomial {
                        event: *event,
                        probe: problem_standing.normalized.probe.clone(),
                    },
                )?;
                let prime_radiation = successor
                    .radiation
                    .into_iter()
                    .next()
                    .ok_or(ArithmeticMonodromyError::MissingPrimeRadiation)?;
                standing_after.prime_ecology = successor.standing_after;
                for fiber in &prime_radiation.enacted_fibers {
                    let (section, delta) = problem_standing.receive(fiber)?;
                    radiation.transported_sections.push(section);
                    radiation.galois_deltas.push(delta);
                }
                radiation.inherited_problem = Some(problem_standing.clone());
                standing_after.problems.insert(problem.id, problem_standing);
                // No receiver for a not-yet-present problem could lawfully exist.
                radiation.prime_ecology = Some(prime_radiation);
            }
            ArithmeticMonodromyEvent::OpenEulerReceiver {
                event,
                id,
                problem,
                sigma,
            } => {
                if standing_after.euler_receivers.contains_key(id) {
                    return Err(ArithmeticMonodromyError::RepeatedEulerReceiver(*id));
                }
                let problem_standing = standing_after
                    .problems
                    .get(problem)
                    .ok_or(ArithmeticMonodromyError::MissingProblem(*problem))?;
                let mut receiver = ExactEulerReceiverStanding::new(*id, *problem, *sigma, *event)?;
                for section in problem_standing.prime_sections.values() {
                    radiation.euler_deltas.push(receiver.receive(section)?);
                }
                radiation.opened_receiver = Some(receiver.clone());
                standing_after.euler_receivers.insert(*id, receiver);
                standing_after
                    .receiver_incidence
                    .entry(*problem)
                    .or_default()
                    .insert(*id);
            }
        }

        standing_after.used_events.insert(event_id);
        standing_after.validate()?;
        Ok(EventSuccessor {
            standing_after,
            radiation: vec![radiation],
            logical_resources: None,
            physical_resources: None,
        })
    }
}

fn transport_emitted_fibers(
    standing: &mut ArithmeticMonodromyStanding,
    fibers: &[PolynomialPrimeFiber],
    radiation: &mut ArithmeticMonodromyRadiation,
) -> Result<(), ArithmeticMonodromyError> {
    for fiber in fibers {
        let problem_id = QuinticProblemId(fiber.probe.0);
        let problem = standing
            .problems
            .get_mut(&problem_id)
            .ok_or(ArithmeticMonodromyError::MissingProblem(problem_id))?;
        let (section, galois_delta) = problem.receive(fiber)?;
        let incident_receivers = standing
            .receiver_incidence
            .get(&problem_id)
            .cloned()
            .unwrap_or_default();
        for receiver_id in incident_receivers {
            let receiver = standing
                .euler_receivers
                .get_mut(&receiver_id)
                .ok_or(ArithmeticMonodromyError::ReceiverIncidenceMismatch)?;
            radiation.euler_deltas.push(receiver.receive(&section)?);
        }
        radiation.transported_sections.push(section);
        radiation.galois_deltas.push(galois_delta);
    }
    Ok(())
}

fn derive_prime_section(
    problem: QuinticProblemId,
    fiber: &PolynomialPrimeFiber,
) -> Result<QuinticPrimeSection, ArithmeticMonodromyError> {
    fiber.validate()?;
    if fiber.signature.degree
        != u32::try_from(QUINTIC_DEGREE).map_err(|_| ArithmeticMonodromyError::CarrierOverflow)?
    {
        return Err(ArithmeticMonodromyError::NonQuinticFiber {
            problem,
            prime: fiber.prime,
            degree: fiber.signature.degree,
        });
    }
    if fiber.lineage.kind != CausalMaterialKind::Enacted {
        return Err(ArithmeticMonodromyError::UncausedPrimeFiber {
            problem,
            prime: fiber.prime,
        });
    }
    let cycle_type = fiber
        .signature
        .separable
        .then(|| {
            let mut cycles = Vec::new();
            for factor in &fiber.factors {
                if factor.multiplicity != 1 {
                    return Err(ArithmeticMonodromyError::RepeatedFactorAtSeparablePlace {
                        problem,
                        prime: fiber.prime,
                    });
                }
                let degree = u32::try_from(
                    factor
                        .polynomial
                        .degree()
                        .ok_or(ArithmeticMonodromyError::CarrierOverflow)?,
                )
                .map_err(|_| ArithmeticMonodromyError::CarrierOverflow)?;
                cycles.push(degree);
            }
            cycles.sort_unstable();
            let total = cycles.iter().try_fold(0_u32, |sum, degree| {
                sum.checked_add(*degree)
                    .ok_or(ArithmeticMonodromyError::CarrierOverflow)
            })?;
            if total != QUINTIC_DEGREE as u32 {
                return Err(ArithmeticMonodromyError::InvalidCycleType {
                    prime: fiber.prime,
                    cycle_type: cycles,
                });
            }
            Ok(cycles)
        })
        .transpose()?;
    let frobenius_order = cycle_type
        .as_ref()
        .map(|cycles| {
            cycles
                .iter()
                .copied()
                .try_fold(1_u32, checked_least_common_multiple)
        })
        .transpose()?;
    let permutation_is_even = cycle_type.as_ref().map(|cycles| {
        (QUINTIC_DEGREE as u32 - u32::try_from(cycles.len()).expect("five cycles fit in u32"))
            .is_multiple_of(2)
    });
    let euler_denominator = cycle_type
        .as_ref()
        .map(|cycles| formal_euler_denominator(cycles))
        .transpose()?;
    Ok(QuinticPrimeSection {
        schema: "holonic-engine.quintic-prime-section.v1".to_owned(),
        problem,
        probe: fiber.probe,
        prime: fiber.prime,
        source_events: fiber.lineage.source_events.clone(),
        signature: fiber.signature.clone(),
        cycle_type,
        frobenius_order,
        permutation_is_even,
        euler_denominator,
    })
}

fn initial_galois_fiber(
    normalized: &NormalizedQuintic,
) -> Result<QuinticGaloisFiber, ArithmeticMonodromyError> {
    let catalogue = quintic_group_catalogue()?;
    let transitive_candidates = if normalized.discriminant.is_zero() {
        BTreeSet::new()
    } else {
        let square = normalized.discriminant_square_root.is_some();
        catalogue
            .iter()
            .filter_map(|(group, entry)| (entry.all_even == square).then_some(*group))
            .collect()
    };
    Ok(QuinticGaloisFiber {
        schema: "holonic-engine.quintic-galois-fiber.v1".to_owned(),
        discriminant: normalized.discriminant.clone(),
        discriminant_square_root: normalized.discriminant_square_root.clone(),
        irreducibility: QuinticIrreducibility::Open,
        cycle_witnesses: BTreeMap::new(),
        transitive_candidates,
    })
}

fn transport_section_into_galois(
    galois: &mut QuinticGaloisFiber,
    section: &QuinticPrimeSection,
) -> Result<(), ArithmeticMonodromyError> {
    let Some(cycle_type) = &section.cycle_type else {
        return Ok(());
    };
    galois
        .cycle_witnesses
        .entry(cycle_type.clone())
        .or_default()
        .insert(section.prime);
    if cycle_type == &[QUINTIC_DEGREE as u32]
        && matches!(galois.irreducibility, QuinticIrreducibility::Open)
    {
        galois.irreducibility = QuinticIrreducibility::CertifiedByPrime {
            prime: section.prime,
            source_events: section.source_events.clone(),
        };
    }
    let catalogue = quintic_group_catalogue()?;
    galois
        .transitive_candidates
        .retain(|group| catalogue[group].cycle_types.contains(cycle_type));
    if matches!(
        galois.irreducibility,
        QuinticIrreducibility::CertifiedByPrime { .. }
    ) && galois.transitive_candidates.is_empty()
    {
        return Err(ArithmeticMonodromyError::TransitiveCatalogueContradiction);
    }
    Ok(())
}

fn formal_euler_denominator(cycle_type: &[u32]) -> Result<Vec<BigInt>, ArithmeticMonodromyError> {
    let mut result = vec![BigInt::one()];
    for degree in cycle_type {
        if *degree == 0 {
            return Err(ArithmeticMonodromyError::InvalidCycleType {
                prime: 0,
                cycle_type: cycle_type.to_vec(),
            });
        }
        let degree =
            usize::try_from(*degree).map_err(|_| ArithmeticMonodromyError::CarrierOverflow)?;
        let mut factor = vec![BigInt::zero(); degree + 1];
        factor[0] = BigInt::one();
        factor[degree] = -BigInt::one();
        result = multiply_integer_polynomials(&result, &factor);
    }
    if result.len() != QUINTIC_DEGREE + 1 || result[0] != BigInt::one() {
        return Err(ArithmeticMonodromyError::MalformedEulerDenominator);
    }
    Ok(result)
}

fn evaluate_euler_local_factor(
    prime: u64,
    sigma: u32,
    cycle_type: &[u32],
) -> Result<Rat, ArithmeticMonodromyError> {
    if prime < 2 || sigma <= 1 {
        return Err(ArithmeticMonodromyError::InvalidEulerEvaluation { prime, sigma });
    }
    let mut result = Rat::one();
    for degree in cycle_type {
        let exponent = sigma
            .checked_mul(*degree)
            .ok_or(ArithmeticMonodromyError::CarrierOverflow)?;
        let power = BigInt::from(prime).pow(exponent);
        result *= Rat::new(power.clone(), power - BigInt::one());
    }
    Ok(result)
}

fn multiply_integer_polynomials(left: &[BigInt], right: &[BigInt]) -> Vec<BigInt> {
    let mut product = vec![BigInt::zero(); left.len() + right.len() - 1];
    for (left_degree, left_coefficient) in left.iter().enumerate() {
        for (right_degree, right_coefficient) in right.iter().enumerate() {
            product[left_degree + right_degree] += left_coefficient * right_coefficient;
        }
    }
    while product.len() > 1 && product.last().is_some_and(Zero::is_zero) {
        product.pop();
    }
    product
}

fn checked_least_common_multiple(left: u32, right: u32) -> Result<u32, ArithmeticMonodromyError> {
    let divisor = greatest_common_divisor_u32(left, right);
    left.checked_div(divisor)
        .and_then(|reduced| reduced.checked_mul(right))
        .ok_or(ArithmeticMonodromyError::CarrierOverflow)
}

fn greatest_common_divisor_u32(mut left: u32, mut right: u32) -> u32 {
    while right != 0 {
        let remainder = left % right;
        left = right;
        right = remainder;
    }
    left
}

type Permutation5 = [u8; QUINTIC_DEGREE];

#[derive(Clone, Debug)]
struct QuinticGroupCatalogueEntry {
    cycle_types: BTreeSet<Vec<u32>>,
    all_even: bool,
}

fn quintic_group_catalogue()
-> Result<BTreeMap<QuinticTransitiveGroup, QuinticGroupCatalogueEntry>, ArithmeticMonodromyError> {
    let rotation = [1, 2, 3, 4, 0];
    let reflection = [0, 4, 3, 2, 1];
    let dilation_two = [0, 2, 4, 1, 3];
    let three_cycle = [1, 2, 0, 3, 4];
    let transposition = [1, 0, 2, 3, 4];
    let generators = BTreeMap::from([
        (QuinticTransitiveGroup::Cyclic5, vec![rotation]),
        (
            QuinticTransitiveGroup::Dihedral5,
            vec![rotation, reflection],
        ),
        (
            QuinticTransitiveGroup::Frobenius20,
            vec![rotation, dilation_two],
        ),
        (
            QuinticTransitiveGroup::Alternating5,
            vec![rotation, three_cycle],
        ),
        (
            QuinticTransitiveGroup::Symmetric5,
            vec![rotation, transposition],
        ),
    ]);
    let mut catalogue = BTreeMap::new();
    for (group, generators) in generators {
        let elements = generated_permutation_group(&generators)?;
        if elements.len()
            != usize::try_from(group.order())
                .map_err(|_| ArithmeticMonodromyError::CarrierOverflow)?
        {
            return Err(ArithmeticMonodromyError::InvalidGroupCatalogue(group));
        }
        let cycle_types = elements.iter().map(permutation_cycle_type).collect();
        let all_even = elements.iter().all(permutation_is_even);
        catalogue.insert(
            group,
            QuinticGroupCatalogueEntry {
                cycle_types,
                all_even,
            },
        );
    }
    Ok(catalogue)
}

fn generated_permutation_group(
    generators: &[Permutation5],
) -> Result<BTreeSet<Permutation5>, ArithmeticMonodromyError> {
    for generator in generators {
        validate_permutation(generator)?;
    }
    let identity = [0, 1, 2, 3, 4];
    let mut elements = BTreeSet::from([identity]);
    let mut frontier = VecDeque::from([identity]);
    while let Some(current) = frontier.pop_front() {
        for generator in generators {
            let next = compose_permutations(&current, generator);
            if elements.insert(next) {
                if elements.len() > 120 {
                    return Err(ArithmeticMonodromyError::InvalidPermutationGroup);
                }
                frontier.push_back(next);
            }
        }
    }
    Ok(elements)
}

fn validate_permutation(permutation: &Permutation5) -> Result<(), ArithmeticMonodromyError> {
    if permutation.iter().copied().collect::<BTreeSet<_>>() != BTreeSet::from([0, 1, 2, 3, 4]) {
        return Err(ArithmeticMonodromyError::InvalidPermutationGroup);
    }
    Ok(())
}

fn compose_permutations(left: &Permutation5, right: &Permutation5) -> Permutation5 {
    let mut result = [0_u8; QUINTIC_DEGREE];
    for index in 0..QUINTIC_DEGREE {
        result[index] = left[usize::from(right[index])];
    }
    result
}

fn permutation_cycle_type(permutation: &Permutation5) -> Vec<u32> {
    let mut visited = [false; QUINTIC_DEGREE];
    let mut cycles = Vec::new();
    for start in 0..QUINTIC_DEGREE {
        if visited[start] {
            continue;
        }
        let mut cursor = start;
        let mut length = 0_u32;
        while !visited[cursor] {
            visited[cursor] = true;
            cursor = usize::from(permutation[cursor]);
            length += 1;
        }
        cycles.push(length);
    }
    cycles.sort_unstable();
    cycles
}

fn permutation_is_even(permutation: &Permutation5) -> bool {
    let cycles = permutation_cycle_type(permutation);
    (QUINTIC_DEGREE as u32 - cycles.len() as u32).is_multiple_of(2)
}

fn monic_polynomial_discriminant(
    coefficients: &[BigInt],
) -> Result<BigInt, ArithmeticMonodromyError> {
    if coefficients.len() < 2 || coefficients.last() != Some(&BigInt::one()) {
        return Err(ArithmeticMonodromyError::MalformedDiscriminantPolynomial);
    }
    let degree = coefficients.len() - 1;
    let derivative = coefficients
        .iter()
        .enumerate()
        .skip(1)
        .map(|(power, coefficient)| coefficient * BigInt::from(power))
        .collect::<Vec<_>>();
    let resultant = polynomial_resultant(coefficients, &derivative)?;
    let triangular = degree
        .checked_mul(degree - 1)
        .and_then(|value| value.checked_div(2))
        .ok_or(ArithmeticMonodromyError::CarrierOverflow)?;
    Ok(if triangular.is_multiple_of(2) {
        resultant
    } else {
        -resultant
    })
}

fn polynomial_resultant(
    left_low_first: &[BigInt],
    right_low_first: &[BigInt],
) -> Result<BigInt, ArithmeticMonodromyError> {
    let left_degree = left_low_first
        .len()
        .checked_sub(1)
        .ok_or(ArithmeticMonodromyError::MalformedDiscriminantPolynomial)?;
    let right_degree = right_low_first
        .len()
        .checked_sub(1)
        .ok_or(ArithmeticMonodromyError::MalformedDiscriminantPolynomial)?;
    if left_low_first.last().is_none_or(Zero::is_zero)
        || right_low_first.last().is_none_or(Zero::is_zero)
    {
        return Err(ArithmeticMonodromyError::MalformedDiscriminantPolynomial);
    }
    let size = left_degree
        .checked_add(right_degree)
        .ok_or(ArithmeticMonodromyError::CarrierOverflow)?;
    let left_high_first = left_low_first.iter().rev().cloned().collect::<Vec<_>>();
    let right_high_first = right_low_first.iter().rev().cloned().collect::<Vec<_>>();
    let mut sylvester = vec![vec![BigInt::zero(); size]; size];
    for row in 0..right_degree {
        for (offset, coefficient) in left_high_first.iter().enumerate() {
            sylvester[row][row + offset] = coefficient.clone();
        }
    }
    for row in 0..left_degree {
        for (offset, coefficient) in right_high_first.iter().enumerate() {
            sylvester[right_degree + row][row + offset] = coefficient.clone();
        }
    }
    bareiss_determinant(sylvester)
}

fn bareiss_determinant(mut matrix: Vec<Vec<BigInt>>) -> Result<BigInt, ArithmeticMonodromyError> {
    let size = matrix.len();
    if size == 0 || matrix.iter().any(|row| row.len() != size) {
        return Err(ArithmeticMonodromyError::MalformedDeterminant);
    }
    if size == 1 {
        return Ok(matrix[0][0].clone());
    }
    let mut previous_pivot = BigInt::one();
    let mut sign = BigInt::one();
    for pivot_index in 0..size - 1 {
        let pivot_row = (pivot_index..size).find(|row| !matrix[*row][pivot_index].is_zero());
        let Some(pivot_row) = pivot_row else {
            return Ok(BigInt::zero());
        };
        if pivot_row != pivot_index {
            matrix.swap(pivot_row, pivot_index);
            sign = -sign;
        }
        let pivot = matrix[pivot_index][pivot_index].clone();
        for row in pivot_index + 1..size {
            for column in pivot_index + 1..size {
                let numerator = &matrix[row][column] * &pivot
                    - &matrix[row][pivot_index] * &matrix[pivot_index][column];
                let quotient = &numerator / &previous_pivot;
                if &quotient * &previous_pivot != numerator {
                    return Err(ArithmeticMonodromyError::NonExactBareissDivision);
                }
                matrix[row][column] = quotient;
            }
            matrix[row][pivot_index] = BigInt::zero();
        }
        previous_pivot = pivot;
    }
    Ok(sign * matrix[size - 1][size - 1].clone())
}

fn rational_integer_square_root(value: &BigInt) -> Option<BigInt> {
    if value.is_negative() {
        return None;
    }
    let root = floor_integer_square_root(value);
    (&root * &root == *value).then_some(root)
}

fn floor_integer_square_root(value: &BigInt) -> BigInt {
    debug_assert!(!value.is_negative());
    if value <= &BigInt::one() {
        return value.clone();
    }
    let mut estimate = value.clone();
    loop {
        let next = (&estimate + value / &estimate) / 2;
        if next >= estimate {
            return estimate;
        }
        estimate = next;
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QuinticGeometryReceipt {
    pub normalized_coefficients: Vec<BigInt>,
    pub discriminant: BigInt,
    pub discriminant_square_root: Option<BigInt>,
    pub prime_cycle_types: BTreeMap<u64, Option<Vec<u32>>>,
    pub prime_euler_denominators: BTreeMap<u64, Option<Vec<BigInt>>>,
    pub irreducibility: QuinticIrreducibility,
    pub transitive_candidates: BTreeSet<QuinticTransitiveGroup>,
}

impl From<&QuinticProblemStanding> for QuinticGeometryReceipt {
    fn from(problem: &QuinticProblemStanding) -> Self {
        Self {
            normalized_coefficients: problem.normalized.coefficients.clone(),
            discriminant: problem.normalized.discriminant.clone(),
            discriminant_square_root: problem.normalized.discriminant_square_root.clone(),
            prime_cycle_types: problem
                .prime_sections
                .iter()
                .map(|(prime, section)| (*prime, section.cycle_type.clone()))
                .collect(),
            prime_euler_denominators: problem
                .prime_sections
                .iter()
                .map(|(prime, section)| (*prime, section.euler_denominator.clone()))
                .collect(),
            irreducibility: problem.galois.irreducibility.clone(),
            transitive_candidates: problem.galois.transitive_candidates.clone(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct EulerGeometryReceipt {
    pub problem: QuinticProblemId,
    pub sigma: u32,
    pub local_cycle_types: BTreeMap<u64, Vec<u32>>,
    pub open_places: BTreeSet<u64>,
    pub exact_product: Rat,
}

impl From<&ExactEulerReceiverStanding> for EulerGeometryReceipt {
    fn from(receiver: &ExactEulerReceiverStanding) -> Self {
        Self {
            problem: receiver.problem,
            sigma: receiver.sigma,
            local_cycle_types: receiver
                .local_sections
                .iter()
                .map(|(prime, section)| (*prime, section.cycle_type.clone()))
                .collect(),
            open_places: receiver.open_places.keys().copied().collect(),
            exact_product: receiver.exact_product.clone(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArithmeticMonodromyGeometryReceipt {
    pub schema: String,
    pub prime_ecology: PrimeEcologyGeometryReceipt,
    pub problems: BTreeMap<QuinticProblemId, QuinticGeometryReceipt>,
    pub euler_receivers: BTreeMap<EulerReceiverId, EulerGeometryReceipt>,
}

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub enum ArithmeticMonodromyFace {
    CoefficientCover(QuinticProblemId),
    PrimePlace(u64),
    FrobeniusOrbit(u64),
    EulerRecurrence(u64),
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArithmeticMonodromyTransportCell {
    pub problem: QuinticProblemId,
    pub prime: u64,
    pub source_events: BTreeSet<EventId>,
    pub faces: BTreeSet<ArithmeticMonodromyFace>,
    pub glued: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PrimeMonodromyChart {
    pub prime: u64,
    pub source_events: BTreeSet<EventId>,
    /// One receiver-local Frobenius loop period per irreducible factor.
    pub local_orbit_periods: Option<Vec<u32>>,
    pub euler_denominator: Option<Vec<BigInt>>,
    pub polynomial_discriminant_place_open: bool,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum CrossPrimeRootSheetGluing {
    /// Factor degrees alone do not canonically label one prime's residue roots as another
    /// prime's residue roots or as complex roots.
    OpenWithoutTransportWitness,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ArithmeticMonodromyAtlasReceipt {
    pub schema: String,
    pub problem: QuinticProblemId,
    pub inherited_coefficient_count: usize,
    pub normalized_projective_free_rank: usize,
    pub root_scale: BigInt,
    pub prime_charts: Vec<PrimeMonodromyChart>,
    pub transport_cells: Vec<ArithmeticMonodromyTransportCell>,
    pub galois_fiber: QuinticGaloisFiber,
    pub cross_prime_root_sheet_gluing: CrossPrimeRootSheetGluing,
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum ArithmeticMonodromyError {
    #[error(transparent)]
    PrimeEcology(#[from] PrimeEcologyError),
    #[error("integral quintic {0:?} is malformed")]
    MalformedQuintic(QuinticProblemId),
    #[error("normalization of quintic {0:?} is malformed")]
    MalformedNormalization(QuinticProblemId),
    #[error("quintic problem standing {0:?} is malformed")]
    MalformedProblemStanding(QuinticProblemId),
    #[error("arithmetic-monodromy standing is malformed")]
    MalformedStanding,
    #[error("the law and standing declarations differ")]
    LawStandingMismatch,
    #[error("event {0:?} has already crossed this arithmetic-monodromy world")]
    RepeatedEvent(EventId),
    #[error("quintic problem {0:?} is already present")]
    RepeatedProblem(QuinticProblemId),
    #[error("quintic problem {0:?} is absent")]
    MissingProblem(QuinticProblemId),
    #[error("Euler receiver {0:?} is already present")]
    RepeatedEulerReceiver(EulerReceiverId),
    #[error("Euler receiver {0:?} is malformed")]
    MalformedEulerReceiver(EulerReceiverId),
    #[error("Euler sigma must be an integer greater than one, received {0}")]
    InvalidEulerSigma(u32),
    #[error("Euler evaluation is invalid at prime {prime}, sigma {sigma}")]
    InvalidEulerEvaluation { prime: u64, sigma: u32 },
    #[error("Euler receiver {receiver:?} cannot receive problem {problem:?}")]
    ReceiverProblemMismatch {
        receiver: EulerReceiverId,
        problem: QuinticProblemId,
    },
    #[error("Euler receiver {receiver:?} already received prime {prime}")]
    RepeatedPrimeTransport {
        receiver: EulerReceiverId,
        prime: u64,
    },
    #[error("problem {problem:?} already received prime section {prime}")]
    RepeatedPrimeSection {
        problem: QuinticProblemId,
        prime: u64,
    },
    #[error("problem {problem:?} cannot receive probe {probe:?}")]
    FiberProbeMismatch {
        problem: QuinticProblemId,
        probe: PolynomialProbeId,
    },
    #[error("prime probe {0:?} is absent from the underlying ecology")]
    MissingPrimeProbe(PolynomialProbeId),
    #[error("the problem/probe populations differ")]
    ProblemProbePopulationMismatch,
    #[error("the event population differs from the retained standing")]
    EventPopulationMismatch,
    #[error("the problem-to-receiver propagation incidence differs from standing")]
    ReceiverIncidenceMismatch,
    #[error("prime ecology emitted no radiation")]
    MissingPrimeRadiation,
    #[error("problem {problem:?} received a degree-{degree} fiber at prime {prime}")]
    NonQuinticFiber {
        problem: QuinticProblemId,
        prime: u64,
        degree: u32,
    },
    #[error("problem {problem:?} received an uncaused fiber at prime {prime}")]
    UncausedPrimeFiber {
        problem: QuinticProblemId,
        prime: u64,
    },
    #[error("problem {problem:?} reports a repeated factor at separable prime {prime}")]
    RepeatedFactorAtSeparablePlace {
        problem: QuinticProblemId,
        prime: u64,
    },
    #[error("invalid Frobenius cycle type {cycle_type:?} at prime {prime}")]
    InvalidCycleType { prime: u64, cycle_type: Vec<u32> },
    #[error("the formal Euler denominator is malformed")]
    MalformedEulerDenominator,
    #[error("the exact transitive quintic catalogue contradicts a certified irreducible fiber")]
    TransitiveCatalogueContradiction,
    #[error("the permutation catalogue for {0:?} is invalid")]
    InvalidGroupCatalogue(QuinticTransitiveGroup),
    #[error("a permutation group carrier is invalid")]
    InvalidPermutationGroup,
    #[error("the discriminant polynomial is malformed")]
    MalformedDiscriminantPolynomial,
    #[error("the determinant carrier is malformed")]
    MalformedDeterminant,
    #[error("Bareiss elimination encountered a non-exact division")]
    NonExactBareissDivision,
    #[error("an exact carrier overflowed its declared machine index")]
    CarrierOverflow,
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::CausalWorld;

    const PROBLEM_EVENT: EventId = EventId(1_000_000);
    const RECEIVER_EVENT: EventId = EventId(2_000_000);
    const PROBLEM: QuinticProblemId = QuinticProblemId(17);
    const RECEIVER: EulerReceiverId = EulerReceiverId(23);

    fn a5_problem() -> IntegralQuinticProblem {
        // Twice x^5 - x^4 - 11x^3 + x^2 + 12x - 4. The scalar presentation
        // deliberately exercises the nonmonic exact root-scale path.
        IntegralQuinticProblem::new(
            PROBLEM,
            "scaled-totally-real-A5",
            [-8_i64, 24, 2, -22, -2, 2]
                .into_iter()
                .map(BigInt::from)
                .collect(),
        )
        .unwrap()
    }

    fn admit_through(
        world: &mut CausalWorld<ArithmeticMonodromyLaw>,
        through: u64,
    ) -> Result<(), ArithmeticMonodromyError> {
        for value in 2..=through {
            world.receive(&ArithmeticMonodromyEvent::AdmitInteger(
                ArithmeticFiberEvent {
                    event: EventId(value),
                    value,
                },
            ))?;
        }
        Ok(())
    }

    #[test]
    fn quintic_group_catalogue_has_exact_orders_and_expected_parity() {
        let catalogue = quintic_group_catalogue().unwrap();
        assert_eq!(catalogue.len(), 5);
        assert!(catalogue[&QuinticTransitiveGroup::Cyclic5].all_even);
        assert!(catalogue[&QuinticTransitiveGroup::Dihedral5].all_even);
        assert!(!catalogue[&QuinticTransitiveGroup::Frobenius20].all_even);
        assert!(catalogue[&QuinticTransitiveGroup::Alternating5].all_even);
        assert!(!catalogue[&QuinticTransitiveGroup::Symmetric5].all_even);
    }

    #[test]
    fn exact_normalization_preserves_a_general_integral_quintic_root_scale() {
        let problem = IntegralQuinticProblem::new(
            QuinticProblemId(1),
            "general",
            [3_i64, -5, 7, 11, -13, -2]
                .into_iter()
                .map(BigInt::from)
                .collect(),
        )
        .unwrap();
        let normalized = problem.normalize().unwrap();
        assert_eq!(normalized.root_scale, BigInt::from(-2));
        assert_eq!(normalized.coefficients.last(), Some(&BigInt::one()));
        // g(a_5 x) = a_5^4 f(x), checked at several exact integer receivers.
        for x in -3_i64..=3 {
            let x = BigInt::from(x);
            let y = &normalized.root_scale * &x;
            let left = evaluate_integer_polynomial(&normalized.coefficients, &y);
            let right = normalized.root_scale.pow(4)
                * evaluate_integer_polynomial(&problem.coefficients, &x);
            assert_eq!(left, right);
        }
    }

    #[test]
    fn a5_fibers_drive_the_same_galois_and_euler_standing_across_chronologies() {
        let law = ArithmeticMonodromyLaw::new(1).unwrap();
        let standing = ArithmeticMonodromyStanding::new(1).unwrap();
        let mut early = CausalWorld::new(law, standing);
        early
            .receive(&ArithmeticMonodromyEvent::InheritQuintic {
                event: PROBLEM_EVENT,
                problem: a5_problem(),
            })
            .unwrap();
        early
            .receive(&ArithmeticMonodromyEvent::OpenEulerReceiver {
                event: RECEIVER_EVENT,
                id: RECEIVER,
                problem: PROBLEM,
                sigma: 2,
            })
            .unwrap();
        admit_through(&mut early, 61).unwrap();

        let law = ArithmeticMonodromyLaw::new(1).unwrap();
        let standing = ArithmeticMonodromyStanding::new(1).unwrap();
        let mut late = CausalWorld::new(law, standing);
        admit_through(&mut late, 61).unwrap();
        late.receive(&ArithmeticMonodromyEvent::InheritQuintic {
            event: PROBLEM_EVENT,
            problem: a5_problem(),
        })
        .unwrap();
        late.receive(&ArithmeticMonodromyEvent::OpenEulerReceiver {
            event: RECEIVER_EVENT,
            id: RECEIVER,
            problem: PROBLEM,
            sigma: 2,
        })
        .unwrap();

        early.standing().validate().unwrap();
        late.standing().validate().unwrap();
        assert_eq!(
            early.standing().geometry_receipt(),
            late.standing().geometry_receipt()
        );
        let problem = &early.standing().problems()[&PROBLEM];
        assert_eq!(
            problem.galois.unique_certified_group(),
            Some(QuinticTransitiveGroup::Alternating5)
        );
        assert!(problem.normalized.discriminant_square_root.is_some());
        let receiver = &early.standing().euler_receivers()[&RECEIVER];
        assert!(!receiver.local_sections.is_empty());
        assert!(receiver.exact_product > Rat::one());
    }

    #[test]
    fn certified_a5_future_cycle_fiber_rejects_every_odd_partition() {
        let law = ArithmeticMonodromyLaw::new(1).unwrap();
        let standing = ArithmeticMonodromyStanding::new(1).unwrap();
        let mut world = CausalWorld::new(law, standing);
        world
            .receive(&ArithmeticMonodromyEvent::InheritQuintic {
                event: PROBLEM_EVENT,
                problem: a5_problem(),
            })
            .unwrap();
        admit_through(&mut world, 61).unwrap();
        let galois = &world.standing().problems()[&PROBLEM].galois;
        assert_eq!(
            galois.unique_certified_group(),
            Some(QuinticTransitiveGroup::Alternating5)
        );
        let admitted = galois.admitted_future_cycle_types().unwrap();
        assert!(admitted.contains(&vec![5]));
        assert!(admitted.contains(&vec![1, 1, 3]));
        assert!(admitted.contains(&vec![1, 2, 2]));
        assert!(!admitted.contains(&vec![2, 3]));
        assert!(!admitted.contains(&vec![1, 4]));
    }

    #[test]
    fn nonsquare_control_closes_as_s5_from_caused_prime_sections() {
        let law = ArithmeticMonodromyLaw::new(1).unwrap();
        let standing = ArithmeticMonodromyStanding::new(1).unwrap();
        let mut world = CausalWorld::new(law, standing);
        let problem = IntegralQuinticProblem::new(
            PROBLEM,
            "x5-x-1",
            [-1_i64, -1, 0, 0, 0, 1]
                .into_iter()
                .map(BigInt::from)
                .collect(),
        )
        .unwrap();
        world
            .receive(&ArithmeticMonodromyEvent::InheritQuintic {
                event: PROBLEM_EVENT,
                problem,
            })
            .unwrap();
        admit_through(&mut world, 31).unwrap();
        let problem = &world.standing().problems()[&PROBLEM];
        assert_eq!(problem.normalized.discriminant, BigInt::from(2869));
        assert_eq!(problem.normalized.discriminant_square_root, None);
        assert_eq!(
            problem.galois.unique_certified_group(),
            Some(QuinticTransitiveGroup::Symmetric5)
        );
        assert_eq!(problem.prime_sections[&19].cycle_type, None);
    }

    fn evaluate_integer_polynomial(coefficients: &[BigInt], x: &BigInt) -> BigInt {
        coefficients
            .iter()
            .rev()
            .fold(BigInt::zero(), |value, coefficient| value * x + coefficient)
    }
}
