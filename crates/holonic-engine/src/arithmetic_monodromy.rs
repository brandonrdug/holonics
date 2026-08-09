//! Exact transport from an integral polynomial through prime-place monodromy and Euler receivers.
//!
//! This is one production mathematical world, not a Galois-group lookup table or a rendered
//! polynomial fixture. An inherited integral polynomial **of any degree at least two** is changed
//! by an exact rational root-scale into the monic integer probe accepted by
//! [`crate::PrimeEcologyLaw`]. Every subsequently founded prime receives that same probe. The
//! emitted finite-field factorization is transported, without re-factorization here, into:
//!
//! - an unramified Frobenius cycle section;
//! - the exact **constraint population** the observed sections leave on the Galois group;
//! - a formal permutation-Euler denominator; and
//! - every already-open exact integer-sigma Euler receiver.
//!
//! ## The degree is a rung, not a category
//!
//! Until 2026-08-09 this module carried `const QUINTIC_DEGREE: usize = 5` and refused any
//! polynomial whose coefficient count was not six. `canon/THE_CONTAMINANT_PROTOCOL.md` §2.6 names
//! that species — **a restriction the organ imposes presented as a fact about the subject** — and
//! records why it is not hygiene: `solvable_by_radicals` refusing at degree five is meaningful only
//! against the degrees where it does *not* refuse, so an organ that only ever sees degree five
//! cannot state its own theorem.
//!
//! ## What replaced the catalogue
//!
//! There are exactly five transitive subgroups of `S_5` and no such small catalogue exists at
//! general degree, so the catalogue is **not** generalised. It is retained as the degree-five
//! instance and an independent cross-check ([`quintic_group_catalogue`],
//! [`QuinticTransitiveGroup`]), and the degree-general return is the constraint population:
//!
//! - the observed cycle types with their witness primes;
//! - parity, from whether the discriminant is a square in `Q` — `G <= A_n` exactly then;
//! - transitivity, certified by one prime whose reduction is irreducible of full degree;
//! - and, **at prime degree only**, Galois's theorem on solvable equations of prime degree:
//!   an irreducible polynomial of prime degree `p` over a characteristic-zero field is solvable by
//!   radicals **iff** its Galois group embeds in `AGL(1,p) = {x -> ax + b}`, of order `p(p-1)`.
//!   An element `x -> ax + b` has cycle type `[1^p]` (identity), `[p]` (`a = 1`, `b != 0`), or
//!   `[1, d, ..., d]` with `d = ord(a)` dividing `p-1` and `(p-1)/d` cycles. Observing a Frobenius
//!   cycle type outside that derived set therefore **proves** `G` is not contained in `AGL(1,p)`,
//!   and at irreducible prime degree that is a proof of non-solvability with a named witness prime.
//!   At `p = 5` the admissible set is `{[1,1,1,1,1], [1,2,2], [1,4], [5]}`, which is exactly the
//!   union of the cycle types of `C_5`, `D_5` and `F_20` — the three the catalogue marks solvable.
//!
//! At composite degree the theorem states nothing, and [`SolvabilityConstraint`] returns
//! `NoCriterionAtThisDegree` rather than a guess. **A refusal that names why is the correct
//! return.**
//!
//! Observed cycle types may restrict the degree-five catalogue, and one irreducible reduction
//! certifies rational irreducibility, but absence of an unobserved cycle type never excludes a
//! group. A repeated reduction is retained as an open polynomial-discriminant place; this law does
//! not pretend that the chosen power basis supplies a ramified number-field Euler factor.
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
    ArithmeticFiberEvent, CausalMaterialKind, EventId,
    EventSuccessor, ExactEventLaw, IntegerPolynomialProbe, PolynomialFiberSignature,
    PolynomialPrimeFiber, PolynomialProbeId, PrimeEcologyError, PrimeEcologyEvent,
    PrimeEcologyGeometryReceipt, PrimeEcologyLaw, PrimeEcologyRadiation, PrimeEcologyStanding,
};

/// The lowest degree at which this organ's own material exists.
///
/// **MATERIAL, and the theorem is named.** Every return here is founded on the discriminant
/// `disc(f) = (-1)^(n(n-1)/2) Res(f, f')`, and `Res(f, f')` requires `deg f' >= 1`, hence `n >= 2`.
/// The same floor is stated independently by
/// [`crate::rational_polynomial::integer_discriminant`], which refuses `degree < 2` with
/// `DiscriminantDegreeTooLow`. It is not an aperture: a degree-one polynomial has one root, no pair
/// of roots to separate, no cycle type but the identity, and no Galois group to constrain.
const LEAST_DEGREE_WITH_A_DISCRIMINANT: usize = 2;

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct QuinticProblemId(pub u64);

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct EulerReceiverId(pub u64);

/// One inherited integral polynomial, coefficient-first, of any degree at least two.
///
/// The leading coefficient may be any nonzero integer. Scalar content is not erased: it remains
/// visible in the inherited presentation even though it does not change the root population.
///
/// **The degree is read off the coefficient vector.** The type keeps its historical name because
/// its module does; the *code* imposes no degree.
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

    /// The degree, read off the coefficient vector. Never authored.
    pub fn degree(&self) -> usize {
        self.coefficients.len().saturating_sub(1)
    }

    pub fn validate(&self) -> Result<(), ArithmeticMonodromyError> {
        if self.schema != "holonic-engine.integral-quintic-problem.v1"
            || self.name.is_empty()
            || self.coefficients.len() < LEAST_DEGREE_WITH_A_DISCRIMINANT + 1
            || self.coefficients[self.degree()].is_zero()
        {
            return Err(ArithmeticMonodromyError::MalformedQuintic(self.id));
        }
        Ok(())
    }

    /// Change `f(x)` into the monic integral polynomial
    ///
    /// `g(y) = a_n^(n-1) f(y/a_n)`, with `y = a_n x`.
    ///
    /// This preserves the splitting field over `Q`; it is not a numerical normalization. The
    /// coefficient of `y^d` is `c_d a_n^(n-1-d)`, and at `d = n` that is `a_n a_n^(-1) = 1`, which
    /// is why the loop runs below the leading term and pushes the one.
    pub fn normalize(&self) -> Result<NormalizedQuintic, ArithmeticMonodromyError> {
        self.validate()?;
        let degree = self.degree();
        let root_scale = self.coefficients[degree].clone();
        let mut normalized_coefficients = Vec::with_capacity(degree + 1);
        for (power, coefficient) in self.coefficients[..degree].iter().enumerate() {
            let exponent = u32::try_from(degree - 1 - power)
                .map_err(|_| ArithmeticMonodromyError::CarrierOverflow)?;
            normalized_coefficients.push(coefficient * root_scale.pow(exponent));
        }
        normalized_coefficients.push(BigInt::one());
        let probe = IntegerPolynomialProbe::new(
            PolynomialProbeId(self.id.0),
            format!("degree-{degree}[{}]", self.name),
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
    /// The degree, read off the normalised coefficient vector.
    pub fn degree(&self) -> usize {
        self.coefficients.len().saturating_sub(1)
    }

    fn validate(&self, inherited: &IntegralQuinticProblem) -> Result<(), ArithmeticMonodromyError> {
        if self.schema != "holonic-engine.normalized-quintic.v1"
            || self.problem != inherited.id
            || self.probe.id != PolynomialProbeId(inherited.id.0)
            || self.coefficients.len() != inherited.coefficients.len()
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

/// One observed Frobenius cycle type together with the prime that returned it.
///
/// A witness, not a count: the return names the material that decided it.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct CycleTypeWitness {
    pub prime: u64,
    pub cycle_type: Vec<u32>,
}

/// What the observed sections have settled about solvability by radicals, at any degree.
///
/// This is the degree-general replacement for reading a five-element catalogue. It returns a
/// **constraint**, never a group name, because at general degree there is no small catalogue to
/// name one from.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum SolvabilityConstraint {
    /// The degree is composite. Galois's theorem on solvable equations of **prime** degree states
    /// nothing here, and this organ returns no solvability verdict rather than guessing one.
    NoCriterionAtThisDegree {
        degree: usize,
        /// The smallest nontrivial factor, exhibited so the refusal names its own reason.
        least_factor: usize,
    },
    /// Prime degree, but no prime has yet certified irreducibility, so the theorem's hypothesis is
    /// unmet. Any affine-inadmissible type observed is still carried: *that* reading is a fact
    /// about `AGL(1,p)` and needs no hypothesis, but it does not by itself decide solvability.
    IrreducibilityNotCertified {
        degree: usize,
        outside_affine_group: Option<CycleTypeWitness>,
    },
    /// Prime degree, irreducible, and an observed Frobenius cycle type is the cycle type of no
    /// element of `AGL(1,p)`. Therefore `G` is not contained in `AGL(1,p)`, and by Galois's theorem
    /// the polynomial is **not solvable by radicals**. The witness prime is named.
    NotSolvable {
        degree: usize,
        witness: CycleTypeWitness,
        /// The derived admissible set the witness fell outside of.
        admissible_cycle_types: BTreeSet<Vec<u32>>,
    },
    /// Prime degree, irreducible, and every observed cycle type is admissible for `AGL(1,p)`.
    ///
    /// **This is not a proof of solvability.** The receiver family has seen finitely many primes
    /// and an unobserved type excludes nothing. The name says so.
    ConsistentWithSolvable {
        degree: usize,
        observed_cycle_types: BTreeSet<Vec<u32>>,
        admissible_cycle_types: BTreeSet<Vec<u32>>,
    },
}

impl SolvabilityConstraint {
    pub fn label(&self) -> &'static str {
        match self {
            Self::NoCriterionAtThisDegree { .. } => "NO-CRITERION-AT-THIS-DEGREE",
            Self::IrreducibilityNotCertified { .. } => "IRREDUCIBILITY-NOT-CERTIFIED",
            Self::NotSolvable { .. } => "NOT-SOLVABLE",
            Self::ConsistentWithSolvable { .. } => "CONSISTENT-WITH-SOLVABLE",
        }
    }

    /// The one verdict this criterion is entitled to assert.
    pub fn refutes_solvability(&self) -> bool {
        matches!(self, Self::NotSolvable { .. })
    }

    /// What refused, written out. Never a bool and never a group name at general degree.
    pub fn written(&self) -> String {
        match self {
            Self::NoCriterionAtThisDegree {
                degree,
                least_factor,
            } => format!(
                "degree {degree} is composite ({least_factor} divides it); Galois's prime-degree \
                 theorem states nothing here and no solvability verdict is returned"
            ),
            Self::IrreducibilityNotCertified {
                degree,
                outside_affine_group,
            } => match outside_affine_group {
                Some(witness) => format!(
                    "degree {degree} is prime and the cycle type {:?} at prime {} lies outside \
                     AGL(1,{degree}), so G is not contained in it — but irreducibility is not \
                     certified, so Galois's theorem does not convert that into a solvability \
                     verdict",
                    witness.cycle_type, witness.prime
                ),
                None => format!(
                    "degree {degree} is prime but irreducibility is not certified, so the \
                     prime-degree criterion has no hypothesis to run on"
                ),
            },
            Self::NotSolvable {
                degree, witness, ..
            } => format!(
                "the Frobenius cycle type {:?} at prime {} is the cycle type of no affine map \
                 x -> ax + b over F_{degree}, so G is not contained in AGL(1,{degree}); by \
                 Galois's theorem on irreducible equations of prime degree, not solvable by \
                 radicals",
                witness.cycle_type, witness.prime
            ),
            Self::ConsistentWithSolvable {
                degree,
                observed_cycle_types,
                ..
            } => format!(
                "every one of the {} observed cycle types is admissible for AGL(1,{degree}); \
                 consistent with solvability and NOT a proof of it — an unobserved type excludes \
                 nothing",
                observed_cycle_types.len()
            ),
        }
    }
}

/// The cycle types of the elements of `AGL(1,p) = {x -> ax + b : a in F_p^*, b in F_p}`, derived.
///
/// - `a = 1, b = 0` is the identity: `[1^p]`.
/// - `a = 1, b != 0` is a single `p`-cycle: `[p]`.
/// - `a != 1` has the unique fixed point `x = b/(1-a)` and every other orbit of length
///   `d = ord(a)`, which divides `p-1`: `[1, d, ..., d]` with `(p-1)/d` cycles of length `d`.
///
/// Every `d >= 2` dividing `p-1` is realised, because `F_p^*` is cyclic of order `p-1`. Nothing is
/// tabulated: the set is computed from `p` by enumerating the divisors of `p-1`.
///
/// At `p = 5` this returns `{[1,1,1,1,1], [1,2,2], [1,4], [5]}`, which is exactly the union of the
/// cycle types of `C_5`, `D_5` and `F_20`.
pub fn affine_group_cycle_types(prime_degree: usize) -> BTreeSet<Vec<u32>> {
    let mut types = BTreeSet::new();
    let degree = u32::try_from(prime_degree).unwrap_or(u32::MAX);
    types.insert(vec![1_u32; prime_degree]);
    types.insert(vec![degree]);
    for order in 2..prime_degree {
        if !(prime_degree - 1).is_multiple_of(order) {
            continue;
        }
        let cycles = (prime_degree - 1) / order;
        let mut cycle_type = vec![1_u32];
        cycle_type.extend(std::iter::repeat_n(
            u32::try_from(order).unwrap_or(u32::MAX),
            cycles,
        ));
        cycle_type.sort_unstable();
        types.insert(cycle_type);
    }
    types
}

/// The least nontrivial factor of `n`, or `None` when `n` is prime. Trial transport to the
/// square-root frontier: exhaustion is what founds primality, exactly as `CLAUDE.md` §3 states it.
pub fn least_nontrivial_factor(value: usize) -> Option<usize> {
    if value < 2 {
        return Some(value);
    }
    let mut candidate: usize = 2;
    while candidate.saturating_mul(candidate) <= value {
        if value.is_multiple_of(candidate) {
            return Some(candidate);
        }
        candidate += 1;
    }
    None
}

/// The five transitive subgroups of `S_5`, in their natural degree-five actions.
///
/// **Retained as the degree-five instance and an independent cross-check**, not generalised. See
/// [`SolvabilityConstraint`] for the criterion that runs at every degree.
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
    /// The degree of the normalised source, read off its coefficients.
    pub degree: usize,
    pub discriminant: BigInt,
    pub discriminant_square_root: Option<BigInt>,
    pub irreducibility: QuinticIrreducibility,
    /// Cycle type -> every prime receiver which returned that exact type.
    pub cycle_witnesses: BTreeMap<Vec<u32>, BTreeSet<u64>>,
    /// The degree-general constraint: what the observed sections have settled about solvability.
    pub solvability: SolvabilityConstraint,
    /// **Degree five only.** Conditional until `irreducibility` closes. Empty means either that the
    /// transitive catalogue was obstructed by the received sections, or that the degree is not five
    /// and the catalogue does not apply at all — [`Self::catalogue_applies`] separates the two.
    pub transitive_candidates: BTreeSet<QuinticTransitiveGroup>,
}

impl QuinticGaloisFiber {
    /// Whether the degree-five transitive catalogue is inside its declared aperture here.
    ///
    /// An organ used past its declared aperture is a defect even when it appears to return
    /// (`CLAUDE.md` §8), and an empty candidate set means *obstructed* only when the catalogue
    /// applies in the first place.
    pub fn catalogue_applies(&self) -> bool {
        self.degree == catalogued_transitive_degree()
    }

    pub fn unique_certified_group(&self) -> Option<QuinticTransitiveGroup> {
        if matches!(
            self.irreducibility,
            QuinticIrreducibility::CertifiedByPrime { .. }
        ) && self.catalogue_applies()
            && self.transitive_candidates.len() == 1
        {
            self.transitive_candidates.iter().copied().next()
        } else {
            None
        }
    }

    /// The cycle types the surviving degree-five candidates could still return. Empty at every
    /// other degree, where the catalogue does not apply.
    pub fn admitted_future_cycle_types(
        &self,
    ) -> Result<BTreeSet<Vec<u32>>, ArithmeticMonodromyError> {
        if !self.catalogue_applies() {
            return Ok(BTreeSet::new());
        }
        let catalogue = quintic_group_catalogue()?;
        Ok(self
            .transitive_candidates
            .iter()
            .flat_map(|group| catalogue[group].cycle_types.iter().cloned())
            .collect())
    }

    /// The two routes to a solvability verdict, held against each other at degree five.
    ///
    /// `Some(true)` means both applied and agreed, `Some(false)` means both applied and disagreed —
    /// which is a defect in one of them — and `None` means only one route applied, so there is
    /// nothing to compare. The equivalence asserted is
    ///
    /// ```text
    ///   SolvabilityConstraint::NotSolvable  <=>  no admitted transitive group is solvable
    /// ```
    ///
    /// and it holds at `p = 5` because `AGL(1,5)`'s cycle types are exactly the union of `C_5`'s,
    /// `D_5`'s and `F_20`'s.
    pub fn criterion_agrees_with_catalogue(&self) -> Option<bool> {
        if !self.catalogue_applies()
            || !matches!(
                self.irreducibility,
                QuinticIrreducibility::CertifiedByPrime { .. }
            )
        {
            return None;
        }
        let catalogue_refutes = !self.transitive_candidates.is_empty()
            && !self
                .transitive_candidates
                .iter()
                .any(|group| group.solvable_by_radicals());
        Some(self.solvability.refutes_solvability() == catalogue_refutes)
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
        let section = derive_prime_section(self.problem.id, self.normalized.degree(), fiber)?;
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
            inherited_coefficient_count: standing.problem.coefficients.len(),
            normalized_projective_free_rank: standing.normalized.degree(),
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
    degree: usize,
    fiber: &PolynomialPrimeFiber,
) -> Result<QuinticPrimeSection, ArithmeticMonodromyError> {
    fiber.validate()?;
    let expected =
        u32::try_from(degree).map_err(|_| ArithmeticMonodromyError::CarrierOverflow)?;
    if fiber.signature.degree != expected {
        return Err(ArithmeticMonodromyError::FiberDegreeMismatch {
            problem,
            prime: fiber.prime,
            degree: fiber.signature.degree,
            expected,
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
            if total != expected {
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
    // The sign of a permutation on `n` points is `(-1)^(n - number of cycles)`: each cycle of
    // length `L` is `L - 1` transpositions, and the lengths sum to `n`.
    let permutation_is_even = cycle_type.as_ref().map(|cycles| {
        (expected - u32::try_from(cycles.len()).expect("a cycle population fits in u32"))
            .is_multiple_of(2)
    });
    let euler_denominator = cycle_type
        .as_ref()
        .map(|cycles| formal_euler_denominator(cycles, degree))
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
    let degree = normalized.degree();
    // Parity is degree-general: `disc(f)` is a square in `Q` exactly when `G <= A_n`. The
    // catalogue is not, so it is filtered only at its own degree.
    let transitive_candidates = if normalized.discriminant.is_zero() || degree != catalogued_transitive_degree() {
        BTreeSet::new()
    } else {
        let square = normalized.discriminant_square_root.is_some();
        quintic_group_catalogue()?
            .iter()
            .filter_map(|(group, entry)| (entry.all_even == square).then_some(*group))
            .collect()
    };
    let mut galois = QuinticGaloisFiber {
        schema: "holonic-engine.quintic-galois-fiber.v1".to_owned(),
        degree,
        discriminant: normalized.discriminant.clone(),
        discriminant_square_root: normalized.discriminant_square_root.clone(),
        irreducibility: QuinticIrreducibility::Open,
        cycle_witnesses: BTreeMap::new(),
        solvability: SolvabilityConstraint::NoCriterionAtThisDegree {
            degree,
            least_factor: 0,
        },
        transitive_candidates,
    };
    galois.solvability = derive_solvability_constraint(&galois);
    Ok(galois)
}

/// Galois's theorem on solvable equations of prime degree, run against the observed cycle types.
///
/// The reading is entirely derived: [`affine_group_cycle_types`] computes the admissible set from
/// the degree, and a single observed type outside it proves `G` is not contained in `AGL(1,p)`.
/// Everything the theorem does not license is returned as one of the two non-verdict species.
fn derive_solvability_constraint(galois: &QuinticGaloisFiber) -> SolvabilityConstraint {
    let degree = galois.degree;
    if let Some(least_factor) = least_nontrivial_factor(degree) {
        return SolvabilityConstraint::NoCriterionAtThisDegree {
            degree,
            least_factor,
        };
    }
    let admissible = affine_group_cycle_types(degree);
    let outside = galois
        .cycle_witnesses
        .iter()
        .find(|(cycle_type, _)| !admissible.contains(*cycle_type))
        .and_then(|(cycle_type, primes)| {
            primes.iter().next().map(|prime| CycleTypeWitness {
                prime: *prime,
                cycle_type: cycle_type.clone(),
            })
        });
    if !matches!(
        galois.irreducibility,
        QuinticIrreducibility::CertifiedByPrime { .. }
    ) {
        return SolvabilityConstraint::IrreducibilityNotCertified {
            degree,
            outside_affine_group: outside,
        };
    }
    match outside {
        Some(witness) => SolvabilityConstraint::NotSolvable {
            degree,
            witness,
            admissible_cycle_types: admissible,
        },
        None => SolvabilityConstraint::ConsistentWithSolvable {
            degree,
            observed_cycle_types: galois.cycle_witnesses.keys().cloned().collect(),
            admissible_cycle_types: admissible,
        },
    }
}

fn transport_section_into_galois(
    galois: &mut QuinticGaloisFiber,
    section: &QuinticPrimeSection,
) -> Result<(), ArithmeticMonodromyError> {
    let Some(cycle_type) = &section.cycle_type else {
        return Ok(());
    };
    let full_cycle =
        u32::try_from(galois.degree).map_err(|_| ArithmeticMonodromyError::CarrierOverflow)?;
    galois
        .cycle_witnesses
        .entry(cycle_type.clone())
        .or_default()
        .insert(section.prime);
    if cycle_type == &[full_cycle] && matches!(galois.irreducibility, QuinticIrreducibility::Open) {
        galois.irreducibility = QuinticIrreducibility::CertifiedByPrime {
            prime: section.prime,
            source_events: section.source_events.clone(),
        };
    }
    if galois.catalogue_applies() {
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
    }
    galois.solvability = derive_solvability_constraint(galois);
    Ok(())
}

fn formal_euler_denominator(
    cycle_type: &[u32],
    degree: usize,
) -> Result<Vec<BigInt>, ArithmeticMonodromyError> {
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
    if result.len() != degree + 1 || result[0] != BigInt::one() {
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

/// A permutation of `0..n`, in one-line notation.
///
/// **This carrier was `type Permutation5 = [u8; QUINTIC_DEGREE]` until 2026-08-09** — the degree
/// carried as a type, which no search over `const NAME: type = N;` could ever see
/// (`canon/THE_AUTHORED_LEVEL.md` §5.4 names it as the standing example). Its extent is now read
/// off the permutation itself.
type Permutation = Vec<u8>;

#[derive(Clone, Debug)]
struct QuinticGroupCatalogueEntry {
    cycle_types: BTreeSet<Vec<u32>>,
    all_even: bool,
}

/// The declared generators of the five transitive subgroups of `S_5`, as **material**.
///
/// A permutation is not a level: it is the group's definition, written in one-line notation. Their
/// common extent is what [`catalogued_transitive_degree`] reads, so the catalogue's degree is
/// carried by the mathematics it declares rather than by a constant this organ authored.
fn quintic_group_generators() -> BTreeMap<QuinticTransitiveGroup, Vec<Permutation>> {
    let rotation: Permutation = vec![1, 2, 3, 4, 0];
    let reflection: Permutation = vec![0, 4, 3, 2, 1];
    let dilation_two: Permutation = vec![0, 2, 4, 1, 3];
    let three_cycle: Permutation = vec![1, 2, 0, 3, 4];
    let transposition: Permutation = vec![1, 0, 2, 3, 4];
    BTreeMap::from([
        (QuinticTransitiveGroup::Cyclic5, vec![rotation.clone()]),
        (
            QuinticTransitiveGroup::Dihedral5,
            vec![rotation.clone(), reflection],
        ),
        (
            QuinticTransitiveGroup::Frobenius20,
            vec![rotation.clone(), dilation_two],
        ),
        (
            QuinticTransitiveGroup::Alternating5,
            vec![rotation.clone(), three_cycle],
        ),
        (
            QuinticTransitiveGroup::Symmetric5,
            vec![rotation, transposition],
        ),
    ])
}

/// The degree the transitive catalogue is declared over, **read off its own generators**.
///
/// `S_5` has exactly five transitive subgroups; there is no comparably small catalogue at general
/// degree, so the catalogue is not generalised. It is retained as its own instance and as the
/// independent cross-check on [`SolvabilityConstraint`], and this function is how any other organ
/// asks whether it is inside that aperture — without a `5` written anywhere but in the declared
/// permutations themselves.
pub fn catalogued_transitive_degree() -> usize {
    quintic_group_generators()
        .values()
        .flat_map(|generators| generators.iter())
        .map(Vec::len)
        .max()
        .unwrap_or(0)
}

/// The five transitive subgroups of `S_5`, generated rather than tabulated.
///
/// **Degree five only, and deliberately so.** This is the catalogued instance
/// [`SolvabilityConstraint`] is cross-checked against; it is not the criterion.
fn quintic_group_catalogue()
-> Result<BTreeMap<QuinticTransitiveGroup, QuinticGroupCatalogueEntry>, ArithmeticMonodromyError> {
    let mut catalogue = BTreeMap::new();
    for (group, generators) in quintic_group_generators() {
        let elements = generated_permutation_group(&generators)?;
        if elements.len()
            != usize::try_from(group.order())
                .map_err(|_| ArithmeticMonodromyError::CarrierOverflow)?
        {
            return Err(ArithmeticMonodromyError::InvalidGroupCatalogue(group));
        }
        let cycle_types = elements
            .iter()
            .map(permutation_cycle_type)
            .collect();
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

/// The subgroup of `S_n` generated by a declared generator set, by breadth-first closure.
///
/// The closure bound is `n!` — the order of the whole symmetric group, which no subgroup exceeds by
/// Lagrange. It is read off the generators' own extent, never authored: the previous form compared
/// against the literal `120`, which is `5!` written as a number.
fn generated_permutation_group(
    generators: &[Permutation],
) -> Result<BTreeSet<Permutation>, ArithmeticMonodromyError> {
    let extent = generators
        .first()
        .map(Vec::len)
        .ok_or(ArithmeticMonodromyError::InvalidPermutationGroup)?;
    for generator in generators {
        validate_permutation(generator, extent)?;
    }
    let symmetric_order = (1..=extent).try_fold(1_usize, |product, factor| {
        product
            .checked_mul(factor)
            .ok_or(ArithmeticMonodromyError::CarrierOverflow)
    })?;
    let identity: Permutation = (0..extent)
        .map(|index| u8::try_from(index).map_err(|_| ArithmeticMonodromyError::CarrierOverflow))
        .collect::<Result<_, _>>()?;
    let mut elements = BTreeSet::from([identity.clone()]);
    let mut frontier = VecDeque::from([identity]);
    while let Some(current) = frontier.pop_front() {
        for generator in generators {
            let next = compose_permutations(&current, generator);
            if elements.insert(next.clone()) {
                if elements.len() > symmetric_order {
                    return Err(ArithmeticMonodromyError::InvalidPermutationGroup);
                }
                frontier.push_back(next);
            }
        }
    }
    Ok(elements)
}

fn validate_permutation(
    permutation: &Permutation,
    extent: usize,
) -> Result<(), ArithmeticMonodromyError> {
    let expected = (0..extent)
        .map(|index| u8::try_from(index).map_err(|_| ArithmeticMonodromyError::CarrierOverflow))
        .collect::<Result<BTreeSet<_>, _>>()?;
    if permutation.len() != extent
        || permutation.iter().copied().collect::<BTreeSet<_>>() != expected
    {
        return Err(ArithmeticMonodromyError::InvalidPermutationGroup);
    }
    Ok(())
}

fn compose_permutations(left: &Permutation, right: &Permutation) -> Permutation {
    right
        .iter()
        .map(|index| left[usize::from(*index)])
        .collect()
}

fn permutation_cycle_type(permutation: &Permutation) -> Vec<u32> {
    let mut visited = vec![false; permutation.len()];
    let mut cycles = Vec::new();
    for start in 0..permutation.len() {
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

fn permutation_is_even(permutation: &Permutation) -> bool {
    let cycles = permutation_cycle_type(permutation);
    (permutation.len() - cycles.len()).is_multiple_of(2)
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
    #[error(
        "problem {problem:?} received a degree-{degree} fiber at prime {prime}, but its own degree \
         is {expected}"
    )]
    FiberDegreeMismatch {
        problem: QuinticProblemId,
        prime: u64,
        degree: u32,
        expected: u32,
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

    /// **What this test body declares as its horn local-section limit.** It moved out of the organ
    /// on 2026-08-09 (`canon/THE_CONTAMINANT_PROTOCOL.md` §2.5 — *a default is a level the organ
    /// picked because the caller was never asked*), and a fixture is a caller. The value reproduces
    /// the excised `DEFAULT_HORN_LOCAL_SECTION_LIMIT` so these fixtures' returns are unchanged by
    /// the move.
    const TEST_HORN_LOCAL_SECTION_LIMIT: u64 = 1_000_000;
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

    /// The degree-general criterion, held against the degree-five catalogue on the one degree
    /// where both exist.
    ///
    /// `AGL(1,5)`'s cycle types must be **exactly** the union of the cycle types of `C_5`, `D_5`
    /// and `F_20` — the three groups `solvable_by_radicals()` marks solvable. That is not an
    /// arrangement: `F_20` **is** `AGL(1,5)`, and the other two are its subgroups. Two independent
    /// implementations of one set, per `CLAUDE.md` §8.
    #[test]
    fn the_affine_criterion_reproduces_the_catalogue_at_degree_five() {
        let catalogue = quintic_group_catalogue().unwrap();
        let solvable_union = catalogue
            .iter()
            .filter(|(group, _)| group.solvable_by_radicals())
            .flat_map(|(_, entry)| entry.cycle_types.iter().cloned())
            .collect::<BTreeSet<_>>();
        assert_eq!(affine_group_cycle_types(5), solvable_union);
        assert_eq!(
            solvable_union,
            BTreeSet::from([vec![1, 1, 1, 1, 1], vec![1, 2, 2], vec![1, 4], vec![5]])
        );
        // And the separating material: every cycle type an S_5 or A_5 element has that the affine
        // group does not is a refuter, so the criterion is not vacuous at this degree.
        let symmetric = &catalogue[&QuinticTransitiveGroup::Symmetric5].cycle_types;
        let refuters = symmetric
            .difference(&solvable_union)
            .cloned()
            .collect::<BTreeSet<_>>();
        assert_eq!(
            refuters,
            BTreeSet::from([vec![1, 1, 1, 2], vec![1, 1, 3], vec![2, 3]])
        );
    }

    /// The admissible set is computed from the divisors of `p-1`, never tabulated.
    ///
    /// `|types| = tau(p-1) + 1`: the identity, the `p`-cycle, and one type per divisor `d >= 2` of
    /// `p-1`. Every type partitions `p`, which is what makes it a cycle type on `p` points at all.
    #[test]
    fn affine_cycle_types_are_derived_from_the_divisors_of_the_predecessor() {
        for prime in [2_usize, 3, 5, 7, 11, 13] {
            let types = affine_group_cycle_types(prime);
            let divisors = (1..prime).filter(|d| (prime - 1) % d == 0).count();
            assert_eq!(
                types.len(),
                divisors + 1,
                "AGL(1,{prime}) should carry tau({}) + 1 cycle types",
                prime - 1
            );
            for cycle_type in &types {
                let total: u32 = cycle_type.iter().sum();
                assert_eq!(total as usize, prime, "{cycle_type:?} does not partition {prime}");
            }
            assert!(types.contains(&vec![prime as u32]));
            assert!(types.contains(&vec![1_u32; prime]));
        }
        // Degree seven, worked: the divisors of six above one are 2, 3 and 6.
        assert_eq!(
            affine_group_cycle_types(7),
            BTreeSet::from([
                vec![1, 1, 1, 1, 1, 1, 1],
                vec![1, 2, 2, 2],
                vec![1, 3, 3],
                vec![1, 6],
                vec![7],
            ])
        );
    }

    /// Trial transport to the square-root frontier, which is what founds primality.
    #[test]
    fn the_least_factor_founds_the_degrees_the_criterion_applies_to() {
        for prime in [2_usize, 3, 5, 7, 11, 13, 17, 19, 23] {
            assert_eq!(least_nontrivial_factor(prime), None, "{prime} is prime");
        }
        assert_eq!(least_nontrivial_factor(4), Some(2));
        assert_eq!(least_nontrivial_factor(6), Some(2));
        assert_eq!(least_nontrivial_factor(9), Some(3));
        assert_eq!(least_nontrivial_factor(25), Some(5));
        assert_eq!(least_nontrivial_factor(35), Some(5));
    }

    /// The permutation carrier is general, and the closure bound is `n!` read off the generators.
    ///
    /// `Permutation5 = [u8; 5]` could not have run this at all: the degree was the type.
    #[test]
    fn the_permutation_carrier_generates_at_a_degree_other_than_five() {
        // S_3 from a transposition and a three-cycle.
        let symmetric_three =
            generated_permutation_group(&[vec![1, 0, 2], vec![1, 2, 0]]).unwrap();
        assert_eq!(symmetric_three.len(), 6);
        assert_eq!(
            symmetric_three
                .iter()
                .map(permutation_cycle_type)
                .collect::<BTreeSet<_>>(),
            BTreeSet::from([vec![1, 1, 1], vec![1, 2], vec![3]])
        );
        // C_7 from a single seven-cycle: order seven, every non-identity element a full cycle.
        let cyclic_seven = generated_permutation_group(&[vec![1, 2, 3, 4, 5, 6, 0]]).unwrap();
        assert_eq!(cyclic_seven.len(), 7);
        assert!(cyclic_seven.iter().all(permutation_is_even));
        // A malformed generator is refused rather than silently padded.
        assert!(generated_permutation_group(&[vec![0, 0, 1]]).is_err());
    }

    /// Normalization is `a_n^(n-1) f(y/a_n)` at every degree, checked at exact integer receivers.
    #[test]
    fn a_cubic_and_a_sextic_normalize_through_the_same_root_scale() {
        for (degree, coefficients) in [
            (3_usize, vec![5_i64, -1, 4, 3]),
            (6, vec![-7_i64, 2, 0, 1, -3, 0, -2]),
        ] {
            let problem = IntegralQuinticProblem::new(
                QuinticProblemId(degree as u64),
                format!("degree-{degree}"),
                coefficients.iter().copied().map(BigInt::from).collect(),
            )
            .unwrap();
            assert_eq!(problem.degree(), degree);
            let normalized = problem.normalize().unwrap();
            assert_eq!(normalized.degree(), degree);
            assert_eq!(normalized.coefficients.last(), Some(&BigInt::one()));
            let exponent = u32::try_from(degree - 1).unwrap();
            for x in -3_i64..=3 {
                let x = BigInt::from(x);
                let y = &normalized.root_scale * &x;
                assert_eq!(
                    evaluate_integer_polynomial(&normalized.coefficients, &y),
                    normalized.root_scale.pow(exponent)
                        * evaluate_integer_polynomial(&problem.coefficients, &x)
                );
            }
        }
    }

    /// The one degree floor this organ keeps, and it is a theorem rather than an aperture.
    #[test]
    fn a_linear_polynomial_is_refused_because_it_has_no_discriminant() {
        assert!(
            IntegralQuinticProblem::new(
                QuinticProblemId(1),
                "linear",
                vec![BigInt::from(-2), BigInt::one()],
            )
            .is_err()
        );
        assert!(
            IntegralQuinticProblem::new(
                QuinticProblemId(1),
                "quadratic",
                vec![BigInt::from(-2), BigInt::from(0), BigInt::one()],
            )
            .is_ok()
        );
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
        let law = ArithmeticMonodromyLaw::with_horn_local_section_limit(1, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
        let standing = ArithmeticMonodromyStanding::with_horn_local_section_limit(1, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
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

        let law = ArithmeticMonodromyLaw::with_horn_local_section_limit(1, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
        let standing = ArithmeticMonodromyStanding::with_horn_local_section_limit(1, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
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
        let law = ArithmeticMonodromyLaw::with_horn_local_section_limit(1, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
        let standing = ArithmeticMonodromyStanding::with_horn_local_section_limit(1, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
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
        let law = ArithmeticMonodromyLaw::with_horn_local_section_limit(1, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
        let standing = ArithmeticMonodromyStanding::with_horn_local_section_limit(1, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
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
