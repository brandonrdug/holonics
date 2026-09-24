//! **The helical pair contact: the cell that slips, dissipates and addresses.**
//!
//! [definition] Two navigators with situated screws `ξ_a`, `ξ_b` and initial configurations
//! generate the curves `x_a(s)`, `x_b(t)` ([objects §4](../../../../docs/ELEMENTARY_OBJECTS.md#4-pair-contact)).
//! Their contact is read at the retained configuration:
//!
//! ```text
//! Δ = x_a(s) − x_b(t)          Q = ⟨Δ|Δ⟩
//! J = [v_a | −v_b]             Δ̇ = J (ṡ, ṫ)                       the slip map
//! DQ = 2 Jᵀ Δ                  D²Q = 2 JᵀJ + 2 diag(Δ·a_a, −Δ·a_b)
//! M = Σ_f w_f J_fᵀ D_f J_f     P(u) = ⟨J u, w D J u⟩ ≥ 0           the contact material
//! P(u) = 0  ⇔  D J u = 0  (w > 0)   q·v_a = p·v_b  ⇔  a no-slip lock at rate ratio p/q
//! ```
//!
//! The contact is a resistive element on relative slip: flow `f = J u`, effort `e = −w D f`,
//! power `⟨e, f⟩ = −⟨u, M u⟩ ≤ 0`. For a positive weight `w > 0` (Lean's hypothesis `hw`) zero
//! power is exactly `D J u = 0`; a zero weight dissipates nothing at any rate. Zero power coincides
//! with no slip only where the material is definite on the attainable slips; a positive
//! semidefinite `D` can be blind to a slip. A lock at a positive rate ratio has a Farey address;
//! signed and stationary relations keep their own reading, and the rate pair `0/0` declares no
//! ratio and is refused.
//!
//! The alignment of two velocities is a ratio carried undivided: by Lagrange's identity
//! `⟨a|b⟩² + |a × b|² = |a|²|b|²`, the cohering and turning faces are two numerators over one
//! denominator, and the sign of `⟨a|b⟩` (the hand the square erases) is kept beside them.
//!
//! An ordered family of situated screws is a **serial chain**: its finite configuration is the
//! ordered product of the joint actions, its Jacobian columns are each joint's Lie generator
//! recharted through the preceding product, and a contact between two links reads the relative
//! velocity of its two points through those columns; at the joints' declared rates the columns
//! sum to the contact's slip. A revolute joint is carried in the Cayley half-angle chart, whose
//! parameter rate `ṫ` is the angular rate `2ṫ/(1 + t²)`; no rational screw is exponentiated.
//!
//! | Lean | Rust |
//! |---|---|
//! | `Transport/HelicalPairInteraction.pairSlip`, `pairSlip_mulVec`, `pairSlip_transpose_mulVec` | [`PairContact::slip`], [`PairContact::relative_velocity`] |
//! | `Transport/HelicalPairInteraction.pairFeatureAt_gradient`, `pairQuadranceHessian` | [`PairContact::gradient`], [`PairContact::hessian`] |
//! | `Transport/HelicalPairInteraction.pairFeatureReturn_adjoint` | [`PairContact::feature_pullback`] |
//! | `Transport/HelicalPairInteraction.pair_face_power`, `pair_face_power_eq_zero_iff_material_null` | [`ContactMaterial::power`], [`ContactMaterial::zero_power_kernel`] |
//! | `Transport/HelicalPairInteraction.lock_iff_zero_power` | [`pair_lock`], [`ContactMaterial::definite_on_slips`] |
//! | `Holon/Conformance.pairContact_resistive` | [`ContactMaterial::element`], [`ContactMaterial::bond`] |
//! | `Geometry/PairResonance` (neighbours, mediant) | [`PairContact::lock`] through [`LockAddress`] |
//! | `HolonicsResearch/Transport/Fold.lagrange_identity` | [`Alignment`] |
//! | `Transport/SerialScrewChain.serialConfiguration`, `serialPrefixes`, `cayleyZChart` | [`SerialChain`] |
//!
//! [proved-derived; implemented-exact] The chain's derivative has no Lean counterpart:
//! [`JointMotion::parameter_generator`], [`SerialChain::spatial_jacobian`],
//! [`SerialChain::contact_jacobian`] and [`SerialChain::contact_slip`] state it here, and the
//! continuous chain derivative is the #62 obligation (`Transport/SerialScrewChain` stops at the
//! finite configuration). The tests compare every column with the exact product-rule derivative of
//! the Cayley charts.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use thiserror::Error;

use crate::geometry::screw::{PairQuadranceJet, ScrewGenerator, ScrewPair, SituatedScrew};
use crate::geometry::{AffineMap3, Axis, RatMat3, RatVec3};
use crate::holon::HolonError;
use crate::holon::element::ResistiveRelation;
use crate::holon::port::Bond;
use crate::navigator::address::LockAddress;
use crate::ratio::linear::inertia::{InertiaError, SymmetricForm, inertia};
use crate::ratio::linear::{ExactLinearError, ExactRatMatrix};
use crate::ratio::{Presentation, Rat, integer};

/// Every refusal of a contact. Bad input is a typed return, never a panic.
#[derive(Debug, Error, PartialEq, Eq)]
pub enum ContactError {
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
    #[error(transparent)]
    Inertia(#[from] InertiaError),
    #[error(transparent)]
    Holon(#[from] HolonError),
    #[error("a contact response acts on the three slip coordinates; this one has extent {found}")]
    ResponseExtent { found: usize },
    #[error("a contact response must be positive semidefinite")]
    ResponseNotPassive,
    #[error("a contact weight must be nonnegative, found {weight}")]
    NegativeWeight { weight: Rat },
    #[error("{what}: expected {expected}, found {found}")]
    Shape {
        what: &'static str,
        expected: usize,
        found: usize,
    },
    #[error("a zero velocity has no alignment against another")]
    NullVelocity,
    #[error("the rate pair 0/0 declares no rate ratio")]
    DegenerateRate,
    #[error("the joint's situated generator is not the generator of its finite chart")]
    GeneratorMismatch,
    #[error("joint parameter {parameter} lies outside [{lower}, {upper}]")]
    OutsideLimit {
        parameter: Rat,
        lower: Rat,
        upper: Rat,
    },
    #[error("a joint limit must have its lower bound at or below its upper bound")]
    InvalidLimit,
    #[error("a chain frame must be a proper rigid motion")]
    NotProperRigid,
    #[error("link {link} is outside the chain")]
    LinkOutside { link: usize },
}

fn column_matrix(columns: &[RatVec3]) -> Result<ExactRatMatrix, ExactLinearError> {
    ExactRatMatrix::shaped(
        3,
        columns.len(),
        [0, 1, 2]
            .into_iter()
            .map(|row| {
                columns
                    .iter()
                    .map(|column| match row {
                        0 => column.x.clone(),
                        1 => column.y.clone(),
                        _ => column.z.clone(),
                    })
                    .collect()
            })
            .collect(),
    )
}

#[cfg(test)]
fn vector(values: &[Rat]) -> RatVec3 {
    RatVec3::new(values[0].clone(), values[1].clone(), values[2].clone())
}

// -------------------------------------------------------------------------------------------
// the pair

/// **The helical pair contact** at the retained initial configuration of both navigators.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairContact {
    pair: ScrewPair,
    velocities: [RatVec3; 2],
    accelerations: [RatVec3; 2],
    jet: PairQuadranceJet,
}

/// A covector over the fixed-generator pair feature `(Δ, Q, DQ)`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FeatureCovector {
    pub delta: RatVec3,
    pub quadrance: Rat,
    pub gradient: [Rat; 2],
}

/// What a declared rate ratio says about the pair.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LockReading {
    /// `q·v_a ≠ p·v_b`: the pair slips at this ratio.
    NotLocked,
    /// A positive lock, addressed by its Stern–Brocot word.
    PositiveAddress(LockAddress),
    /// A lock at a signed or stationary rate relation, outside the positive Farey chart.
    SignedOrStationary {
        numerator: BigInt,
        denominator: BigInt,
    },
}

impl PairContact {
    pub fn of(pair: ScrewPair) -> Self {
        let (a, b) = (pair.first(), pair.second());
        let velocities = [
            a.generator().velocity(a.initial()),
            b.generator().velocity(b.initial()),
        ];
        let accelerations = [
            a.generator().acceleration(a.initial()),
            b.generator().acceleration(b.initial()),
        ];
        let jet = PairQuadranceJet::at(a.generator(), a.initial(), b.generator(), b.initial());
        Self {
            pair,
            velocities,
            accelerations,
            jet,
        }
    }

    pub fn pair(&self) -> &ScrewPair {
        &self.pair
    }

    /// The quadrance jet of the pair's two generated curves.
    pub fn jet(&self) -> &PairQuadranceJet {
        &self.jet
    }

    /// `Δ = x_a − x_b`.
    pub fn separation(&self) -> &RatVec3 {
        self.jet.separation()
    }

    /// `Q = ⟨Δ|Δ⟩`.
    pub fn quadrance(&self) -> &Rat {
        self.jet.quadrance()
    }

    /// **The slip map** `J = [v_a | −v_b]`, `3 × 2`.
    pub fn slip(&self) -> Result<ExactRatMatrix, ContactError> {
        Ok(column_matrix(&[
            self.velocities[0].clone(),
            self.velocities[1].scale(&integer(-1)),
        ])?)
    }

    /// `Δ̇ = J (ṡ, ṫ) = ṡ v_a − ṫ v_b`.
    pub fn relative_velocity(&self, rates: &[Rat; 2]) -> RatVec3 {
        self.velocities[0]
            .scale(&rates[0])
            .subtract(&self.velocities[1].scale(&rates[1]))
    }

    /// `DQ = 2 Jᵀ Δ`, read through the slip adjoint.
    pub fn gradient(&self) -> Result<[Rat; 2], ContactError> {
        let delta = self.separation();
        let pulled = self.slip()?.transpose()?.apply(&[
            delta.x.clone(),
            delta.y.clone(),
            delta.z.clone(),
        ])?;
        Ok([integer(2) * &pulled[0], integer(2) * &pulled[1]])
    }

    /// `D²Q = 2 JᵀJ + 2 diag(Δ·a_a, −Δ·a_b)`: the isotropic contact form and both geometric terms.
    pub fn hessian(&self) -> Result<[[Rat; 2]; 2], ContactError> {
        let slip = self.slip()?;
        let gram = slip.transpose()?.multiply(&slip)?;
        let two = integer(2);
        let delta = self.separation();
        let geometric = [
            delta.dot(&self.accelerations[0]),
            -delta.dot(&self.accelerations[1]),
        ];
        Ok([
            [
                &two * (gram.get(0, 0)? + &geometric[0]),
                &two * gram.get(0, 1)?,
            ],
            [
                &two * gram.get(1, 0)?,
                &two * (gram.get(1, 1)? + &geometric[1]),
            ],
        ])
    }

    /// **The complete fixed-generator return** of a covector over `(Δ, Q, DQ)`:
    /// `Jᵀ λ_Δ + λ_Q DQ + (D²Q)ᵀ λ_DQ`, including the Hessian term the scalar pullback lacks.
    pub fn feature_pullback(&self, covector: &FeatureCovector) -> Result<[Rat; 2], ContactError> {
        let slip = self.slip()?;
        let gradient = self.gradient()?;
        let hessian = self.hessian()?;
        let delta = &covector.delta;
        let through_slip =
            slip.transpose()?
                .apply(&[delta.x.clone(), delta.y.clone(), delta.z.clone()])?;
        let mut result = [Rat::zero(), Rat::zero()];
        for (column, value) in result.iter_mut().enumerate() {
            *value = &through_slip[column]
                + &covector.quadrance * &gradient[column]
                + &hessian[0][column] * &covector.gradient[0]
                + &hessian[1][column] * &covector.gradient[1];
        }
        Ok(result)
    }

    /// The lock reading at the rate ratio `p/q`: a lock whose ratio is positive carries its Farey
    /// address, whatever the signs of `p` and `q` (`−1/−2` is the lock `1/2`). The pair `0/0` is
    /// refused.
    pub fn lock(
        &self,
        numerator: &BigInt,
        denominator: &BigInt,
    ) -> Result<LockReading, ContactError> {
        if !pair_lock(&self.pair, numerator, denominator)? {
            return Ok(LockReading::NotLocked);
        }
        if !denominator.is_zero() && Rat::new(numerator.clone(), denominator.clone()).is_positive()
        {
            if let Ok(address) = LockAddress::from_ratio(numerator, denominator) {
                return Ok(LockReading::PositiveAddress(address));
            }
        }
        Ok(LockReading::SignedOrStationary {
            numerator: numerator.clone(),
            denominator: denominator.clone(),
        })
    }
}

/// [proved-derived; implemented-exact] The pair locks at rate ratio `p/q` exactly when
/// `q·v_a = p·v_b` at the retained initial configurations: the zero-slip direction of
/// `Transport/HelicalPairInteraction.lock_iff_zero_power`. The pair `0/0` is no rate ratio (it
/// would read every pair as locked) and is refused.
pub fn pair_lock(
    pair: &ScrewPair,
    numerator: &BigInt,
    denominator: &BigInt,
) -> Result<bool, ContactError> {
    if numerator.is_zero() && denominator.is_zero() {
        return Err(ContactError::DegenerateRate);
    }
    let (a, b) = (pair.first(), pair.second());
    let va = a.generator().velocity(a.initial());
    let vb = b.generator().velocity(b.initial());
    Ok(va.scale(&Rat::from_integer(denominator.clone()))
        == vb.scale(&Rat::from_integer(numerator.clone())))
}

// -------------------------------------------------------------------------------------------
// the material

/// **The contact material** `w D` on the three slip coordinates, certified passive.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ContactMaterial {
    response: SymmetricForm,
    weight: Rat,
}

impl ContactMaterial {
    /// A material from a positive semidefinite response `D` and a nonnegative weight `w`. Both
    /// are decided exactly (the response by its inertia).
    pub fn new(response: SymmetricForm, weight: Rat) -> Result<Self, ContactError> {
        if response.extent() != 3 {
            return Err(ContactError::ResponseExtent {
                found: response.extent(),
            });
        }
        if inertia(&response).negative != 0 {
            return Err(ContactError::ResponseNotPassive);
        }
        if weight.is_negative() {
            return Err(ContactError::NegativeWeight { weight });
        }
        Ok(Self { response, weight })
    }

    pub fn response(&self) -> &SymmetricForm {
        &self.response
    }

    pub fn weight(&self) -> &Rat {
        &self.weight
    }

    /// The resistance `R = w D` as a matrix.
    fn resistance(&self) -> Result<ExactRatMatrix, ContactError> {
        Ok(ExactRatMatrix::shaped(
            3,
            3,
            (0..3)
                .map(|row| {
                    (0..3)
                        .map(|column| &self.weight * self.response.at(row, column))
                        .collect()
                })
                .collect(),
        )?)
    }

    /// **The contact form** `M = w JᵀDJ` over the slip map's columns.
    pub fn form(&self, slip: &ExactRatMatrix) -> Result<ExactRatMatrix, ContactError> {
        check_slip(slip)?;
        Ok(slip
            .transpose()?
            .multiply(&self.resistance()?)?
            .multiply(slip)?)
    }

    /// **The dissipated power** `P(u) = ⟨J u, w D J u⟩ = ⟨u, M u⟩ ≥ 0`.
    pub fn power(&self, slip: &ExactRatMatrix, rates: &[Rat]) -> Result<Rat, ContactError> {
        let flow = slip.apply(rates)?;
        let traction = self.resistance()?.apply(&flow)?;
        Ok(flow.iter().zip(&traction).map(|(f, e)| f * e).sum())
    }

    /// **The contact as the core resistive relation** `R = w D`, certified passive.
    pub fn element(&self) -> Result<ResistiveRelation, ContactError> {
        Ok(ResistiveRelation::new(self.resistance()?)?)
    }

    /// **The contact bond** at a rate: flow the slip `f = J u`, effort the traction `e = −w D f`.
    /// Its power is `−⟨u, M u⟩ ≤ 0`.
    pub fn bond(&self, slip: &ExactRatMatrix, rates: &[Rat]) -> Result<Bond, ContactError> {
        let flow = slip.apply(rates)?;
        let effort = self
            .resistance()?
            .apply(&flow)?
            .into_iter()
            .map(|value| -value)
            .collect();
        Ok(Bond::new(flow, effort)?)
    }

    /// The rates of zero power: `ker(wDJ)`, which contains the no-slip rates `ker J`. For `w > 0`
    /// it is `ker(DJ)`; a zero weight makes every rate silent.
    pub fn zero_power_kernel(&self, slip: &ExactRatMatrix) -> Result<Vec<Vec<Rat>>, ContactError> {
        Ok(self.resistance()?.multiply(slip)?.kernel_basis()?)
    }

    /// Whether zero power forces zero slip: the material is definite on the attainable slips,
    /// `rank(wDJ) = rank(J)`.
    pub fn definite_on_slips(&self, slip: &ExactRatMatrix) -> Result<bool, ContactError> {
        Ok(self.resistance()?.multiply(slip)?.rank()? == slip.rank()?)
    }
}

fn check_slip(slip: &ExactRatMatrix) -> Result<(), ContactError> {
    if slip.rows() == 3 {
        Ok(())
    } else {
        Err(ContactError::Shape {
            what: "slip map rows",
            expected: 3,
            found: slip.rows(),
        })
    }
}

/// **The assembled contact material** `M = Σ_f w_f J_fᵀ D_f J_f` over several faces sharing one
/// rate chart.
pub fn contact_material(
    faces: &[(ExactRatMatrix, ContactMaterial)],
) -> Result<ExactRatMatrix, ContactError> {
    let mut total: Option<ExactRatMatrix> = None;
    for (slip, material) in faces {
        let form = material.form(slip)?;
        total = Some(match total {
            None => form,
            Some(sum) => sum.add(&form)?,
        });
    }
    total.ok_or(ContactError::Shape {
        what: "contact faces",
        expected: 1,
        found: 0,
    })
}

// -------------------------------------------------------------------------------------------
// alignment

/// **The alignment of two velocities, undivided.** `cohere = ⟨a|b⟩²` and `turn = |a × b|²` over
/// the one denominator `|a|²|b|²`, with the hand `⟨a|b⟩` kept beside the square that erases it.
/// The faces close by Lagrange's identity, Lean `HolonicsResearch/Transport/Fold.lagrange_identity`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Alignment {
    pub cohere: Rat,
    pub turn: Rat,
    pub span: Rat,
    pub hand: Rat,
}

impl Alignment {
    pub fn of(a: &RatVec3, b: &RatVec3) -> Result<Self, ContactError> {
        let span = a.norm_squared() * b.norm_squared();
        if span.is_zero() {
            return Err(ContactError::NullVelocity);
        }
        let hand = a.dot(b);
        Ok(Self {
            cohere: &hand * &hand,
            turn: a.cross(b).norm_squared(),
            span,
            hand,
        })
    }

    /// The squared cosine as its presentation, `⟨a|b⟩² : |a|²|b|²`.
    pub fn cohering(&self) -> Presentation {
        Presentation::new(self.cohere.clone(), self.span.clone())
    }

    /// The squared sine as its presentation, `|a × b|² : |a|²|b|²`.
    pub fn turning(&self) -> Presentation {
        Presentation::new(self.turn.clone(), self.span.clone())
    }

    /// Lagrange's identity (`Transport/Fold.lagrange_identity`): the two faces close,
    /// `cohere + turn = span`.
    pub fn closes(&self) -> bool {
        &self.cohere + &self.turn == self.span
    }
}

// -------------------------------------------------------------------------------------------
// the serial chain

/// A closed interval of a joint's chart parameter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JointLimit {
    lower: Rat,
    upper: Rat,
}

impl JointLimit {
    pub fn new(lower: Rat, upper: Rat) -> Result<Self, ContactError> {
        if lower > upper {
            return Err(ContactError::InvalidLimit);
        }
        Ok(Self { lower, upper })
    }

    pub fn contains(&self, value: &Rat) -> bool {
        &self.lower <= value && value <= &self.upper
    }

    fn check(&self, parameter: &Rat) -> Result<(), ContactError> {
        if self.contains(parameter) {
            Ok(())
        } else {
            Err(ContactError::OutsideLimit {
                parameter: parameter.clone(),
                lower: self.lower.clone(),
                upper: self.upper.clone(),
            })
        }
    }
}

/// **The finite action of one joint.** A revolute joint is carried in the Cayley half-angle chart;
/// `rate` is the chart parameter's derivative along the declared clock, which
/// [`SerialChain::contact_slip`] reads.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JointMotion {
    Revolute {
        axis: Axis,
        pivot: RatVec3,
        parameter: Rat,
        rate: Rat,
    },
    Prismatic {
        axis: RatVec3,
        displacement: Rat,
        rate: Rat,
    },
}

impl JointMotion {
    pub fn parameter(&self) -> &Rat {
        match self {
            Self::Revolute { parameter, .. } => parameter,
            Self::Prismatic { displacement, .. } => displacement,
        }
    }

    /// The chart parameter's declared rate `ṫ`.
    pub fn rate(&self) -> &Rat {
        match self {
            Self::Revolute { rate, .. } | Self::Prismatic { rate, .. } => rate,
        }
    }

    /// The finite action at a chart parameter.
    pub fn map_at(&self, parameter: &Rat) -> AffineMap3 {
        match self {
            Self::Revolute { axis, pivot, .. } => {
                AffineMap3::rotation_about(pivot, axis.cayley_rotation(parameter))
            }
            Self::Prismatic { axis, .. } => AffineMap3 {
                linear: RatMat3::identity(),
                translation: axis.scale(parameter),
            },
        }
    }

    /// The finite action at the joint's own parameter.
    pub fn finite_map(&self) -> AffineMap3 {
        self.map_at(self.parameter())
    }

    /// **The Lie generator per unit chart parameter.** A Cayley parameter `t` turns at the
    /// angular rate `2/(1 + t²)` per unit `t`, about the axis through the pivot; a prismatic joint
    /// advances along its axis.
    pub fn parameter_generator(&self) -> ScrewGenerator {
        match self {
            Self::Revolute {
                axis,
                pivot,
                parameter,
                ..
            } => {
                let angular = axis
                    .unit()
                    .scale(&(integer(2) / (Rat::one() + parameter * parameter)));
                let advance = pivot.cross(&angular);
                ScrewGenerator::new(angular, advance)
            }
            Self::Prismatic { axis, .. } => ScrewGenerator::new(RatVec3::zero(), axis.clone()),
        }
    }
}

/// One situated screw and its admitted finite joint action.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SerialJoint {
    site: SituatedScrew,
    motion: JointMotion,
    limit: Option<JointLimit>,
}

impl SerialJoint {
    /// A joint whose situated generator is the parameter generator of its finite chart, at a
    /// parameter inside its limit.
    pub fn new(
        site: SituatedScrew,
        motion: JointMotion,
        limit: Option<JointLimit>,
    ) -> Result<Self, ContactError> {
        if let Some(limit) = &limit {
            limit.check(motion.parameter())?;
        }
        if site.generator() != &motion.parameter_generator() {
            return Err(ContactError::GeneratorMismatch);
        }
        Ok(Self {
            site,
            motion,
            limit,
        })
    }

    pub fn site(&self) -> &SituatedScrew {
        &self.site
    }

    pub fn motion(&self) -> &JointMotion {
        &self.motion
    }
}

/// An oriented contact between two link-local points; `orientation` points from the second link
/// toward the first.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinkContact {
    pub first_link: usize,
    pub second_link: usize,
    pub first_point: RatVec3,
    pub second_point: RatVec3,
    pub orientation: RatVec3,
}

/// The contact rows of a chain per unit joint parameter.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinkContactJacobian {
    /// The relative velocity `v_first − v_second` each joint's unit parameter rate produces.
    pub velocity_columns: Vec<RatVec3>,
    /// The oriented scalar row `orientation · (v_first − v_second)`.
    pub row: Vec<Rat>,
}

impl LinkContactJacobian {
    /// The slip map of the contact over the joint rates: a pair contact's `J` for the chain.
    pub fn slip(&self) -> Result<ExactRatMatrix, ContactError> {
        Ok(column_matrix(&self.velocity_columns)?)
    }

    /// Pull a contact force back to the joints: `Jᵀ F`.
    pub fn pullback_force(&self, force: &RatVec3) -> Vec<Rat> {
        self.velocity_columns
            .iter()
            .map(|column| column.dot(force))
            .collect()
    }
}

/// How a supplied candidate family meets a target endpoint.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Closure {
    Unique(Vec<Rat>),
    Plural(Vec<Vec<Rat>>),
    Null,
}

/// The endpoint family of an all-prismatic chain: the affine preimage `particular + span(kernel)`,
/// with the joint limits retained beside it.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrismaticEndpointFibre {
    pub particular: Vec<Rat>,
    pub kernel: Vec<Vec<Rat>>,
    limits: Vec<Option<JointLimit>>,
    source: ExactRatMatrix,
    target: Vec<Rat>,
}

impl PrismaticEndpointFibre {
    /// Whether a parameter vector reaches the target and lies inside every joint limit.
    pub fn admits(&self, parameters: &[Rat]) -> bool {
        parameters.len() == self.limits.len()
            && self
                .source
                .apply(parameters)
                .is_ok_and(|image| image == self.target)
            && self
                .limits
                .iter()
                .zip(parameters)
                .all(|(limit, value)| limit.as_ref().is_none_or(|limit| limit.contains(value)))
    }
}

/// **A serial chain**: an ordered product of proper rigid joint actions on a base frame.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SerialChain {
    base: AffineMap3,
    joints: Vec<SerialJoint>,
}

impl SerialChain {
    pub fn new(base: AffineMap3, joints: Vec<SerialJoint>) -> Result<Self, ContactError> {
        if !base.linear.is_special_orthogonal() {
            return Err(ContactError::NotProperRigid);
        }
        Ok(Self { base, joints })
    }

    pub fn joints(&self) -> &[SerialJoint] {
        &self.joints
    }

    /// One transform per link; link `i` includes joint `i` (Lean `serialPrefixes`).
    pub fn link_transforms(&self) -> Vec<AffineMap3> {
        let mut prefix = self.base.clone();
        self.joints
            .iter()
            .map(|joint| {
                prefix = joint.motion.finite_map().followed_by(&prefix);
                prefix.clone()
            })
            .collect()
    }

    /// The endpoint configuration (Lean `serialConfiguration`).
    pub fn endpoint(&self) -> AffineMap3 {
        self.endpoint_at(
            &self
                .joints
                .iter()
                .map(|joint| joint.motion.parameter().clone())
                .collect::<Vec<_>>(),
        )
        .expect("the chain's own parameters lie inside its limits")
    }

    /// The endpoint at declared joint parameters, each checked against its limit.
    pub fn endpoint_at(&self, parameters: &[Rat]) -> Result<AffineMap3, ContactError> {
        if parameters.len() != self.joints.len() {
            return Err(ContactError::Shape {
                what: "joint parameters",
                expected: self.joints.len(),
                found: parameters.len(),
            });
        }
        let mut prefix = self.base.clone();
        for (joint, parameter) in self.joints.iter().zip(parameters) {
            if let Some(limit) = &joint.limit {
                limit.check(parameter)?;
            }
            prefix = joint.motion.map_at(parameter).followed_by(&prefix);
        }
        Ok(prefix)
    }

    /// **The spatial Jacobian**: each joint's parameter generator recharted through the finite
    /// product preceding it.
    pub fn spatial_jacobian(&self) -> Result<Vec<ScrewGenerator>, ContactError> {
        let mut prefix = self.base.clone();
        let mut columns = Vec::with_capacity(self.joints.len());
        for joint in &self.joints {
            columns.push(
                joint
                    .site
                    .generator()
                    .rechart(&prefix)
                    .map_err(|_| ContactError::NotProperRigid)?,
            );
            prefix = joint.motion.finite_map().followed_by(&prefix);
        }
        Ok(columns)
    }

    /// **A contact between two links**, read through the Jacobian: joint `j` moves a link point
    /// only when the point's link lies at or after `j`.
    pub fn contact_jacobian(
        &self,
        contact: &LinkContact,
    ) -> Result<LinkContactJacobian, ContactError> {
        let transforms = self.link_transforms();
        let place = |link: usize, point: &RatVec3| {
            transforms
                .get(link)
                .map(|transform| transform.apply(point))
                .ok_or(ContactError::LinkOutside { link })
        };
        let first = place(contact.first_link, &contact.first_point)?;
        let second = place(contact.second_link, &contact.second_point)?;
        let mut velocity_columns = Vec::with_capacity(self.joints.len());
        let mut row = Vec::with_capacity(self.joints.len());
        for (joint, column) in self.spatial_jacobian()?.iter().enumerate() {
            let moving = |link: usize, point: &RatVec3| {
                if joint <= link {
                    column.velocity(point)
                } else {
                    RatVec3::zero()
                }
            };
            let relative =
                moving(contact.first_link, &first).subtract(&moving(contact.second_link, &second));
            row.push(contact.orientation.dot(&relative));
            velocity_columns.push(relative);
        }
        Ok(LinkContactJacobian {
            velocity_columns,
            row,
        })
    }

    /// **The contact's slip at the declared joint rates**: `Δ̇ = Σ_j ṫ_j (v_first − v_second)_j`,
    /// the contact Jacobian applied to the rates each joint carries.
    pub fn contact_slip(&self, contact: &LinkContact) -> Result<RatVec3, ContactError> {
        let jacobian = self.contact_jacobian(contact)?;
        Ok(jacobian
            .velocity_columns
            .iter()
            .zip(&self.joints)
            .fold(RatVec3::zero(), |slip, (column, joint)| {
                slip.add(&column.scale(joint.motion.rate()))
            }))
    }

    /// Compare a supplied candidate family with a target endpoint. The plural and null fibres
    /// are kept; no candidate is chosen by search.
    pub fn closure(
        &self,
        target: &AffineMap3,
        candidates: Vec<Vec<Rat>>,
    ) -> Result<Closure, ContactError> {
        let mut matching = Vec::new();
        for candidate in candidates {
            if &self.endpoint_at(&candidate)? == target {
                matching.push(candidate);
            }
        }
        Ok(match matching.len() {
            0 => Closure::Null,
            1 => Closure::Unique(matching.remove(0)),
            _ => Closure::Plural(matching),
        })
    }

    /// **The complete endpoint family of an all-prismatic chain**, through the exact affine
    /// preimage. `None` when the target is unreachable or a joint is revolute (a revolute chart is
    /// nonlinear and is never linearized here).
    pub fn prismatic_endpoint_fibre(
        &self,
        target: &AffineMap3,
    ) -> Result<Option<PrismaticEndpointFibre>, ContactError> {
        let mut axes = Vec::with_capacity(self.joints.len());
        for joint in &self.joints {
            match &joint.motion {
                JointMotion::Prismatic { axis, .. } => axes.push(self.base.linear.apply(axis)),
                JointMotion::Revolute { .. } => return Ok(None),
            }
        }
        if target.linear != self.base.linear {
            return Ok(None);
        }
        let source = column_matrix(&axes)?;
        let offset = target.translation.subtract(&self.base.translation);
        let goal = vec![offset.x, offset.y, offset.z];
        Ok(source
            .preimage_fibre(&goal)?
            .map(|(particular, kernel)| PrismaticEndpointFibre {
                particular,
                kernel,
                limits: self
                    .joints
                    .iter()
                    .map(|joint| joint.limit.clone())
                    .collect(),
                source,
                target: goal,
            }))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::geometry::rational_circle;
    use crate::ratio::rat;

    fn screw(angular: [i64; 3], advance: [i64; 3], at: [i64; 3]) -> SituatedScrew {
        SituatedScrew::new(
            ScrewGenerator::new(
                RatVec3::from_i64(angular[0], angular[1], angular[2]),
                RatVec3::from_i64(advance[0], advance[1], advance[2]),
            ),
            RatVec3::from_i64(at[0], at[1], at[2]),
        )
    }

    /// A rotated, translated base frame: a proper rigid motion that is not the identity.
    fn rotated_base() -> AffineMap3 {
        AffineMap3 {
            linear: Axis::X
                .cayley_rotation(&rat(1, 2))
                .multiply(&Axis::Z.cayley_rotation(&rat(-2, 3))),
            translation: RatVec3::from_i64(1, -2, 3),
        }
    }

    /// The Cayley chart's derivative in `t`, entry by entry by the quotient rule:
    /// `c′ = −4t/(1 + t²)²`, `s′ = 2(1 − t²)/(1 + t²)²`.
    fn cayley_derivative(axis: Axis, t: &Rat) -> RatMat3 {
        let spread = Rat::one() + t * t;
        let spread = &spread * &spread;
        let dc = -(integer(4) * t) / &spread;
        let ds = integer(2) * (Rat::one() - t * t) / &spread;
        let o = Rat::zero();
        match axis {
            Axis::X => RatMat3::new([
                [o.clone(), o.clone(), o.clone()],
                [o.clone(), dc.clone(), -ds.clone()],
                [o, ds, dc],
            ]),
            Axis::Y => RatMat3::new([
                [dc.clone(), o.clone(), ds.clone()],
                [o.clone(), o.clone(), o.clone()],
                [-ds, o, dc],
            ]),
            Axis::Z => RatMat3::new([
                [dc.clone(), -ds.clone(), o.clone()],
                [ds, dc, o.clone()],
                [o.clone(), o.clone(), o],
            ]),
        }
    }

    fn revolute(axis: Axis, pivot: RatVec3, parameter: Rat, rate: Rat) -> SerialJoint {
        let motion = JointMotion::Revolute {
            axis,
            pivot,
            parameter,
            rate,
        };
        SerialJoint::new(
            SituatedScrew::new(motion.parameter_generator(), RatVec3::zero()),
            motion,
            None,
        )
        .unwrap()
    }

    fn prismatic(axis: [i64; 3], limit: Option<JointLimit>) -> SerialJoint {
        let motion = JointMotion::Prismatic {
            axis: RatVec3::from_i64(axis[0], axis[1], axis[2]),
            displacement: Rat::zero(),
            rate: integer(1),
        };
        SerialJoint::new(
            SituatedScrew::new(motion.parameter_generator(), RatVec3::zero()),
            motion,
            limit,
        )
        .unwrap()
    }

    fn form(rows: &[[i64; 3]; 3]) -> SymmetricForm {
        SymmetricForm::from_rows(
            rows.iter()
                .map(|row| row.iter().map(|value| integer(*value)).collect())
                .collect(),
        )
        .unwrap()
    }

    /// Lean `pairSlip_mulVec`, `pairFeatureAt_gradient`, `pairQuadranceHessian`: the slip map reads
    /// the relative velocity, `DQ = 2JᵀΔ` and `D²Q = 2JᵀJ + 2 diag(Δ·a_a, −Δ·a_b)` agree exactly
    /// with the quadrance jet of the two generated curves.
    #[test]
    fn the_slip_map_carries_the_quadrance_gradient_and_hessian() {
        let pair = ScrewPair::new(
            screw([0, 0, 1], [0, 0, 2], [3, 1, 0]),
            screw([1, 0, 0], [0, 1, 0], [0, 2, -1]),
        );
        let contact = PairContact::of(pair);
        let rates = [rat(2, 3), integer(-5)];
        let slip = contact.slip().unwrap();
        let relative = contact.relative_velocity(&rates);
        assert_eq!(
            slip.apply(&rates).unwrap(),
            vec![relative.x.clone(), relative.y.clone(), relative.z.clone()]
        );
        assert_eq!(&contact.gradient().unwrap(), contact.jet().gradient());
        assert_eq!(&contact.hessian().unwrap(), contact.jet().hessian());
    }

    /// Lean `pairFeatureReturn_adjoint`: the complete return pairs with every rate exactly as the
    /// three feature covectors pair with the feature's variation.
    #[test]
    fn the_feature_return_is_the_adjoint_of_the_feature_variation() {
        let pair = ScrewPair::new(
            screw([0, 1, 0], [1, 0, 0], [1, 1, 1]),
            screw([0, 0, 2], [0, 0, 0], [2, 0, 1]),
        );
        let contact = PairContact::of(pair);
        let covector = FeatureCovector {
            delta: RatVec3::from_i64(1, -2, 3),
            quadrance: rat(1, 2),
            gradient: [integer(4), rat(-1, 3)],
        };
        let returned = contact.feature_pullback(&covector).unwrap();
        let u = [rat(3, 7), integer(2)];
        let slip = contact.slip().unwrap().apply(&u).unwrap();
        let gradient = contact.gradient().unwrap();
        let hessian = contact.hessian().unwrap();
        let forward = covector.delta.dot(&vector(&slip))
            + &covector.quadrance * (&gradient[0] * &u[0] + &gradient[1] * &u[1])
            + &covector.gradient[0] * (&hessian[0][0] * &u[0] + &hessian[0][1] * &u[1])
            + &covector.gradient[1] * (&hessian[1][0] * &u[0] + &hessian[1][1] * &u[1]);
        assert_eq!(forward, &returned[0] * &u[0] + &returned[1] * &u[1]);
    }

    /// Lean `pair_face_power`, `pair_face_power_eq_zero_iff_material_null` and
    /// `Holon/Conformance.pairContact_resistive`: `M = w JᵀDJ` is positive semidefinite, the power
    /// vanishes exactly on `ker(DJ)`, the contact bond draws `−⟨u, M u⟩`, and zero power forces no
    /// slip only when `D` is definite on the attainable slips.
    #[test]
    fn the_contact_material_is_passive_and_zero_power_is_material_null() {
        let pair = ScrewPair::new(
            screw([0, 0, 0], [1, 0, 0], [0, 0, 0]),
            screw([0, 0, 0], [0, 1, 0], [1, 0, 0]),
        );
        let slip = PairContact::of(pair).slip().unwrap();
        let blind =
            ContactMaterial::new(form(&[[1, 0, 0], [0, 0, 0], [0, 0, 1]]), integer(2)).unwrap();
        let definite =
            ContactMaterial::new(form(&[[2, 1, 0], [1, 2, 0], [0, 0, 1]]), integer(1)).unwrap();
        for material in [&blind, &definite] {
            let m = material.form(&slip).unwrap();
            let mform = SymmetricForm::from_rows(m.to_rows()).unwrap();
            assert_eq!(inertia(&mform).negative, 0);
            let u = vec![rat(1, 2), integer(3)];
            let power = material.power(&slip, &u).unwrap();
            assert!(!power.is_negative());
            assert_eq!(material.bond(&slip, &u).unwrap().power(), -power);
            for rate in material.zero_power_kernel(&slip).unwrap() {
                assert!(material.power(&slip, &rate).unwrap().is_zero());
            }
        }
        // The blind response cannot see the second object's slip: zero power without no-slip.
        assert!(!blind.definite_on_slips(&slip).unwrap());
        let silent = blind.zero_power_kernel(&slip).unwrap();
        assert_eq!(silent.len(), 1);
        assert!(!slip.apply(&silent[0]).unwrap().iter().all(Zero::is_zero));
        assert!(definite.definite_on_slips(&slip).unwrap());
        assert!(definite.zero_power_kernel(&slip).unwrap().is_empty());
        assert!(
            ContactMaterial::new(form(&[[1, 0, 0], [0, -1, 0], [0, 0, 1]]), integer(1)).is_err()
        );
    }

    /// Lean `lock_iff_zero_power` and `Geometry/PairResonance`: coaxial rotations at rates `1` and
    /// `2` lock exactly at `1/2`, addressed by its Stern–Brocot word whatever the signs that
    /// present it (`−1/−2` is the same lock); a counter-rotating pair locks at a signed ratio and a
    /// stationary relation keeps its own reading; `0/0` declares no ratio and is refused rather
    /// than read as a lock of every pair.
    #[test]
    fn a_lock_is_zero_slip_at_its_rate_ratio_and_carries_its_farey_address() {
        let big = |value: i64| BigInt::from(value);
        let pair = ScrewPair::new(
            screw([0, 0, 1], [0, 0, 0], [1, 0, 0]),
            screw([0, 0, 2], [0, 0, 0], [1, 0, 0]),
        );
        let contact = PairContact::of(pair);
        let LockReading::PositiveAddress(address) = contact.lock(&big(1), &big(2)).unwrap() else {
            panic!("coaxial rates 1 and 2 lock at 1/2");
        };
        assert_eq!(address.to_ratio().unwrap(), rat(1, 2));
        assert_eq!(address.period().unwrap(), BigInt::from(2));
        assert!(
            contact
                .relative_velocity(&[integer(2), integer(1)])
                .norm_squared()
                .is_zero()
        );
        assert_eq!(
            contact.lock(&big(-1), &big(-2)).unwrap(),
            LockReading::PositiveAddress(address)
        );
        assert_eq!(
            contact.lock(&big(1), &big(3)).unwrap(),
            LockReading::NotLocked
        );
        let counter = PairContact::of(ScrewPair::new(
            screw([0, 0, 1], [0, 0, 0], [1, 0, 0]),
            screw([0, 0, -2], [0, 0, 0], [1, 0, 0]),
        ));
        assert_eq!(
            counter.lock(&big(-1), &big(2)).unwrap(),
            LockReading::SignedOrStationary {
                numerator: big(-1),
                denominator: big(2),
            }
        );
        let resting = PairContact::of(ScrewPair::new(
            screw([0, 0, 0], [0, 0, 0], [0, 0, 0]),
            screw([0, 0, 0], [0, 0, 0], [1, 1, 1]),
        ));
        assert!(matches!(
            resting.lock(&big(0), &big(1)).unwrap(),
            LockReading::SignedOrStationary { .. }
        ));
        let unrelated = ScrewPair::new(
            screw([0, 0, 1], [0, 0, 2], [3, 1, 0]),
            screw([1, 0, 0], [0, 1, 0], [0, 2, -1]),
        );
        assert_eq!(
            pair_lock(&unrelated, &big(0), &big(0)),
            Err(ContactError::DegenerateRate)
        );
        assert_eq!(
            PairContact::of(unrelated).lock(&big(0), &big(0)),
            Err(ContactError::DegenerateRate)
        );
        assert_eq!(
            resting.lock(&big(0), &big(0)),
            Err(ContactError::DegenerateRate)
        );
    }

    /// Lagrange's identity: the cohering and turning faces of two velocities close over one
    /// denominator; parallel velocities turn by nothing and keep their hand.
    #[test]
    fn the_alignment_faces_close_by_lagranges_identity() {
        let a = RatVec3::from_i64(1, 2, -2);
        let b = RatVec3::from_i64(3, 0, 4);
        let alignment = Alignment::of(&a, &b).unwrap();
        assert!(alignment.closes());
        assert_eq!(alignment.cohering().quotient(), Some(rat(25, 225)));
        let opposed = Alignment::of(&a, &a.scale(&integer(-3))).unwrap();
        assert!(opposed.turn.is_zero() && opposed.hand.is_negative() && opposed.closes());
        assert_eq!(
            Alignment::of(&a, &RatVec3::zero()),
            Err(ContactError::NullVelocity)
        );
    }

    /// No Lean counterpart; obligation #62 (continuous chain derivative). A revolute joint's
    /// Jacobian column is the derivative of its Cayley chart. At parameter `t` the rotation's
    /// entries have derivatives
    /// `c′ = −(2/(1+t²)) s`, `s′ = (2/(1+t²)) c`, and the column's velocity at a link point equals
    /// that derivative applied to the point's rest position, exactly.
    #[test]
    fn a_revolute_column_is_the_derivative_of_its_cayley_chart() {
        let t = rat(1, 3);
        let motion = JointMotion::Revolute {
            axis: Axis::Z,
            pivot: RatVec3::zero(),
            parameter: t.clone(),
            rate: integer(1),
        };
        let site = SituatedScrew::new(motion.parameter_generator(), RatVec3::zero());
        let chain = SerialChain::new(
            AffineMap3::identity(),
            vec![SerialJoint::new(site, motion, None).unwrap()],
        )
        .unwrap();
        let rest = RatVec3::from_i64(2, 1, 5);
        let moved = chain.link_transforms()[0].apply(&rest);
        let velocity = chain.spatial_jacobian().unwrap()[0].velocity(&moved);
        let (c, s) = rational_circle(&t);
        let rate = integer(2) / (Rat::one() + &t * &t);
        let (dc, ds) = (-(&rate * &s), &rate * &c);
        let expected = RatVec3::new(
            &dc * &rest.x - &ds * &rest.y,
            &ds * &rest.x + &dc * &rest.y,
            Rat::zero(),
        );
        assert_eq!(velocity, expected);
        let jacobian = chain
            .contact_jacobian(&LinkContact {
                first_link: 0,
                second_link: 0,
                first_point: rest.clone(),
                second_point: RatVec3::zero(),
                orientation: RatVec3::from_i64(1, 0, 0),
            })
            .unwrap();
        assert_eq!(jacobian.row, vec![expected.x.clone()]);
        assert_eq!(
            jacobian.pullback_force(&RatVec3::from_i64(1, 0, 0)),
            jacobian.row
        );
    }

    /// No Lean counterpart; obligation #62 (continuous chain derivative). Two revolute joints with
    /// off-origin pivots on a rotated, translated base `B`: each spatial Jacobian column, read at
    /// the moved point, is the exact product-rule derivative of the endpoint `B·M₁(t₁)·M₂(t₂)·p`
    /// with `M_i x = R_i(t_i)(x − c_i) + c_i`, namely `∂₁ = B·R₁′(t₁)(M₂p − c₁)` and
    /// `∂₂ = B·R₁(t₁)R₂′(t₂)(p − c₂)`, where `R′` is the quotient-rule derivative of the Cayley
    /// chart (independent of the `2/(1 + t²)` angular rate the generator carries). A contact from
    /// the tip to a point `q` on the first link reads `∂₁ − B·R₁′(t₁)(q − c₁)` and `∂₂`, and at the
    /// declared joint rates its slip is their rate-weighted sum.
    #[test]
    fn two_revolute_columns_are_the_product_rule_derivative_of_the_chain() {
        let base = rotated_base();
        let (t1, t2) = (rat(1, 3), rat(-3, 2));
        let (c1, c2) = (RatVec3::from_i64(1, 2, 0), RatVec3::from_i64(0, -1, 2));
        let (r1, r2) = (integer(2), rat(-1, 5));
        let chain = SerialChain::new(
            base.clone(),
            vec![
                revolute(Axis::Z, c1.clone(), t1.clone(), r1.clone()),
                revolute(Axis::Y, c2.clone(), t2.clone(), r2.clone()),
            ],
        )
        .unwrap();
        let p = RatVec3::from_i64(3, -1, 4);
        let m2 = chain.joints()[1].motion().finite_map();
        let first = base
            .linear
            .apply(&cayley_derivative(Axis::Z, &t1).apply(&m2.apply(&p).subtract(&c1)));
        let second = base
            .linear
            .multiply(&Axis::Z.cayley_rotation(&t1))
            .apply(&cayley_derivative(Axis::Y, &t2).apply(&p.subtract(&c2)));
        let moved = chain.link_transforms()[1].apply(&p);
        assert_eq!(moved, chain.endpoint().apply(&p));
        let columns = chain.spatial_jacobian().unwrap();
        assert_eq!(columns[0].velocity(&moved), first);
        assert_eq!(columns[1].velocity(&moved), second);

        let q = RatVec3::from_i64(-2, 0, 1);
        let contact = LinkContact {
            first_link: 1,
            second_link: 0,
            first_point: p.clone(),
            second_point: q.clone(),
            orientation: RatVec3::from_i64(1, 1, -1),
        };
        let on_first_link = base
            .linear
            .apply(&cayley_derivative(Axis::Z, &t1).apply(&q.subtract(&c1)));
        let expected = vec![first.subtract(&on_first_link), second];
        let jacobian = chain.contact_jacobian(&contact).unwrap();
        assert_eq!(jacobian.velocity_columns, expected);
        assert_eq!(
            jacobian.row,
            expected
                .iter()
                .map(|column| contact.orientation.dot(column))
                .collect::<Vec<_>>()
        );
        let slip = expected[0].scale(&r1).add(&expected[1].scale(&r2));
        assert_eq!(chain.contact_slip(&contact).unwrap(), slip);
        assert_eq!(
            jacobian.slip().unwrap().apply(&[r1, r2]).unwrap(),
            vec![slip.x, slip.y, slip.z]
        );
    }

    /// An all-prismatic chain's endpoint family is the exact affine preimage: two parallel axes
    /// leave a one-dimensional fibre, and the joint limits decide which members are admitted.
    #[test]
    fn a_prismatic_chain_returns_its_complete_endpoint_fibre() {
        let chain = SerialChain::new(
            AffineMap3::identity(),
            vec![
                prismatic(
                    [1, 0, 0],
                    Some(JointLimit::new(integer(0), integer(2)).unwrap()),
                ),
                prismatic([2, 0, 0], None),
                prismatic([0, 1, 0], None),
            ],
        )
        .unwrap();
        let target = AffineMap3 {
            linear: RatMat3::identity(),
            translation: RatVec3::from_i64(4, 3, 0),
        };
        let fibre = chain
            .prismatic_endpoint_fibre(&target)
            .unwrap()
            .expect("reachable");
        assert_eq!(fibre.kernel.len(), 1);
        assert!(fibre.admits(&[integer(2), integer(1), integer(3)]));
        assert!(!fibre.admits(&[integer(4), integer(0), integer(3)]));
        assert_eq!(
            chain
                .closure(
                    &target,
                    vec![
                        vec![integer(2), integer(1), integer(3)],
                        vec![integer(0), integer(2), integer(3)]
                    ]
                )
                .unwrap(),
            Closure::Plural(vec![
                vec![integer(2), integer(1), integer(3)],
                vec![integer(0), integer(2), integer(3)]
            ])
        );
        let unreachable = AffineMap3 {
            linear: RatMat3::identity(),
            translation: RatVec3::from_i64(0, 0, 1),
        };
        assert_eq!(chain.prismatic_endpoint_fibre(&unreachable).unwrap(), None);
    }

    /// Under a rotated, translated base the prismatic axes act through the base's rotation, so the
    /// fibre is the preimage of `Bᵀ(target − b)`: three axes spanning a plane leave a
    /// one-dimensional fibre, every admitted member reaches the target, and the same local
    /// displacement read without the rotation is unreachable.
    #[test]
    fn a_prismatic_fibre_reads_its_axes_through_a_rotated_base() {
        let base = rotated_base();
        let chain = SerialChain::new(
            base.clone(),
            vec![
                prismatic([1, 0, 0], None),
                prismatic([0, 1, 0], None),
                prismatic([1, 1, 0], None),
            ],
        )
        .unwrap();
        let local = RatVec3::from_i64(2, 3, 0);
        let target = AffineMap3 {
            linear: base.linear.clone(),
            translation: base.linear.apply(&local).add(&base.translation),
        };
        let fibre = chain
            .prismatic_endpoint_fibre(&target)
            .unwrap()
            .expect("reachable");
        assert_eq!(fibre.kernel.len(), 1);
        for member in [
            vec![integer(2), integer(3), integer(0)],
            vec![integer(0), integer(1), integer(2)],
            vec![rat(1, 2), rat(3, 2), rat(3, 2)],
        ] {
            assert!(fibre.admits(&member));
            assert_eq!(chain.endpoint_at(&member).unwrap(), target);
        }
        assert!(!fibre.admits(&[integer(3), integer(3), integer(0)]));
        let unrotated = AffineMap3 {
            linear: base.linear.clone(),
            translation: local.add(&base.translation),
        };
        assert_eq!(chain.prismatic_endpoint_fibre(&unrotated).unwrap(), None);
    }
}
