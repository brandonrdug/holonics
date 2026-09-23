//! Exact rational kinematics for an ordered family of situated screws.
//!
//! A joint's finite action and its infinitesimal generator are kept together.  In particular, a
//! Cayley parameter is a half-angle coordinate: if `t` is the parameter and `t_dot` its clock
//! rate, the angular rate is `2*t_dot/(1+t^2)`.  The module therefore refuses an arbitrary proper
//! rigid matrix carrying an unrelated phase label.  It does not exponentiate a rational screw.
//!
//! The chain is an ordered product of the supplied affine actions.  Its spatial Jacobian is
//! obtained by recharting each site's generator through the preceding finite product.  Contact
//! rows are derived from those columns and retain their orientation; their pullback is the
//! transpose in the declared Euclidean pairing.

use crate::exact_linear::ExactRatMatrix;
use crate::holonic_interaction::{ContactFace, CoreClock, InteractionRefusal};
use crate::inertia::SymmetricForm;
use num_traits::One;
use relational_geometry::{
    AffineMap3, HingeAxis, Rat, RatVec3, RationalPhase, ScrewGenerator, SituatedScrew,
};
use thiserror::Error;

fn axis_vector(axis: HingeAxis) -> RatVec3 {
    match axis {
        HingeAxis::X => RatVec3::from_i64(1, 0, 0),
        HingeAxis::Y => RatVec3::from_i64(0, 1, 0),
        HingeAxis::Z => RatVec3::from_i64(0, 0, 1),
    }
}

fn scale_generator(generator: &ScrewGenerator, scalar: &Rat) -> ScrewGenerator {
    ScrewGenerator::new(
        generator.angular().scale(scalar),
        generator.advance().scale(scalar),
    )
}

/// Wire/version marker for the serial kinematics packet.
pub const SERIAL_CHAIN_SCHEMA: &str = "holonic-engine.holonic-chain.serial.v1";
pub const SERIAL_JOINT_CEILING: usize = 1024;
pub const CLOSURE_CANDIDATE_CEILING: usize = 4096;

/// A joint-local clock.  Its coordinate is the chart parameter, while `rate` is its derivative
/// with respect to the declared physical/model clock.  It is intentionally separate from source
/// occurrence and from the chain's refinement coordinate.
///
/// [definition; agent-inferred] **A derived chart of the one clock.** The clock is the core
/// [`CoreClock`] (step `h`, tick odometer); a joint clock is the affine chart
/// `coordinate = origin + rate · elapsed`, `elapsed = h · ticks` ([`CoreClock::elapsed`]), read at
/// one clock reading. [`Self::on_clock`] forms it and [`Self::origin_on`] inverts it, so
/// `JointClock::on_clock(c, JointClock::origin_on(j, c), j.rate()) == j` for every reading `c`.
/// For a revolute joint the coordinate is the Cayley half-angle parameter, so a constant
/// `rate` is a constant parameter rate, not a constant turn rate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JointClock {
    coordinate: Rat,
    rate: Rat,
}

impl JointClock {
    pub fn new(coordinate: Rat, rate: Rat) -> Self {
        Self { coordinate, rate }
    }

    /// The joint chart at the core clock's reading: `origin + rate · elapsed`.
    pub fn on_clock(clock: &CoreClock, origin: Rat, rate: Rat) -> Self {
        let coordinate = origin + &rate * clock.elapsed();
        Self { coordinate, rate }
    }

    /// The chart origin (the coordinate at the clock's rest) given the clock reading this joint
    /// clock was read at: `coordinate − rate · elapsed`.
    pub fn origin_on(&self, clock: &CoreClock) -> Rat {
        &self.coordinate - &self.rate * clock.elapsed()
    }

    pub fn coordinate(&self) -> &Rat {
        &self.coordinate
    }

    pub fn rate(&self) -> &Rat {
        &self.rate
    }
}

/// A closed interval in the joint's declared parameter chart.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JointLimit {
    lower: Rat,
    upper: Rat,
}

impl JointLimit {
    pub fn new(lower: Rat, upper: Rat) -> Result<Self, SerialError> {
        if lower > upper {
            return Err(SerialError::InvalidLimit { lower, upper });
        }
        Ok(Self { lower, upper })
    }

    pub fn lower(&self) -> &Rat {
        &self.lower
    }

    pub fn upper(&self) -> &Rat {
        &self.upper
    }

    pub fn contains(&self, value: &Rat) -> bool {
        &self.lower <= value && value <= &self.upper
    }
}

/// Exact finite action of one joint.  `parameter_rate` and `rate` are derivatives with respect
/// to the joint's declared physical/model clock, not turn rates hidden in a phase label.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum JointMotion {
    Revolute {
        axis: HingeAxis,
        pivot: RatVec3,
        parameter: Rat,
        parameter_rate: Rat,
        clock: JointClock,
        extra_turns: i64,
    },
    Prismatic {
        axis: RatVec3,
        displacement: Rat,
        rate: Rat,
        clock: JointClock,
    },
}

impl JointMotion {
    pub fn revolute(axis: HingeAxis, pivot: RatVec3, parameter: Rat, parameter_rate: Rat) -> Self {
        Self::Revolute {
            axis,
            pivot,
            parameter: parameter.clone(),
            parameter_rate: parameter_rate.clone(),
            clock: JointClock::new(parameter, parameter_rate),
            extra_turns: 0,
        }
    }

    pub fn prismatic(axis: RatVec3, displacement: Rat, rate: Rat) -> Self {
        Self::Prismatic {
            axis,
            displacement: displacement.clone(),
            rate: rate.clone(),
            clock: JointClock::new(displacement, rate),
        }
    }

    pub fn parameter(&self) -> &Rat {
        match self {
            Self::Revolute { parameter, .. } => parameter,
            Self::Prismatic { displacement, .. } => displacement,
        }
    }

    pub fn clock(&self) -> &JointClock {
        match self {
            Self::Revolute { clock, .. } | Self::Prismatic { clock, .. } => clock,
        }
    }

    /// Retain an explicit lift without claiming that the Cayley point closes after any period.
    pub fn with_extra_turns(mut self, extra_turns: i64) -> Self {
        if let Self::Revolute {
            extra_turns: turns, ..
        } = &mut self
        {
            *turns = extra_turns;
        }
        self
    }

    pub fn phase(&self) -> Option<RationalPhase> {
        match self {
            Self::Revolute {
                parameter,
                extra_turns,
                ..
            } => Some(RationalPhase::new(parameter.clone(), *extra_turns)),
            Self::Prismatic { .. } => None,
        }
    }

    /// The exact finite action in the joint's local chart.
    pub fn finite_map(&self) -> AffineMap3 {
        match self {
            Self::Revolute {
                axis,
                pivot,
                parameter,
                ..
            } => AffineMap3::rotation_about(pivot, axis.rotation(parameter)),
            Self::Prismatic {
                axis, displacement, ..
            } => AffineMap3 {
                linear: relational_geometry::RatMat3::identity(),
                translation: axis.scale(displacement),
            },
        }
    }

    /// Generator per unit change of the joint chart coordinate.
    pub fn parameter_generator(&self) -> ScrewGenerator {
        match self {
            Self::Revolute {
                axis,
                pivot,
                parameter,
                ..
            } => {
                let denominator = Rat::one() + parameter * parameter;
                let angular =
                    axis_vector(*axis).scale(&(Rat::from_integer(2.into()) / denominator));
                let advance = angular.cross(pivot).scale(&-Rat::one());
                ScrewGenerator::new(angular, advance)
            }
            Self::Prismatic { axis, .. } => ScrewGenerator::new(RatVec3::zero(), axis.clone()),
        }
    }

    /// Generator per unit physical/model clock.  The clock rate is intentionally applied here,
    /// outside the spatial parameter Jacobian.
    pub fn generator(&self) -> ScrewGenerator {
        scale_generator(&self.parameter_generator(), self.clock().rate())
    }

    pub fn clock_generator(&self) -> ScrewGenerator {
        self.generator()
    }

    /// Exact finite action with a replacement chart coordinate.  The supplied coordinate is
    /// checked by the chain's limits before this operation is used for endpoint inference.
    pub fn map_at_parameter(&self, parameter: &Rat) -> AffineMap3 {
        match self {
            Self::Revolute { axis, pivot, .. } => {
                AffineMap3::rotation_about(pivot, axis.rotation(parameter))
            }
            Self::Prismatic { axis, .. } => AffineMap3 {
                linear: relational_geometry::RatMat3::identity(),
                translation: axis.scale(parameter),
            },
        }
    }

    pub fn is_revolute(&self) -> bool {
        matches!(self, Self::Revolute { .. })
    }
}

/// One situated generator and its admitted finite joint action.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SerialJoint {
    site: SituatedScrew,
    motion: JointMotion,
    limit: Option<JointLimit>,
}

impl SerialJoint {
    pub fn new(
        site: SituatedScrew,
        motion: JointMotion,
        limit: Option<JointLimit>,
    ) -> Result<Self, SerialError> {
        let clock_matches = match &motion {
            JointMotion::Revolute {
                parameter,
                parameter_rate,
                clock,
                ..
            } => clock.coordinate() == parameter && clock.rate() == parameter_rate,
            JointMotion::Prismatic {
                displacement,
                rate,
                clock,
                ..
            } => clock.coordinate() == displacement && clock.rate() == rate,
        };
        if !clock_matches {
            return Err(SerialError::ClockMismatch);
        }
        if let Some(limit) = &limit {
            if !limit.contains(motion.parameter()) {
                return Err(SerialError::OutsideLimit {
                    parameter: motion.parameter().clone(),
                    lower: limit.lower.clone(),
                    upper: limit.upper.clone(),
                });
            }
        }
        let expected = motion.parameter_generator();
        if site.generator() != &expected {
            return Err(SerialError::GeneratorMismatch {
                expected,
                supplied: site.generator().clone(),
            });
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

    pub fn limit(&self) -> Option<&JointLimit> {
        self.limit.as_ref()
    }

    pub fn finite_map(&self) -> AffineMap3 {
        self.motion.finite_map()
    }
}

/// An externally supplied endpoint candidate.  Keeping candidates explicit is deliberate: this
/// packet does not claim to solve a nonlinear inverse-kinematics problem from a target face.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ClosureCandidate {
    pub parameters: Vec<Rat>,
}

/// Exact result of comparing a supplied candidate family with a target endpoint.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ClosureFamily {
    Unique {
        candidate: ClosureCandidate,
        correction: AffineMap3,
    },
    Plural {
        candidates: Vec<ClosureCandidate>,
        target: AffineMap3,
    },
    Null {
        target: AffineMap3,
        retained_candidates: Vec<ClosureCandidate>,
    },
}

/// An oriented contact between two link-local points.  `orientation` points from the second link
/// toward the first; a positive scalar row therefore means separating motion in that direction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinkContact {
    pub first_link: usize,
    pub second_link: usize,
    pub first_point: RatVec3,
    pub second_point: RatVec3,
    pub orientation: RatVec3,
}

/// Contact Jacobian per unit joint parameter and its Euclidean covector pullback.
/// Supply the actual parameter rates for a physical/model clock once when evaluating slip
/// or power; these columns have not already been multiplied by JointClock::rate.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinkContactJacobian {
    contact: LinkContact,
    first_link: usize,
    second_link: usize,
    orientation: RatVec3,
    /// Full relative velocity columns before the oriented scalar receiver.
    velocity_columns: Vec<RatVec3>,
    /// Oriented scalar contact row, `orientation · (v_first-v_second)`.
    row: Vec<Rat>,
}

/// An ambient affine preimage intersected with the retained joint limits. The linear
/// fibre may be nonempty while that constrained intersection is empty; `admits` checks
/// a candidate against both the endpoint equation and every limit. The ambient fibre is the
/// core [`AffineFibre`](holonic_core::restriction::AffineFibre) (plan phase 10).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PrismaticEndpointFibre {
    fibre: holonic_core::restriction::AffineFibre,
    limits: Vec<Option<JointLimit>>,
    source: ExactRatMatrix,
    target: Vec<Rat>,
}

impl PrismaticEndpointFibre {
    pub fn particular(&self) -> &[Rat] {
        &self.fibre.particular
    }

    pub fn kernel(&self) -> &[Vec<Rat>] {
        &self.fibre.radical
    }

    /// The ambient affine preimage, before the joint limits.
    pub fn affine_fibre(&self) -> &holonic_core::restriction::AffineFibre {
        &self.fibre
    }

    pub fn limits(&self) -> &[Option<JointLimit>] {
        &self.limits
    }

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
                .all(|(limit, parameter)| {
                    limit
                        .as_ref()
                        .map_or(true, |limit| limit.contains(parameter))
                })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PrismaticEndpointInference {
    Fibre(PrismaticEndpointFibre),
    UnsupportedNonlinearJoint,
    Empty,
}

impl LinkContactJacobian {
    pub fn source(&self) -> &LinkContact {
        &self.contact
    }
    pub fn first_link(&self) -> usize {
        self.first_link
    }
    pub fn second_link(&self) -> usize {
        self.second_link
    }
    pub fn orientation(&self) -> &RatVec3 {
        &self.orientation
    }
    pub fn velocity_columns(&self) -> &[RatVec3] {
        &self.velocity_columns
    }
    pub fn row(&self) -> &[Rat] {
        &self.row
    }

    pub fn pullback(&self, contact_covector: &Rat) -> Vec<Rat> {
        self.row
            .iter()
            .map(|entry| entry * contact_covector)
            .collect()
    }

    pub fn pullback_force(&self, force: &RatVec3) -> Vec<Rat> {
        self.velocity_columns
            .iter()
            .map(|column| column.dot(force))
            .collect()
    }

    /// Build one material face over the complete relative velocity map. The three rows are the
    /// oriented pair's spatial slip coordinates; all joint columns enter one quadratic form, so
    /// cross-joint terms in `Jᵀ D J` are retained.
    pub fn contact_face(
        &self,
        lineage: impl Into<String>,
        response: SymmetricForm,
        weight: Rat,
    ) -> Result<ContactFace, SerialError> {
        let columns = self.velocity_columns.len();
        let slip = ExactRatMatrix::shaped(
            3,
            columns,
            (0..3)
                .map(|row| {
                    self.velocity_columns
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
        .map_err(|error| SerialError::Linear(error.to_string()))?;
        ContactFace::declared(lineage, slip, response, weight)
            .map_err(|error: InteractionRefusal| SerialError::Contact(error.to_string()))
    }
}

/// An ordered serial product of proper rigid joint actions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SerialChain {
    base: AffineMap3,
    joints: Vec<SerialJoint>,
}

impl SerialChain {
    pub fn new(base: AffineMap3, joints: Vec<SerialJoint>) -> Result<Self, SerialError> {
        if !base.linear.is_special_orthogonal() {
            return Err(SerialError::NotProperRigidFrame);
        }
        if joints.len() > SERIAL_JOINT_CEILING {
            return Err(SerialError::TooLarge {
                what: "serial joint population",
                limit: SERIAL_JOINT_CEILING,
                actual: joints.len(),
            });
        }
        Ok(Self { base, joints })
    }

    pub fn base(&self) -> &AffineMap3 {
        &self.base
    }

    pub fn joints(&self) -> &[SerialJoint] {
        &self.joints
    }

    /// One transform per link, where link `i` includes joint `i`.
    pub fn link_transforms(&self) -> Vec<AffineMap3> {
        let mut prefix = self.base.clone();
        let mut transforms = Vec::with_capacity(self.joints.len());
        for joint in &self.joints {
            prefix = joint.finite_map().followed_by(&prefix);
            transforms.push(prefix.clone());
        }
        transforms
    }

    pub fn endpoint(&self) -> AffineMap3 {
        self.link_transforms()
            .last()
            .cloned()
            .unwrap_or_else(|| self.base.clone())
    }

    /// The exact rigid map that returns the endpoint frame to the base frame.
    pub fn endpoint_inverse(&self) -> Result<AffineMap3, SerialError> {
        self.endpoint()
            .inverse()
            .ok_or(SerialError::SingularEndpoint)
    }

    fn endpoint_for_parameters(&self, parameters: &[Rat]) -> Result<AffineMap3, SerialError> {
        if parameters.len() != self.joints.len() {
            return Err(SerialError::ParameterWidth {
                expected: self.joints.len(),
                supplied: parameters.len(),
            });
        }
        let mut prefix = self.base.clone();
        for (joint, parameter) in self.joints.iter().zip(parameters) {
            if let Some(limit) = joint.limit() {
                if !limit.contains(parameter) {
                    return Err(SerialError::OutsideLimit {
                        parameter: parameter.clone(),
                        lower: limit.lower.clone(),
                        upper: limit.upper.clone(),
                    });
                }
            }
            prefix = joint
                .motion
                .map_at_parameter(parameter)
                .followed_by(&prefix);
        }
        Ok(prefix)
    }

    /// Spatial Jacobian columns, in joint order.  A column is the site's local generator
    /// transported through the finite product preceding that site.
    pub fn spatial_jacobian(&self) -> Result<Vec<ScrewGenerator>, SerialError> {
        let mut prefix = self.base.clone();
        let mut columns = Vec::with_capacity(self.joints.len());
        for joint in &self.joints {
            columns.push(
                joint
                    .site
                    .generator()
                    .rechart(&prefix)
                    .map_err(|_| SerialError::NotProperRigidFrame)?,
            );
            prefix = joint.finite_map().followed_by(&prefix);
        }
        Ok(columns)
    }

    /// Spatial columns multiplied by the declared physical/model clock rates.
    pub fn spatial_velocity_jacobian(&self) -> Result<Vec<ScrewGenerator>, SerialError> {
        let mut prefix = self.base.clone();
        let mut columns = Vec::with_capacity(self.joints.len());
        for joint in &self.joints {
            let column = joint
                .site
                .generator()
                .rechart(&prefix)
                .map_err(|_| SerialError::NotProperRigidFrame)?;
            columns.push(scale_generator(&column, joint.motion.clock().rate()));
            prefix = joint.finite_map().followed_by(&prefix);
        }
        Ok(columns)
    }

    /// Solve only the declared endpoint comparison.  A caller that has an admissible inverse
    /// family supplies its exact candidates; this method preserves plural and null fibres rather
    /// than choosing one by an unlicensed numerical search.
    pub fn closure_control(
        &self,
        target: AffineMap3,
        candidates: Vec<ClosureCandidate>,
    ) -> Result<ClosureFamily, SerialError> {
        if !target.linear.is_special_orthogonal() {
            return Err(SerialError::NotProperRigidFrame);
        }
        if candidates.len() > CLOSURE_CANDIDATE_CEILING {
            return Err(SerialError::TooLarge {
                what: "closure candidate population",
                limit: CLOSURE_CANDIDATE_CEILING,
                actual: candidates.len(),
            });
        }
        let mut evaluated = Vec::with_capacity(candidates.len());
        for candidate in candidates {
            let endpoint = self.endpoint_for_parameters(&candidate.parameters)?;
            evaluated.push((candidate, endpoint));
        }
        let matching: Vec<_> = evaluated
            .iter()
            .filter(|(_, endpoint)| *endpoint == target)
            .map(|(candidate, _)| candidate.clone())
            .collect();
        match matching.len() {
            1 => {
                let candidate = matching.into_iter().next().expect("one candidate");
                let endpoint = self.endpoint_for_parameters(&candidate.parameters)?;
                let correction = endpoint
                    .inverse()
                    .ok_or(SerialError::SingularEndpoint)?
                    .followed_by(&target);
                Ok(ClosureFamily::Unique {
                    candidate,
                    correction,
                })
            }
            n if n > 1 => Ok(ClosureFamily::Plural {
                candidates: matching,
                target,
            }),
            _ => Ok(ClosureFamily::Null {
                target,
                retained_candidates: evaluated
                    .into_iter()
                    .map(|(candidate, _)| candidate)
                    .collect(),
            }),
        }
    }

    /// Residual correction `C` such that `C ∘ endpoint = target` under the affine owner’s
    /// right-action convention.
    pub fn endpoint_residual(&self, target: &AffineMap3) -> Result<AffineMap3, SerialError> {
        if !target.linear.is_special_orthogonal() {
            return Err(SerialError::NotProperRigidFrame);
        }
        Ok(self.endpoint_inverse()?.followed_by(target))
    }

    /// Infer the complete all-prismatic endpoint family through the shared exact linear preimage
    /// owner. Revolute charts return a typed unsupported-domain result; their bounded phase
    /// families remain explicit `ClosureCandidate`s and are never replaced by a linearized solve.
    pub fn prismatic_endpoint_fibre(
        &self,
        target: &AffineMap3,
    ) -> Result<PrismaticEndpointInference, SerialError> {
        if !target.linear.is_special_orthogonal() {
            return Err(SerialError::NotProperRigidFrame);
        }
        if self.joints.iter().any(|joint| joint.motion.is_revolute()) {
            return Ok(PrismaticEndpointInference::UnsupportedNonlinearJoint);
        }
        if target.linear != self.base.linear {
            return Ok(PrismaticEndpointInference::Empty);
        }
        let columns: Vec<RatVec3> = self
            .joints
            .iter()
            .map(|joint| {
                self.base.linear.apply(match &joint.motion {
                    JointMotion::Prismatic { axis, .. } => axis,
                    JointMotion::Revolute { .. } => unreachable!("revolute joints were filtered"),
                })
            })
            .collect();
        let rows = (0..3)
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
            .collect();
        let matrix = ExactRatMatrix::shaped(3, columns.len(), rows)
            .map_err(|error| SerialError::Linear(error.to_string()))?;
        let target_translation = target.translation.subtract(&self.base.translation);
        let target_vector = vec![
            target_translation.x,
            target_translation.y,
            target_translation.z,
        ];
        let Some(fibre) = matrix
            .affine_fibre(&target_vector)
            .map_err(|error| SerialError::Linear(error.to_string()))?
        else {
            return Ok(PrismaticEndpointInference::Empty);
        };
        Ok(PrismaticEndpointInference::Fibre(PrismaticEndpointFibre {
            fibre,
            limits: self
                .joints
                .iter()
                .map(|joint| joint.limit.clone())
                .collect(),
            source: matrix,
            target: target_vector,
        }))
    }

    pub fn link_point(&self, link: usize, point: &RatVec3) -> Result<RatVec3, SerialError> {
        self.link_transforms()
            .get(link)
            .ok_or(SerialError::LinkOutOfBounds { link })
            .map(|transform| transform.apply(point))
    }

    pub fn contact_jacobian(
        &self,
        contact: &LinkContact,
    ) -> Result<LinkContactJacobian, SerialError> {
        let transforms = self.link_transforms();
        if contact.first_link >= transforms.len() {
            return Err(SerialError::LinkOutOfBounds {
                link: contact.first_link,
            });
        }
        if contact.second_link >= transforms.len() {
            return Err(SerialError::LinkOutOfBounds {
                link: contact.second_link,
            });
        }
        let first_world = transforms[contact.first_link].apply(&contact.first_point);
        let second_world = transforms[contact.second_link].apply(&contact.second_point);
        let columns = self.spatial_jacobian()?;
        let mut velocity_columns = Vec::with_capacity(columns.len());
        let mut row = Vec::with_capacity(columns.len());
        for (joint, column) in columns.iter().enumerate() {
            let first = if joint <= contact.first_link {
                column.velocity(&first_world)
            } else {
                RatVec3::zero()
            };
            let second = if joint <= contact.second_link {
                column.velocity(&second_world)
            } else {
                RatVec3::zero()
            };
            let relative = first.subtract(&second);
            row.push(contact.orientation.dot(&relative));
            velocity_columns.push(relative);
        }
        Ok(LinkContactJacobian {
            contact: contact.clone(),
            first_link: contact.first_link,
            second_link: contact.second_link,
            orientation: contact.orientation.clone(),
            velocity_columns,
            row,
        })
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum SerialError {
    #[error("serial base/action must be a proper rigid frame")]
    NotProperRigidFrame,
    #[error("joint limit is inverted: {lower} > {upper}")]
    InvalidLimit { lower: Rat, upper: Rat },
    #[error("joint parameter {parameter} lies outside [{lower}, {upper}]")]
    OutsideLimit {
        parameter: Rat,
        lower: Rat,
        upper: Rat,
    },
    #[error("joint chart and retained clock disagree")]
    ClockMismatch,
    #[error("parameter vector has width {supplied}; expected {expected}")]
    ParameterWidth { expected: usize, supplied: usize },
    #[error("finite joint chart generator does not match its situated generator")]
    GeneratorMismatch {
        expected: ScrewGenerator,
        supplied: ScrewGenerator,
    },
    #[error("the endpoint affine map has no exact inverse")]
    SingularEndpoint,
    #[error("link index {link} is outside the serial chain")]
    LinkOutOfBounds { link: usize },
    #[error("exact linear endpoint inference failed: {0}")]
    Linear(String),
    #[error("serial contact face refused: {0}")]
    Contact(String),
    #[error("{what} has size {actual}, exceeding declared limit {limit}")]
    TooLarge {
        what: &'static str,
        limit: usize,
        actual: usize,
    },
}

#[cfg(test)]
#[path = "serial/tests.rs"]
mod tests;
