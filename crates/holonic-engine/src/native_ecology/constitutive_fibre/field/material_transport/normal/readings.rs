//! **Readings of the normal Holon, in one module** (plan phase 9, receive facet).
//!
//! [definition] A reading is a coholon's face of the Holon: a passive reading of an effort at
//! zero power (`Holon/Law.lean::passive_reading`; `holonic_core::law::receiver`). These are the
//! host faces every normal receiver returns — the constitution's objective and per-observation
//! report, the wave state's word reading, the one passage reading, the codec faces of the basis
//! receivers (selection, score, projected family), the anchored family receiver, and the coupled
//! comparison and joint readings. The receivers that produce them (`NormalWaveBasisChart`,
//! `NormalWaveBasisFace`, `NormalFamilyBasisFace`, `NormalSectionBasisFace`,
//! `NormalWaveFamilyReceiver`) are device receiver faces kept beside their kernels; each
//! declares its core element with `receiver_element()`.
use super::*;

#[derive(Debug, Serialize)]
pub struct NativeNormalMaterialReading {
    pub forward: NativeFieldCurrentBall,
    pub observed: NativeFieldCurrentBall,
    pub contemporary_source_forward: Option<NativeFieldCurrentBall>,
    pub returned_difference: Option<NativeFieldCurrentBall>,
    pub chronological_current: Option<NativeFieldCurrentBall>,
    pub contemporary_difference: Option<NativeFieldCurrentBall>,
    pub source_current: Option<NativeFieldCurrentBall>,
    pub coefficient_error: Rat,
    pub normal_residual_upper: Rat,
    pub coefficient_norm_upper: Rat,
    pub source_normal_error_upper: Rat,
    pub cross_source_error_upper: Rat,
    pub increments: [Rat; 4],
}

/// Cold objective comparison in the unit-prior source chart. This describes the observed
/// geometry, not language quality or a unique source selected from the retained family.
#[derive(Debug, Serialize)]
pub struct NativeNormalMaterialObjective {
    pub nominal_data_term: Rat,
    pub prior_term: Rat,
    pub nominal_regularized_objective: Rat,
    pub normal_residual_squared: Rat,
    /// H >= I implies 0 <= Phi(M) - min Phi <= ||M H - B||_F^2 / 2.
    pub solve_gap_upper: Rat,
    pub nominal_minimum: crate::ExactInterval,
    /// Bounds at the stored numerical M over every admitted observed-source/target family.
    pub family_data_term: crate::ExactInterval,
    pub family_regularized_objective: crate::ExactInterval,
    /// Minimum for each admitted source geometry, including its unit prior.
    pub family_minimum: crate::ExactInterval,
}

#[derive(Debug, Serialize)]
pub struct NormalWaveReading {
    pub transport: NormalWaveTransport,
    pub steps: u64,
    pub maximum_computed_power_norm: Rat,
    pub uniform_power_equation_defect: Rat,
    pub operator_word_error: Rat,
    pub joint_current: NativeFieldCurrentBall,
}

/// Which motion produced a [`NormalWavePassage`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum NormalPassageKind {
    /// A source word of learned joined passages acting on the held joint (`actuate_section`).
    Actuate,
    /// Material development from a measured source/target section (`develop_section`).
    Develop,
    /// An actual next current received in the generator's receiver chart (`receive`).
    Receive,
    /// A read-only normal-reference continuation from the held joint (`reference_next`).
    Reference,
    /// The one-cut pullback of a pending prediction at the contemporary constitution.
    Pullback,
    /// A change of the future operator-family transport (`set_transport`).
    Transport,
}

/// The one reading of a passage.
#[derive(Debug, Serialize)]
pub struct NormalWavePassageReading {
    pub kind: NormalPassageKind,
    pub prediction_id: Option<u64>,
    /// The epoch of the joint the passage read.
    pub producing_epoch: u64,
    /// Transport of the constitution the passage was read at.
    pub producing_transport: NormalWaveTransport,
    pub epoch: u64,
    pub successor_transport: NormalWaveTransport,
    pub source_joint: Option<NativeFieldCurrentBall>,
    pub produced_joint: Option<NativeFieldCurrentBall>,
    /// The resident normal report of a reception or pullback.
    pub comparison: Option<NativeNormalMaterialReading>,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct NormalBasisSelection {
    pub selected: usize,
    pub selected_coordinate: usize,
    pub centre_score: Rat,
    pub centre_ties: usize,
    pub score_radius: Rat,
    /// Strict interval separation for this finite receiver; never source uniqueness.
    pub robust: bool,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct NormalBasisScore {
    pub centre: Rat,
    pub lower: Rat,
    pub upper: Rat,
}

#[derive(Debug, Serialize)]
pub struct NormalWaveBasisReading {
    pub epoch: Option<u64>,
    pub transport: NormalWaveTransport,
    pub coordinates: Vec<usize>,
    pub selection: NormalBasisSelection,
    pub scores: Vec<NormalBasisScore>,
}

#[derive(Clone, Debug, Serialize, PartialEq, Eq)]
pub struct FamilyBasisSelection {
    pub selected: usize,
    pub selected_coordinate: usize,
    pub projected_score: Rat,
    pub projected_ties: usize,
}

#[derive(Debug, Serialize)]
pub struct FamilyBasisReading {
    pub epoch: u64,
    pub selection: FamilyBasisSelection,
    pub coordinates: Vec<usize>,
    pub projected_scores: Vec<Rat>,
    /// These flags witness unbounded variation at fixed anchor. False does not establish
    /// constancy over the anchor ball, or a robust winning symbol for the whole family.
    pub anchor_independent_free: Vec<bool>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
pub enum NormalFamilySupport {
    Supported,
    EmptyAffineRelation,
    OutsideAnchorBall,
}

#[derive(Debug, Serialize)]
pub struct NormalFamilyReceiverReading {
    pub support: NormalFamilySupport,
    /// The projection of the ball centre onto the affine anchor domain, when that domain exists.
    pub nearest_anchor: Option<Vec<Rat>>,
    /// A declared minimum-norm joint receiver at nearest_anchor, only for supported families.
    pub projected_joint: Option<Vec<Rat>>,
    pub anchor_difference: Option<Vec<Rat>>,
    /// Nonzero coordinates of directions at fixed anchor. False does not imply a constant
    /// coordinate over the full ball; those coordinates can still vary with the anchor.
    pub anchor_independent_free: Vec<bool>,
    /// Every frame has (lambda, anchor, p, c). The first lambda/anchor are reported above;
    /// later copies remain in projected_joint so shared-frame constraints are not discarded.
    pub state_width: usize,
    pub state_count: usize,
}
impl NormalFamilyReceiverReading {
    /// The p,c coordinates at one state in this SAME joint projection, not separately
    /// projected marginal optima. The complete affine family remains on the native receiver.
    pub fn projected_state(&self, state: usize) -> Option<&[Rat]> {
        if state >= self.state_count {
            return None;
        }
        let width = self.state_width.checked_sub(2)? / 2;
        let start = state.checked_mul(self.state_width)?;
        self.projected_joint
            .as_ref()?
            .get(start..start.checked_add(width)?)
    }
}

#[derive(Debug, Serialize, PartialEq, Eq)]
pub struct NormalFamilyComparisonRow {
    /// None is the affine origin; Some(i) is the original source's i-th generator coefficient.
    pub source_direction: Option<usize>,
    pub features: Vec<Rat>,
    pub observed_difference: Vec<Rat>,
}

#[derive(Debug, Serialize, PartialEq, Eq)]
pub struct CoupledJointReading {
    pub relation_residual: Vec<Rat>,
    pub producing_condition_residual: Vec<Rat>,
    pub anchor_difference: Vec<Rat>,
    pub within_anchor: bool,
}
