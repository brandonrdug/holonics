//! The finite transport ecology induced by a receiver/history quotient.
//!
//! [`crate::receiver_exact_compression`] finds the coarsest partition which no declared receiver
//! and admitted successor history can separate.  This owner returns the consequence that turns
//! that partition into a native codec rather than a class list:
//!
//! ```text
//!                         T_i
//!                    X --------> X
//!                    |            |
//!                  q |            | q
//!                    v            v
//!                    Q --------> Q
//!                         U_i
//! ```
//!
//! Every square is checked on the complete source population.  Ordered-word exactness is then an
//! executable induction over those squares, not a replay campaign.  Decoding opens only the
//! declared receiver image and returns the complete source fibre; it never chooses an inverse of a
//! non-injective quotient.

use std::collections::BTreeSet;

use num_traits::Zero;
use holonics::geometry::Rat;
use holonics::geometry::{AffineMap3, PairFiniteMotion, RationalPhaseError, ScrewPair};
use serde::{Deserialize, Serialize};
use thiserror::Error;

use holonics::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::factored_moment::FactoredMomentError;
use holonics::receiver::native::{InputId, NativeStateId, NativeTransport, Observation, ReceiverFactor, ReceiverId};
use crate::receiver_exact_compression::{CollapsedPair, ItemId};

/// The quotient map `q : X -> Q`, exhibited at every source occurrence.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QuotientAssignment {
    pub source: ItemId,
    pub native: NativeStateId,
}

holonics::fibre_field_names!(pub ReconstructionFibreNames = "ReconstructionFibre", "native", "sources", allow);

/// One complete source fibre `q⁻¹(native)`: the core
/// [`PreimageFibre`](holonics::restriction::PreimageFibre) under its `native`/`sources` wire
/// (plan phase 10). This is what an exterior decoder must retain instead of silently choosing a
/// source occurrence.
pub type ReconstructionFibre = holonics::restriction::PreimageFibre<
    NativeStateId,
    BTreeSet<ItemId>,
    ReconstructionFibreNames,
>;

/// One entry of a source generator `T_i`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceTransport {
    pub from: ItemId,
    pub to: ItemId,
}

/// A complete commuting generator square.  `source` and `native` are total functions over their
/// respective declared populations; construction refuses a terminus rather than hiding it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GeneratorSquare {
    pub generator: InputId,
    pub source: Vec<SourceTransport>,
    pub native: Vec<NativeTransport>,
}

/// Exact semantic work used to found the native rest.  These are populations of exact relation
/// reads, not elapsed-time estimates.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverHistoryWork {
    pub quotient_assignments: u64,
    pub receiver_factor_reads: u64,
    pub source_transport_reads: u64,
    pub native_transport_entries: u64,
    pub generator_square_checks: u64,
}

/// The executable result of decoding one native state at one declared receiver.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DecodedReceiverImage {
    pub native: NativeStateId,
    pub receiver: ReceiverId,
    pub observation: Observation,
    pub reconstruction_fibre: BTreeSet<ItemId>,
}

/// An executable witness of `q(T_w x) = U_w(q x)` for one arbitrary ordered word.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct OrderedWordConsequence {
    pub source_start: ItemId,
    pub native_start: NativeStateId,
    pub word: Vec<InputId>,
    pub source_end: ItemId,
    pub encoded_source_end: NativeStateId,
    pub native_end: NativeStateId,
}

impl OrderedWordConsequence {
    pub fn commutes(&self) -> bool {
        self.encoded_source_end == self.native_end
    }
}

/// The complete finite native action founded by a receiver/history quotient.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverHistoryCompression {
    pub schema: String,
    pub source_population: Vec<ItemId>,
    pub native_population: Vec<NativeStateId>,
    pub quotient: Vec<QuotientAssignment>,
    pub receiver_factors: Vec<ReceiverFactor>,
    pub generators: Vec<GeneratorSquare>,
    pub reconstruction_fibres: Vec<ReconstructionFibre>,
    /// Pairs a present-only quotient would have collapsed, with their first separating word.
    pub first_separators: Vec<CollapsedPair>,
    pub construction_work: ReceiverHistoryWork,
}

/// The exact invariant receiver span of one quadratic moment field.  Receiver forms are pulled
/// backward through every admitted generator until their rational span closes.  Coordinates on
/// that span are the hot quotient; the exhibited kernel is the complete covariance fibre which no
/// admitted receiver/history can see.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObservableMomentReceiverHistoryCompression {
    pub schema: String,
    pub factor_population: usize,
    pub basis_forms: Vec<ExactRatMatrix>,
    /// One row per original founded receiver, expressed on `basis_forms`.
    pub present_receiver_factors: ExactRatMatrix,
    /// For each generator, one square operator on observable coordinates.
    pub descended_generator_actions: Vec<ExactRatMatrix>,
    /// A basis of covariance directions annihilated by the complete observable coordinate map.
    pub reconstruction_kernel_basis: Vec<Vec<Rat>>,
}

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum ObservableMomentCompressionError {
    #[error("the observable moment family is empty or has a malformed common factor chart")]
    Shape,
    #[error("the requested receiver or generator lies outside the founded family")]
    Address,
    #[error("the addressed receiver population exceeds its exact finite wire")]
    Extent,
    #[error("the invariant receiver span failed to return an exact coordinate factor")]
    Factorization,
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
    #[error(transparent)]
    FactoredMoment(#[from] FactoredMomentError),
    #[error("phase chart error: {0}")]
    Phase(String),
}

/// The result of decoding one receiver from the observable moment coordinates. The kernel is
/// returned with the face: a receiver value never licenses choosing one hidden pair current.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObservableMomentReceiverDecode {
    pub coordinates: Vec<Rat>,
    pub value: Rat,
    /// The ambient linear moment fibre. It is not a list of physically realizable screw pairs.
    pub ambient_reconstruction_kernel_basis: Vec<Vec<Rat>>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ObservableMomentSeparatorScope {
    AmbientLinearMoment,
}

/// A concrete `E_next T = U E` check for one admitted finite motion.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HelicalMomentTransport {
    pub motion: usize,
    pub word: Vec<usize>,
    pub source_coordinates: Vec<Rat>,
    pub direct_coordinates: Vec<Rat>,
    pub descended_coordinates: Vec<Rat>,
}

impl HelicalMomentTransport {
    pub fn commutes(&self) -> bool {
        self.direct_coordinates == self.descended_coordinates
    }
}

/// A changed receiver that the founded span cannot factor. `kernel_direction` is an explicit
/// hidden moment direction on which this receiver changes, so it is a separator rather than a
/// mere rank diagnostic.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObservableMomentReceiverSeparator {
    pub scope: ObservableMomentSeparatorScope,
    pub receiver_form: ExactRatMatrix,
    /// An ambient matrix direction; rank-one, symmetry, homogeneous and clock constraints are
    /// deliberately not inferred from this separator.
    pub ambient_kernel_direction: Vec<Rat>,
    pub receiver_change: Rat,
}

/// Constraints retained beside the ambient moment fibre for a situated screw pair.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct HelicalMomentAdmissibility {
    pub symmetric_rank_one: bool,
    pub homogeneous_coordinates_fixed: bool,
    /// No common source clock was supplied to this caller, so this remains false.
    pub source_clock_constraints_declared: bool,
}

/// Exact phase reading for a supplied finite word. Closure is checked on the finite affine map;
/// the optional winding and Cayley parameter come from the caller's existing phase chart.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum HelicalPhaseClosure {
    Closed {
        period: usize,
        parameter: Option<Rat>,
        /// Declared extra full turns per elementary Cayley passage.
        declared_winding: Option<i64>,
        polygon_winding: Option<i64>,
        /// Polygon winding plus `period * declared_winding`.
        winding: Option<i64>,
    },
    NonClosing {
        period: usize,
        parameter: Option<Rat>,
        /// Retained only as a declaration; no polygon winding exists at a nonclosed period.
        declared_winding: Option<i64>,
        polygon_winding: Option<i64>,
        winding: Option<i64>,
    },
}

/// The actual screw-pair caller for the existing observable moment encoder and descended action.
/// The pair's affine homogeneous current is encoded once, while every supplied finite motion is
/// checked through the same receiver-history compression and can be reused as an ordered word.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct HelicalMomentReuse {
    pub compression: ObservableMomentReceiverHistoryCompression,
    pub initial_moment: ExactRatMatrix,
    pub receiver: ExactRatMatrix,
    pub initial_coordinates: Vec<Rat>,
    pub initial_decode: ObservableMomentReceiverDecode,
    pub moment_admissibility: HelicalMomentAdmissibility,
    pub motions: Vec<PairFiniteMotion>,
    pub transports: Vec<HelicalMomentTransport>,
    pub phase_closures: Vec<Option<HelicalPhaseClosure>>,
}

impl ObservableMomentReceiverHistoryCompression {
    /// Close a declared quadratic receiver family under exact backward generator action.  The
    /// derived span dimension is determined by the forms and actions; no rank aperture is supplied.
    pub fn found(
        receiver_forms: Vec<ExactRatMatrix>,
        generators: Vec<ExactRatMatrix>,
    ) -> Result<Self, ObservableMomentCompressionError> {
        let factor_population = receiver_forms
            .first()
            .map(ExactRatMatrix::rows)
            .unwrap_or(0);
        if factor_population == 0
            || receiver_forms.is_empty()
            || generators.is_empty()
            || receiver_forms
                .iter()
                .any(|form| form.rows() != factor_population || form.columns() != factor_population)
            || generators.iter().any(|generator| {
                generator.rows() != factor_population || generator.columns() != factor_population
            })
        {
            return Err(ObservableMomentCompressionError::Shape);
        }

        let ambient = factor_population
            .checked_mul(factor_population)
            .ok_or(ObservableMomentCompressionError::Shape)?;
        let coordinates_in = |basis: &[ExactRatMatrix], candidate: &ExactRatMatrix| {
            coordinates_in_form_span(ambient, basis, candidate)
        };
        let mut basis_forms = Vec::<ExactRatMatrix>::new();
        let admit = |basis: &mut Vec<ExactRatMatrix>,
                     candidate: ExactRatMatrix|
         -> Result<bool, ObservableMomentCompressionError> {
            if candidate.entries().iter().all(num_traits::Zero::is_zero)
                || coordinates_in(basis, &candidate)?.is_some()
            {
                return Ok(false);
            }
            basis.push(candidate);
            Ok(true)
        };
        for receiver in &receiver_forms {
            admit(&mut basis_forms, receiver.clone())?;
        }
        if basis_forms.is_empty() {
            return Err(ObservableMomentCompressionError::Shape);
        }
        let mut cursor = 0;
        while cursor < basis_forms.len() {
            let form = basis_forms[cursor].clone();
            for generator in &generators {
                let pulled = generator
                    .transpose()?
                    .multiply(&form)?
                    .multiply(generator)?;
                admit(&mut basis_forms, pulled)?;
            }
            cursor += 1;
        }

        let present_receiver_factors = ExactRatMatrix::new(
            receiver_forms
                .iter()
                .map(|receiver| {
                    coordinates_in(&basis_forms, receiver)?
                        .ok_or(ObservableMomentCompressionError::Factorization)
                })
                .collect::<Result<Vec<_>, _>>()?,
        )?;
        let descended_generator_actions = generators
            .iter()
            .map(|generator| {
                ExactRatMatrix::new(
                    basis_forms
                        .iter()
                        .map(|form| {
                            let pulled =
                                generator.transpose()?.multiply(form)?.multiply(generator)?;
                            coordinates_in(&basis_forms, &pulled)?
                                .ok_or(ObservableMomentCompressionError::Factorization)
                        })
                        .collect::<Result<Vec<_>, ObservableMomentCompressionError>>()?,
                )
                .map_err(ObservableMomentCompressionError::from)
            })
            .collect::<Result<Vec<_>, _>>()?;
        let quotient_matrix = ExactRatMatrix::new(
            basis_forms
                .iter()
                .map(|form| form.entries().to_vec())
                .collect(),
        )?;
        let reconstruction_kernel_basis = quotient_matrix.kernel_basis()?;
        Ok(Self {
            schema: "holonic-engine.observable-moment-receiver-history-compression.v1".to_owned(),
            factor_population,
            basis_forms,
            present_receiver_factors,
            descended_generator_actions,
            reconstruction_kernel_basis,
        })
    }

    /// Return the complete observable coordinate section `q(C)`.
    pub fn quotient(
        &self,
        moment: &ExactRatMatrix,
    ) -> Result<Vec<Rat>, ObservableMomentCompressionError> {
        if moment.rows() != self.factor_population || moment.columns() != self.factor_population {
            return Err(ObservableMomentCompressionError::Shape);
        }
        Ok(self
            .basis_forms
            .iter()
            .map(|form| contract_exact_forms(form, moment))
            .collect())
    }

    pub fn present_receiver(
        &self,
        receiver: usize,
        coordinates: &[Rat],
    ) -> Result<Rat, ObservableMomentCompressionError> {
        self.present_receiver_factors
            .row(receiver)
            .map_err(|_| ObservableMomentCompressionError::Address)
            .and_then(|factor| exact_dot(factor, coordinates))
    }

    pub fn transport_quotient(
        &self,
        generator: usize,
        coordinates: &[Rat],
    ) -> Result<Vec<Rat>, ObservableMomentCompressionError> {
        self.descended_generator_actions
            .get(generator)
            .ok_or(ObservableMomentCompressionError::Address)?
            .apply(coordinates)
            .map_err(ObservableMomentCompressionError::from)
    }

    /// Decode a present receiver and retain the complete unresolved moment fibre.
    pub fn decode_receiver(
        &self,
        receiver: usize,
        moment: &ExactRatMatrix,
    ) -> Result<ObservableMomentReceiverDecode, ObservableMomentCompressionError> {
        let coordinates = self.quotient(moment)?;
        let value = self.present_receiver(receiver, &coordinates)?;
        Ok(ObservableMomentReceiverDecode {
            coordinates,
            value,
            ambient_reconstruction_kernel_basis: self.reconstruction_kernel_basis.clone(),
        })
    }

    /// Return a concrete separator when a changed receiver lies outside the founded observable
    /// span. An in-span receiver returns `None` because its factor is already available.
    pub fn receiver_separator(
        &self,
        receiver: &ExactRatMatrix,
    ) -> Result<Option<ObservableMomentReceiverSeparator>, ObservableMomentCompressionError> {
        let ambient = self
            .factor_population
            .checked_mul(self.factor_population)
            .ok_or(ObservableMomentCompressionError::Shape)?;
        if receiver.rows() != self.factor_population || receiver.columns() != self.factor_population
        {
            return Err(ObservableMomentCompressionError::Shape);
        }
        if coordinates_in_form_span(ambient, &self.basis_forms, receiver)?.is_some() {
            return Ok(None);
        }
        for kernel_direction in &self.reconstruction_kernel_basis {
            let receiver_change = exact_dot(receiver.entries(), kernel_direction)?;
            if !receiver_change.is_zero() {
                return Ok(Some(ObservableMomentReceiverSeparator {
                    scope: ObservableMomentSeparatorScope::AmbientLinearMoment,
                    receiver_form: receiver.clone(),
                    ambient_kernel_direction: kernel_direction.clone(),
                    receiver_change,
                }));
            }
        }
        // A receiver outside the span must separate its quotient kernel. This branch names a
        // malformed factorization instead of silently returning an empty witness.
        Err(ObservableMomentCompressionError::Factorization)
    }
}

impl HelicalMomentReuse {
    /// Found the pair quadrance receiver and all supplied exact finite motions in one existing
    /// observable moment history. Affine translations are represented by homogeneous coordinates;
    /// no infinitesimal-to-finite approximation is introduced.
    pub fn found(
        pair: &ScrewPair,
        motions: Vec<PairFiniteMotion>,
        phase_periods: &[Option<usize>],
    ) -> Result<Self, ObservableMomentCompressionError> {
        if motions.is_empty() || phase_periods.len() != motions.len() {
            return Err(ObservableMomentCompressionError::Shape);
        }
        let receiver = pair_quadrance_receiver()?;
        let generators = motions
            .iter()
            .map(pair_motion_matrix)
            .collect::<Result<Vec<_>, _>>()?;
        let compression =
            ObservableMomentReceiverHistoryCompression::found(vec![receiver.clone()], generators)?;
        let initial_moment = pair_homogeneous_moment(pair)?;
        let initial_coordinates = compression.quotient(&initial_moment)?;
        let initial_decode = compression.decode_receiver(0, &initial_moment)?;
        let moment_admissibility = HelicalMomentAdmissibility {
            symmetric_rank_one: true,
            homogeneous_coordinates_fixed: true,
            source_clock_constraints_declared: false,
        };
        let mut transports = Vec::with_capacity(motions.len());
        let mut phase_closures = Vec::with_capacity(motions.len());
        for (motion_index, (motion, period)) in motions.iter().zip(phase_periods).enumerate() {
            let matrix = pair_motion_matrix(motion)?;
            let transported = transport_moment(&matrix, &initial_moment)?;
            let direct_coordinates = compression.quotient(&transported)?;
            let descended_coordinates =
                compression.transport_quotient(motion_index, &initial_coordinates)?;
            transports.push(HelicalMomentTransport {
                motion: motion_index,
                word: vec![motion_index],
                source_coordinates: initial_coordinates.clone(),
                direct_coordinates,
                descended_coordinates,
            });
            let phase_closure = if let Some(period) = period.as_ref() {
                let period = *period;
                let phase = motion.phase();
                let phase_winding = phase
                    .map(|phase| phase.lifted_winding(period))
                    .transpose()
                    .map_err(|error: RationalPhaseError| {
                        ObservableMomentCompressionError::Phase(error.to_string())
                    })?;
                let polygon_winding = phase
                    .map(|phase| phase.chart_winding(period).map(i64::from))
                    .transpose()
                    .map_err(|error: RationalPhaseError| {
                        ObservableMomentCompressionError::Phase(error.to_string())
                    })?;
                if motion.closes_after(period) {
                    Some(HelicalPhaseClosure::Closed {
                        period,
                        parameter: phase.map(|phase| phase.parameter().clone()),
                        declared_winding: phase.map(|phase| phase.winding()),
                        polygon_winding,
                        winding: phase_winding.map(|reading| reading.lifted),
                    })
                } else {
                    Some(HelicalPhaseClosure::NonClosing {
                        period,
                        parameter: phase.map(|phase| phase.parameter().clone()),
                        declared_winding: phase.map(|phase| phase.winding()),
                        polygon_winding: None,
                        winding: None,
                    })
                }
            } else {
                None
            };
            phase_closures.push(phase_closure);
        }
        Ok(Self {
            compression,
            initial_moment,
            receiver,
            initial_coordinates,
            initial_decode,
            moment_admissibility,
            motions,
            transports,
            phase_closures,
        })
    }

    pub fn decode(
        &self,
        receiver: usize,
        moment: &ExactRatMatrix,
    ) -> Result<ObservableMomentReceiverDecode, ObservableMomentCompressionError> {
        self.compression.decode_receiver(receiver, moment)
    }

    /// Reuse the descended actions for a nontrivial ordered word and compare them with direct
    /// affine transport of the original moment. This is the executable commuting square for the
    /// word, rather than a second compression algorithm.
    pub fn ordered_word(
        &self,
        word: &[usize],
    ) -> Result<HelicalMomentTransport, ObservableMomentCompressionError> {
        if word.is_empty() {
            return Err(ObservableMomentCompressionError::Address);
        }
        let mut composed = self
            .motions
            .get(word[0])
            .ok_or(ObservableMomentCompressionError::Address)?
            .clone();
        let mut descended = self.initial_coordinates.clone();
        for (position, index) in word.iter().enumerate() {
            let motion = self
                .motions
                .get(*index)
                .ok_or(ObservableMomentCompressionError::Address)?;
            if position > 0 {
                composed = composed.followed_by(motion);
            }
            descended = self.compression.transport_quotient(*index, &descended)?;
        }
        let composed_matrix = pair_motion_matrix(&composed)?;
        let transported = transport_moment(&composed_matrix, &self.initial_moment)?;
        let direct = self.compression.quotient(&transported)?;
        Ok(HelicalMomentTransport {
            motion: word[0],
            word: word.to_vec(),
            source_coordinates: self.initial_coordinates.clone(),
            direct_coordinates: direct,
            descended_coordinates: descended,
        })
    }

    pub fn changed_receiver_separator(
        &self,
        receiver: &ExactRatMatrix,
    ) -> Result<Option<ObservableMomentReceiverSeparator>, ObservableMomentCompressionError> {
        self.compression.receiver_separator(receiver)
    }
}

fn pair_homogeneous_current(pair: &ScrewPair) -> Vec<Rat> {
    let current = pair.initial_current();
    current
        .into_iter()
        .take(3)
        .chain(std::iter::once(Rat::from_integer(1.into())))
        .chain(pair.initial_current().into_iter().skip(3))
        .chain(std::iter::once(Rat::from_integer(1.into())))
        .collect()
}

fn pair_homogeneous_moment(
    pair: &ScrewPair,
) -> Result<ExactRatMatrix, ObservableMomentCompressionError> {
    let current = pair_homogeneous_current(pair);
    ExactRatMatrix::new(
        current
            .iter()
            .map(|left| current.iter().map(|right| left * right).collect())
            .collect(),
    )
    .map_err(ObservableMomentCompressionError::from)
}

fn pair_quadrance_receiver() -> Result<ExactRatMatrix, ObservableMomentCompressionError> {
    let mut receiver = vec![vec![Rat::from_integer(0.into()); 8]; 8];
    for index in 0..3 {
        receiver[index][index] = Rat::from_integer(1.into());
        receiver[index][index + 4] = Rat::from_integer((-1).into());
        receiver[index + 4][index] = Rat::from_integer((-1).into());
        receiver[index + 4][index + 4] = Rat::from_integer(1.into());
    }
    ExactRatMatrix::new(receiver).map_err(ObservableMomentCompressionError::from)
}

fn affine_homogeneous(map: &AffineMap3) -> [[Rat; 4]; 4] {
    [
        [
            map.linear.rows[0][0].clone(),
            map.linear.rows[0][1].clone(),
            map.linear.rows[0][2].clone(),
            map.translation.x.clone(),
        ],
        [
            map.linear.rows[1][0].clone(),
            map.linear.rows[1][1].clone(),
            map.linear.rows[1][2].clone(),
            map.translation.y.clone(),
        ],
        [
            map.linear.rows[2][0].clone(),
            map.linear.rows[2][1].clone(),
            map.linear.rows[2][2].clone(),
            map.translation.z.clone(),
        ],
        [
            Rat::from_integer(0.into()),
            Rat::from_integer(0.into()),
            Rat::from_integer(0.into()),
            Rat::from_integer(1.into()),
        ],
    ]
}

fn pair_motion_matrix(
    motion: &PairFiniteMotion,
) -> Result<ExactRatMatrix, ObservableMomentCompressionError> {
    let first = affine_homogeneous(motion.first());
    let second = affine_homogeneous(motion.second());
    let mut matrix = vec![vec![Rat::from_integer(0.into()); 8]; 8];
    for row in 0..4 {
        for column in 0..4 {
            matrix[row][column] = first[row][column].clone();
            matrix[row + 4][column + 4] = second[row][column].clone();
        }
    }
    ExactRatMatrix::new(matrix).map_err(ObservableMomentCompressionError::from)
}

fn transport_moment(
    action: &ExactRatMatrix,
    moment: &ExactRatMatrix,
) -> Result<ExactRatMatrix, ObservableMomentCompressionError> {
    action
        .multiply(moment)
        .and_then(|left| left.multiply(&action.transpose()?))
        .map_err(ObservableMomentCompressionError::from)
}

fn coordinates_in_form_span(
    ambient: usize,
    basis: &[ExactRatMatrix],
    candidate: &ExactRatMatrix,
) -> Result<Option<Vec<Rat>>, ObservableMomentCompressionError> {
    if candidate.entries().len() != ambient {
        return Err(ObservableMomentCompressionError::Shape);
    }
    if basis.is_empty() {
        return Ok(candidate
            .entries()
            .iter()
            .all(num_traits::Zero::is_zero)
            .then(Vec::new));
    }
    let columns = basis.len();
    let carrier = ExactRatMatrix::shaped(
        ambient,
        columns,
        (0..ambient)
            .map(|coordinate| {
                basis
                    .iter()
                    .map(|form| form.entries()[coordinate].clone())
                    .collect()
            })
            .collect(),
    )?;
    Ok(carrier
        .preimage_fibre(candidate.entries())?
        .map(|(coordinates, _)| coordinates))
}

fn exact_dot(left: &[Rat], right: &[Rat]) -> Result<Rat, ObservableMomentCompressionError> {
    if left.len() != right.len() {
        return Err(ObservableMomentCompressionError::Shape);
    }
    Ok(left
        .iter()
        .zip(right)
        .fold(Rat::from_integer(0.into()), |sum, (left, right)| {
            sum + left * right
        }))
}

pub(crate) fn contract_exact_forms(left: &ExactRatMatrix, right: &ExactRatMatrix) -> Rat {
    left.entries()
        .iter()
        .zip(right.entries())
        .fold(Rat::from_integer(0.into()), |sum, (left, right)| {
            sum + left * right
        })
}
