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

use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::factored_moment::FactoredMomentError;
use crate::receiver_exact_compression::{CollapsedPair, InputId, ItemId, Observation, ReceiverId};

/// One state of the native quotient.  Its ordinal is only the canonical address of a conduct
/// block; no arithmetic or semantic ordering is read from it.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct NativeStateId(pub u64);

/// The quotient map `q : X -> Q`, exhibited at every source occurrence.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QuotientAssignment {
    pub source: ItemId,
    pub native: NativeStateId,
}

/// One complete source fibre of `q`.  This is what an exterior decoder must retain instead of
/// silently choosing a source occurrence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReconstructionFibre {
    pub native: NativeStateId,
    pub sources: BTreeSet<ItemId>,
}

/// One entry of a source generator `T_i`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SourceTransport {
    pub from: ItemId,
    pub to: ItemId,
}

/// One entry of the induced native generator `U_i`.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct NativeTransport {
    pub from: NativeStateId,
    pub to: NativeStateId,
}

/// A complete commuting generator square.  `source` and `native` are total functions over their
/// respective declared populations; construction refuses a terminus rather than hiding it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct GeneratorSquare {
    pub generator: InputId,
    pub source: Vec<SourceTransport>,
    pub native: Vec<NativeTransport>,
}

/// The factor `rhoBar_j : Q -> Face` for one native state and receiver.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReceiverFactor {
    pub native: NativeStateId,
    pub receiver: ReceiverId,
    pub observation: Observation,
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
