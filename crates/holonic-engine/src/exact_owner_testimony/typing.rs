//! Port-bound coordinate dimensions and tensor contraction incidence.

use super::*;

/// The hand of one tensor slot.  This is port typing, not a glyph classification.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum TensorVariance {
    Covariant,
    Contravariant,
}

/// Address of one tensor slot in the complete port-bound constraint.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct TensorSlotAddress {
    pub boundary: BoundaryId,
    pub ordinal: u32,
}

/// Whether an index is exposed by the tensor or paired inside one construction.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub enum TensorSlotRole {
    Free,
    ContractedWith(TensorSlotAddress),
}

/// One statement-binder occurrence carried at one tensor slot.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize)]
pub struct TensorSlot {
    pub ordinal: u32,
    pub binder: u64,
    pub variance: TensorVariance,
    pub role: TensorSlotRole,
}

/// Exact typing of one nominal operation boundary.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct TypedMathematicalBoundary {
    boundary: BoundaryId,
    carrier: String,
    dimensions: Vec<Dimension>,
    tensor_slots: Vec<TensorSlot>,
}

impl TypedMathematicalBoundary {
    pub fn new(
        boundary: BoundaryId,
        carrier: impl Into<String>,
        dimension: Option<Dimension>,
        tensor_slots: Vec<TensorSlot>,
    ) -> Result<Self, ExactOwnerWitnessRefusal> {
        Self::coordinate_word(
            boundary,
            carrier,
            dimension.into_iter().collect(),
            tensor_slots,
        )
    }

    /// Type one nominal boundary by its exact ordered coordinate-dimension word. A scalar is the
    /// length-one case; an empty word is a genuinely zero-width boundary.
    pub fn coordinate_word(
        boundary: BoundaryId,
        carrier: impl Into<String>,
        dimensions: Vec<Dimension>,
        mut tensor_slots: Vec<TensorSlot>,
    ) -> Result<Self, ExactOwnerWitnessRefusal> {
        let carrier = carrier.into();
        if carrier.trim().is_empty() {
            return Err(ExactOwnerWitnessRefusal::EmptyCarrier { boundary });
        }
        tensor_slots.sort_by_key(|slot| slot.ordinal);
        if tensor_slots
            .windows(2)
            .any(|pair| pair[0].ordinal == pair[1].ordinal)
        {
            return Err(ExactOwnerWitnessRefusal::DuplicateTensorSlot { boundary });
        }
        Ok(Self {
            boundary,
            carrier,
            dimensions,
            tensor_slots,
        })
    }

    pub const fn boundary(&self) -> BoundaryId {
        self.boundary
    }

    pub fn carrier(&self) -> &str {
        &self.carrier
    }

    pub fn dimension(&self) -> Option<&Dimension> {
        if self.dimensions.len() == 1 {
            self.dimensions.first()
        } else {
            None
        }
    }

    pub fn dimensions(&self) -> &[Dimension] {
        &self.dimensions
    }

    pub fn tensor_slots(&self) -> &[TensorSlot] {
        &self.tensor_slots
    }
}

pub(super) fn validate_contractions<'a>(
    boundaries: impl Iterator<Item = &'a TypedMathematicalBoundary>,
) -> Result<(), ExactOwnerWitnessRefusal> {
    let boundaries = boundaries.collect::<Vec<_>>();
    let mut slots = BTreeMap::new();
    for boundary in &boundaries {
        for slot in &boundary.tensor_slots {
            slots.insert(
                TensorSlotAddress {
                    boundary: boundary.boundary,
                    ordinal: slot.ordinal,
                },
                *slot,
            );
        }
    }
    for (address, slot) in &slots {
        let TensorSlotRole::ContractedWith(partner) = slot.role else {
            continue;
        };
        let paired =
            slots
                .get(&partner)
                .ok_or(ExactOwnerWitnessRefusal::ContractionPartnerAbsent {
                    slot: *address,
                    partner,
                })?;
        if paired.role != TensorSlotRole::ContractedWith(*address)
            || paired.variance == slot.variance
            || paired.binder != slot.binder
        {
            return Err(ExactOwnerWitnessRefusal::ContractionDoesNotPair {
                slot: *address,
                partner,
            });
        }
    }
    Ok(())
}
