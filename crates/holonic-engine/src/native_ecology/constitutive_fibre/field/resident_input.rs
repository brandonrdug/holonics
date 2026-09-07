//! Generated currents enter the ordinary field operation without a host numerical projection.
use super::*;

/// Exact input provenance. Existing exterior arrays keep their original JSON representation.
/// Resident input values live in the immutable historical carrier, not in a fabricated host Vec.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, serde::Deserialize)]
#[serde(untagged, deny_unknown_fields)]
pub enum NativeFieldIncoming {
    Exterior(Vec<NativePhaseCurrent>),
    Resident { resident_nodes: usize },
}
impl NativeFieldIncoming {
    pub fn len(&self) -> usize {
        match self {
            Self::Exterior(v) => v.len(),
            Self::Resident { resident_nodes } => *resident_nodes,
        }
    }
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }
    pub fn is_resident(&self) -> bool {
        matches!(self, Self::Resident { .. })
    }
    pub fn exterior(&self) -> Option<&[NativePhaseCurrent]> {
        match self {
            Self::Exterior(v) => Some(v),
            Self::Resident { .. } => None,
        }
    }
}

pub(super) fn decode_input(
    rest: &ResidentSectionRest,
    nodes: usize,
) -> Result<Vec<NativePhaseCurrent>, ConstitutiveFibreError> {
    if rest.rows != nodes
        || rest.width != 3
        || rest.grain.0 != 0
        || rest.intervals.len() != 3 * nodes
        || rest.intervals.iter().any(|(l, h)| l != h)
    {
        return Err(ConstitutiveFibreError::Shape);
    }
    rest.intervals
        .chunks_exact(3)
        .map(|v| {
            let phase = NativePhaseCurrent::new(v[0].0, v[1].0, v[2].0)?;
            if phase.words() != [v[0].0, v[1].0, v[2].0] {
                return Err(ConstitutiveFibreError::Uncertain);
            }
            Ok(phase)
        })
        .collect()
}

impl<'chart> NativeConstitutiveField<'chart> {
    /// `occurrence` supplies the ordinary entering/emission/anchor contact and has no exterior
    /// input values. `current` is its actual generated input in the field's root receiving chart.
    /// Supplying both forms of input refuses instead of silently overriding one. A known refusal
    /// retains the source capability; unknown completion retains the ordinary pending field.
    pub fn advance_current_resident(
        &mut self,
        occurrence: &mut NativeFieldOccurrence,
        current: ResidentConstitutiveCurrent<'_, 'chart>,
    ) -> Result<NativeFieldContinuation, ConstitutiveFibreError> {
        self.advance_with(occurrence, Some(current), |_, _, _| Ok(()))
            .map(|(c, ())| c)
    }

    /// Cold inspection of the actual input. This is never invoked by resident advancement.
    pub fn inspect_incoming(
        &self,
        at: usize,
    ) -> Result<Vec<NativePhaseCurrent>, ConstitutiveFibreError> {
        let event = self
            .history
            .get(at)
            .ok_or(ConstitutiveFibreError::ForeignOccurrence)?;
        match &event.lineage.incoming {
            NativeFieldIncoming::Exterior(v) => Ok(v.clone()),
            NativeFieldIncoming::Resident { resident_nodes } => {
                let input = event
                    .incoming_rest(self.relation.surface)?
                    .ok_or(ConstitutiveFibreError::Uncertain)?;
                decode_input(&input, *resident_nodes)
            }
        }
    }
}

#[cfg(test)]
mod tests;
