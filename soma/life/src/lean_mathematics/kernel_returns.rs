use holonic_structure::{LocalRelations, LocalSequence};
use serde::Serialize;

use super::{LeanMathematicsError, LeanProofCandidate};

/// The typed consequence of one proof path crossing Lean's kernel environment.
///
/// This is path testimony, not a theorem-selection score. Every member remains in the return
/// family and later cultivation receives the complete family at once.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum LeanKernelOutcome {
    KernelAdmitted,
    Obstructed,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct LeanKernelReturn {
    pub(super) candidate: LeanProofCandidate,
    pub(super) outcome: LeanKernelOutcome,
    pub(super) source_sha256: String,
    pub(super) diagnostic_sha256: String,
    pub(super) diagnostic: String,
    /// Observer telemetry only; it does not enter candidate selection or standing.
    pub(super) observed_millis: u64,
}

impl LeanKernelReturn {
    pub const fn candidate(&self) -> &LeanProofCandidate {
        &self.candidate
    }

    pub const fn outcome(&self) -> LeanKernelOutcome {
        self.outcome
    }

    pub const fn kernel_admitted(&self) -> bool {
        matches!(self.outcome, LeanKernelOutcome::KernelAdmitted)
    }

    pub fn source_sha256(&self) -> &str {
        self.source_sha256.as_str()
    }

    pub fn diagnostic_sha256(&self) -> &str {
        self.diagnostic_sha256.as_str()
    }

    pub fn diagnostic(&self) -> &str {
        self.diagnostic.as_str()
    }

    pub const fn observed_millis(&self) -> u64 {
        self.observed_millis
    }
}

/// One complete, owner-native family of kernel returns.
///
/// The family owns every admitted and obstructed member exactly once. It never materializes an
/// admitted-only population and never ranks admitted members. At the owner mouth, `align_to`
/// transports arbitrary apparatus completion order back onto the deed's exact candidate
/// chronology, so permutation of worker return order cannot alter cultivation.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
#[serde(deny_unknown_fields)]
pub struct LeanKernelReturnFamily {
    members: LocalSequence<LeanKernelReturn>,
}

impl LeanKernelReturnFamily {
    pub fn from_members(
        members: impl IntoIterator<Item = LeanKernelReturn>,
    ) -> Result<Self, LeanMathematicsError> {
        let members = LocalSequence::from_iter(members);
        if members.is_empty() {
            return Err(LeanMathematicsError::IncompleteKernelReturn);
        }
        let mut witnessed = LocalRelations::new();
        for returned in &members {
            if witnessed.insert(returned.candidate.ordinal, ()).is_some() {
                return Err(LeanMathematicsError::IncompleteKernelReturn);
            }
        }
        Ok(Self { members })
    }

    pub fn members(&self) -> &[LeanKernelReturn] {
        &self.members
    }

    #[cfg(test)]
    pub(super) fn members_mut(&mut self) -> &mut [LeanKernelReturn] {
        &mut self.members
    }

    pub fn kernel_admitted(&self) -> impl Iterator<Item = &LeanKernelReturn> {
        self.members
            .iter()
            .filter(|returned| returned.kernel_admitted())
    }

    pub fn obstructions(&self) -> impl Iterator<Item = &LeanKernelReturn> {
        self.members
            .iter()
            .filter(|returned| !returned.kernel_admitted())
    }

    pub fn kernel_admitted_extent(&self) -> usize {
        self.kernel_admitted().count()
    }

    pub fn obstruction_extent(&self) -> usize {
        self.obstructions().count()
    }

    pub(super) fn align_to(
        self,
        candidates: &[LeanProofCandidate],
    ) -> Result<Self, LeanMathematicsError> {
        if self.members.len() != candidates.len() {
            return Err(LeanMathematicsError::IncompleteKernelReturn);
        }
        let mut returned_by_ordinal = LocalRelations::new();
        for returned in self.members {
            let ordinal = returned.candidate.ordinal;
            if returned_by_ordinal.insert(ordinal, returned).is_some() {
                return Err(LeanMathematicsError::IncompleteKernelReturn);
            }
        }
        let mut members = LocalSequence::with_capacity(candidates.len());
        for candidate in candidates {
            let returned = returned_by_ordinal
                .remove(&candidate.ordinal)
                .ok_or(LeanMathematicsError::IncompleteKernelReturn)?;
            if returned.candidate != *candidate {
                return Err(LeanMathematicsError::IncompleteKernelReturn);
            }
            members.push(returned);
        }
        if !returned_by_ordinal.is_empty() {
            return Err(LeanMathematicsError::IncompleteKernelReturn);
        }
        Ok(Self { members })
    }
}
