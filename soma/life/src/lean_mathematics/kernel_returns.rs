use std::collections::{BTreeMap, BTreeSet};

use holonic_structure::{LocalRelations, LocalSequence};
use serde::Serialize;

use crate::holonic_training::{FiberAdmission, FiberStanding};
use super::LeanProofMotion;

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

/// **The two-sided standing of one proof motion across a kernel return family.**
///
/// The conditioning path had to derive its negative side from its own prior predictions, because it
/// only ever watched. **Here the negative side arrives for free, because the kernel answers
/// queries**: `LeanKernelOutcome::Obstructed` is a refusal with a verbatim diagnostic, and it is a
/// refusal *of the motions the submission carried*.
///
/// So the admission law of `crate::holonic_training` applies unchanged to mathematics, over a
/// different material:
///
/// ```text
///     Admitted     the motion appears in kernel-admitted proofs and in no obstructed one
///     Refuted      it appears only in obstructed ones
///     Conflicted   both — its own name does not determine whether it carries
///     Open         it has not been submitted
/// ```
///
/// **`Conflicted` is the class that matters for a method atlas.** A motion that closes some goals
/// and fails others is a transport mechanism whose *chart* is doing work its name does not carry —
/// which is exactly the recognition condition `H.0362`'s formulation nodes require of an atlas
/// edge. It is a junction, not a bad tactic.
///
/// Nothing here ranks: the counts are reported and the verdict turns only on whether each side is
/// zero.
pub fn motion_standing(family: &LeanKernelReturnFamily) -> BTreeMap<String, FiberStanding> {
    let mut standing: BTreeMap<String, FiberStanding> = BTreeMap::new();
    for returned in family.members() {
        let admitted = returned.kernel_admitted();
        // One submission counts once per distinct motion it carries: a motion repeated inside one
        // proof is one piece of evidence about that proof, not several.
        let mut seen = BTreeSet::new();
        for motion in &returned.candidate().motions {
            if !seen.insert(motion_key(motion)) {
                continue;
            }
            let entry = standing.entry(motion_key(motion)).or_default();
            let side = if admitted {
                &mut entry.confirmations
            } else {
                &mut entry.refutations
            };
            *side = side.saturating_add(1);
        }
    }
    standing
}

/// The motion's own species and subject, as its address. `Close` is keyed by its tactic and every
/// other species by the declaration it transports through, because that is what a later proof would
/// have to reach for.
pub fn motion_key(motion: &LeanProofMotion) -> String {
    match motion {
        LeanProofMotion::Close { tactic } => format!("close/{tactic}"),
        LeanProofMotion::Direct { declaration } => format!("direct/{declaration}"),
        LeanProofMotion::Rewrite { declaration } => format!("rewrite/{declaration}"),
        LeanProofMotion::IntroduceFact { declaration } => format!("fact/{declaration}"),
        LeanProofMotion::RecurApply { declaration, depth } => {
            format!("recur{depth}/{declaration}")
        }
        LeanProofMotion::Contrapose {
            hypothesis,
            declaration,
        } => format!("contrapose[{hypothesis}]/{declaration}"),
        LeanProofMotion::Project {
            declaration,
            projection,
        } => format!("project{projection}/{declaration}"),
    }
}

/// The motions this family admits, refutes, holds conflicted, and has never submitted.
pub fn motion_admissions(
    family: &LeanKernelReturnFamily,
) -> BTreeMap<FiberAdmission, Vec<(String, FiberStanding)>> {
    let mut sorted: BTreeMap<FiberAdmission, Vec<(String, FiberStanding)>> = BTreeMap::new();
    for (key, standing) in motion_standing(family) {
        sorted
            .entry(standing.admission())
            .or_default()
            .push((key, standing));
    }
    sorted
}
