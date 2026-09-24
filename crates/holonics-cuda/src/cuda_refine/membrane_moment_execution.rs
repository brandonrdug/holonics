use super::membrane_moment_plan::MomentFrontPlan;
use super::membrane_moment_workspace::MomentFrontWorkspace;
use super::*;

/// One owned device occurrence spanning contraction, receiver formation, and terminal readback.
/// The plan and buffers remain together so extracted phases cannot detach raw pointers from their
/// owners or establish a second CUDA context.
pub(super) struct MomentFrontExecution<'a> {
    pub(super) plan: MomentFrontPlan<'a>,
    pub(super) workspace: MomentFrontWorkspace,
    pub(super) post_target_observer: bool,
    pub(super) materialize_moment_field: bool,
    pub(super) resident_began: std::time::Instant,
    pub(super) cuda_profile: bool,
}

/// Device state founded by contraction and consumed by receiver formation and cold readback.
pub(super) struct MomentContractionLaunch {
    pub(super) resident_gather_launches: u64,
    pub(super) factorized_relational_launches: u64,
    pub(super) completed_target_observer_workspace:
        Option<ResidentCompletedTargetObserverWorkspace>,
}
