//! **Shared exact rational linear operators** — owned by `holonic_core::exact_linear`.
//!
//! [definition] Moved into the Holon core (`crates/holonic-core`) with the exact linear base it
//! belongs to; every public item is re-exported here at its existing path, explicitly, so each
//! `holonic_engine::exact_linear::X` name, and any crate-root name it had, is unchanged. The module
//! documentation, the laws and their tests live with the owner.

pub use holonic_core::exact_linear::{
    BilinearOperator, BilinearProductCore, BilinearRealization, BilinearSupportReturn,
    BilinearSupportSearch, ConstantAccelerationRelease, ContextualFactorization,
    ContextualObstruction, DECLARED_PRIME_IMAGE_CROSSOVER, EnergyMomentum, EnergyMomentumError,
    ExactContextualLift, ExactLinearError, ExactRankFactorization, ExactRatMatrix,
    JointBilinearFibre, JointBilinearSystem, JointPreimageReduction, KernelModeAction,
    KernelModeError, KernelModeReduction, KernelModeSummary, LinearFactorization, LinearMapFamily,
    MaxwellEnergyFace, RebaseReceipt, ReceiverFactorization, ReleasedMotionError,
    VacuumEnergyChart,
};
