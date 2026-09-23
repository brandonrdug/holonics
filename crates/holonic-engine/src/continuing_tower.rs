//! The continuing tower, its gluing trichotomy, and the non-invertible transition that carries its
//! residual — **re-exported from the Holon core's restriction facet**.
//!
//! [definition] The owner moved to `crates/holonic-core/src/restriction/tower.rs`
//! (`holonic_core::restriction::tower`) in phase 6 of
//! `docs/plans/THE_HOLON_CORE_FOUNDS_THE_NATIVE_MACHINERY.md`: restriction is one owner, and the
//! tower is its transverse axis. It carries the correspondence table with
//! `Foundation/ContinuingTower.lean`, which the engine's `lean_citations` scan reads there. Every
//! item is re-exported here at its existing path, so no caller, wire or public name changes.

pub use holonic_core::restriction::tower::{
    ChartRoute, CoarseGrain, CompatibilityReceipt, CompatibleSection, ComposedMigration,
    ComposedTransition, CompositionStage, ComputableTower, EnumerableTower, ExactShift,
    FactorisationReceipt, FibreSplitting, GluingObstruction, GluingResult, HalvingMigration,
    IdentityMigration, IndexRouteReceipt, MaterializedFace, Migration, MigrationOutcome,
    MigrationRefusal, MigrationRefusalOf, MigrationSourceFace, MigrationSourceIndex,
    MigrationTargetFace, MigrationTargetIndex, NaturalityReceipt, NoResidual, ObservationFibre,
    RationalFloor, ReopenOutcome, ReopenReceipt, ReopenRefusal, ResidualMigration, ResidueTower,
    RestrictionReceipt, ReversePassageReceipt, ShiftTower, SplittingRefusal, SquareReopenReceipt,
    SquareRoute, SwapMigration, Tower, TowerFaceOutcome, TowerOutcome, TowerRefusal,
    TowerRestrictTransition, Transition, TwoChartTower, TwoCharts, UnitTower, carry_section,
    check_factors_through_restriction, check_index_routes, check_migration_naturality,
    check_migration_square_reopen, check_restriction_laws, check_reverse_passage,
    computable_section, glue_chain,
};
