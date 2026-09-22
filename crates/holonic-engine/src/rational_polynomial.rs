//! **Exact rational polynomials, their roots, resultants and censuses** — owned by `holonic_core::rational_polynomial`.
//!
//! [definition] Moved into the Holon core (`crates/holonic-core`) with the exact linear base it
//! belongs to; every public item is re-exported here at its existing path, explicitly, so each
//! `holonic_engine::rational_polynomial::X` name, and any crate-root name it had, is unchanged. The module
//! documentation, the laws and their tests live with the owner.

pub use holonic_core::rational_polynomial::{
    BivariatePolynomial, CensusWork, CensusedRealRoot, ExactPolynomialError,
    HALF_INTEGER_DESCENT_CEILING, HALF_PLANE_REFINEMENT_CEILING, HalfPlaneCount,
    ISOLATION_DEPTH_CEILING, MONIC_COMPANION_BIT_CEILING, ROOT_BOUND_DOUBLING_CEILING,
    RationalPolynomial, RationalRootCensus, RealRootEnclosure, ResultantWork, RootSeparation,
    RootSeparationBound, SEPARATION_SPLITTING_DEPTH_CEILING, axis_root_count, cauchy_index,
    certified_real_root_enclosure, distinct_real_root_count, euclidean_resultant, half_plane_count,
    integer_discriminant, interior_split_schedule, isolate_against_chain, isolate_real_roots,
    isolate_with_chain, modular_monic_gcd, monic_from_power_sums, newton_power_sums,
    nonzero_root_lower_bound, rational_root_census, rational_root_census_within,
    rational_roots_by_lifting, real_root_count_with_multiplicity, resultant_in_eliminated_variable,
    root_separation, squared_shrinking_steps, taylor_shifted, worst_retained_fraction,
};
