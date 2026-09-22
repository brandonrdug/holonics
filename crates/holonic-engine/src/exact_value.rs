//! **Exact values: intervals, orderings, integer polynomials, Sturm-certified algebraic roots and certified series** — owned by `holonic_core::exact_value`.
//!
//! [definition] Moved into the Holon core (`crates/holonic-core`) with the exact linear base it
//! belongs to; every public item is re-exported here at its existing path, explicitly, so each
//! `holonic_engine::exact_value::X` name, and any crate-root name it had, is unchanged. The module
//! documentation, the laws and their tests live with the owner.

pub use holonic_core::exact_value::{
    AlgebraicRoot, CertifiedSeries, ExactInterval, ExactOrdering, ExactValue, ExactValueError,
    IntegerPolynomial, STURM_COEFFICIENT_BIT_CEILING, STURM_DEGREE_CEILING, STURM_WORK_CEILING,
    SeriesTailCertificate, SturmChain, SturmIsolationCertificate, check_declared_sturm_work,
    ieee754,
};

// Crate-visible here as it was before the move; `holonic-core` makes it public so the engine can
// read it.
pub(crate) use holonic_core::exact_value::canonical_homogeneous;
