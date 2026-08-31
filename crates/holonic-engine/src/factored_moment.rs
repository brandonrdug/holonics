//! Exact quadratic current carried as an incidence frame and its constitutive form.
//!
//! A weighted current family `x_s` presents the moment
//!
//! ```text
//! C = sum_s w_s (x_s tensor x_s).
//! ```
//!
//! This owner never materializes the ambient `factor_population²` field.  It returns the
//! image section `C = Bᵀ H B`: `B` is a full-row-rank incidence frame and `H` is the constitutive
//! form on that image. A plural generator front acts on the factor leg, after which an addressed
//! coordinate passage derives the next image population and pulls `H` through the same map.
//! Cross-moment Gram charts and matrix inverses are construction certificates, not hot-section
//! anatomy. Source presentations remain a separate reconstruction fibre.

mod types;
pub use types::*;

mod action;
mod passage;
mod section;
mod sparse;
mod spine;

#[cfg(test)]
#[path = "factored_moment/tests.rs"]
mod tests;
