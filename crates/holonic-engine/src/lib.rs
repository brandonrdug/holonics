//! Exact causal execution and receiver-relative visibility.
//!
//! This crate is deliberately not a graphics framework.  It contains no
//! window, camera, raster pipeline, physics package, floating-point scalar,
//! or implicit world coordinate system.  It provides:
//!
//! - an abstract evolution shape with typed interaction;
//! - arbitrary-grade causal incidence and exact local coordinate algebras;
//! - exact realizations of that shape;
//! - receiver-local sections with bounded gluing or obstruction;
//! - exact rational cellular sheaves with deterministic Hodge transport;
//! - multiplication-founded arithmetic and polynomial receiver fibers;
//! - exact integral-quintic transport through caused prime-place Frobenius
//!   sections, conditional transitive Galois fibers, formal permutation-Euler
//!   factors, and growing exact integer-sigma receivers;
//! - dual divisor-receiver reconstruction from opaque common-generator
//!   contact, with exact plural fibers, private-witness obstruction, and an
//!   arithmetic grading membrane;
//! - topology-forming prime receivers with exact finite-field factorization,
//!   Frobenius phases, potential horns, and recurrent CRT-derived filler
//!   families;
//! - lineage-relative reconstruction of opaque finite bit transducers with
//!   production-owned queries, exhaustive receiver testimony, cubical
//!   geometry, and exact x86-64 realization;
//! - factored exact reconstruction of hidden passive transport topology from
//!   lineage-marked aggregate receiver sections;
//! - predictive exact transport fibers whose retained base-law obstructions
//!   cause production-owned parameter enrichment and unseen-interval grades;
//! - exact finite organizational fibers whose returned mixed differences
//!   derive reciprocal closures, exterior ports, and graded lineage repair;
//! - active exact causal-state quotients whose future distinctions carry
//!   state-local organizational grammars and dynamic transport receipts;
//! - growing causal field atlases whose exact local coefficient fibers,
//!   obstruction-founded germs, analytical supports, and receiver-relative
//!   phase gradients remain independent of physical residency;
//! - receiver-local phase atlases whose persistent exact jets emit native
//!   conic germs and whose transported connection loops expose curvature;
//! - receiver-relative graded complexes in which analytic germs carry
//!   internal paths or loops, transported circuits form exact incidence, and
//!   complete lower-grain closures return as coarser receiver points;
//! - structured parameter/resource lifecycles;
//! - a typed exact-value tower with an explicit `OPEN` comparison;
//! - an unfolded causal diagram for algorithms;
//! - exact local mode signatures, declared mode-transport obstructions,
//!   multigraded separation, and deterministic equivalence closure;
//! - exact logical and physical resource receipts;
//! - atomic world-event succession; and
//! - exact ray/surface crossing fibers in one participating receiver's chart;
//! - cyclic hinge returns with carried projective holonomy and balance; and
//! - continuous receiver faces assembled plurally before a finite display
//!   quotient.
//!
//! A display codec or a Vulkan executor may consume these receipts.  Neither
//! is permitted to redefine their mathematics.

pub mod algebraic;
pub mod analytic_field;
pub mod arithmetic_dimensional;
pub mod arithmetic_fiber;
pub mod arithmetic_monodromy;
pub mod arithmetic_phase;
pub mod atlas;
pub mod atmospheric_inverse;
pub mod basin;
pub mod bit_causal;
pub mod category;
pub mod causal;
pub mod causal_body;
pub mod causal_state_grammar;
pub mod causal_traversal;
pub mod conic;
pub mod coupled_informant;
#[cfg(target_os = "linux")]
pub mod cuda_aperture;
#[cfg(target_os = "linux")]
pub mod cuda_relation;
pub mod device;
pub mod diffusion;
pub mod dilation;
pub mod dimensional_receiver;
pub mod dimensional_wave;
pub mod display;
pub mod divisor_reconstruction;
pub mod evolution;
pub mod exact_linear;
pub mod exact_value;
pub mod executor;
pub mod field_atlas;
pub mod generative_transport;
pub mod gluing;
pub mod graph_receiver;
pub mod holonic_complex;
pub mod image;
pub mod implicit;
pub mod interaction;
pub mod inverse_transport;
pub mod live_presentation;
pub mod local_star;
pub mod mode;
pub mod observation_ecology;
pub mod organizational_grammar;
pub mod parameter;
pub mod phase_current;
pub mod physical;
pub mod platform;
#[cfg(all(target_os = "linux", feature = "desktop-x11"))]
pub mod platform_x11;
pub mod presentation;
pub mod prime_ecology;
pub mod realization;
pub mod rebase_invariants;
pub mod receiver;
pub mod receiver_current;
pub mod receiver_ecology;
pub mod receiver_phase_atlas;
pub mod resource;
pub mod sheaf_diffusion;
pub mod simplicial;
pub mod tube;
pub mod wave_propagation;
pub mod world;

pub use algebraic::*;
pub use analytic_field::*;
pub use arithmetic_dimensional::*;
pub use arithmetic_fiber::*;
pub use arithmetic_monodromy::*;
pub use arithmetic_phase::*;
pub use atlas::*;
pub use atmospheric_inverse::*;
pub use basin::*;
pub use bit_causal::*;
pub use category::*;
pub use causal::*;
pub use causal_body::*;
pub use causal_state_grammar::*;
pub use causal_traversal::*;
pub use conic::*;
pub use coupled_informant::*;
#[cfg(target_os = "linux")]
pub use cuda_aperture::*;
#[cfg(target_os = "linux")]
pub use cuda_relation::*;
pub use device::*;
pub use diffusion::*;
pub use dimensional_receiver::*;
pub use dimensional_wave::*;
pub use display::*;
pub use divisor_reconstruction::*;
pub use evolution::*;
pub use exact_linear::*;
pub use exact_value::*;
pub use executor::*;
pub use field_atlas::*;
pub use generative_transport::*;
pub use graph_receiver::*;
pub use holonic_complex::*;
pub use image::*;
pub use implicit::*;
pub use interaction::*;
pub use inverse_transport::*;
pub use live_presentation::*;
pub use local_star::*;
pub use mode::*;
pub use observation_ecology::*;
pub use organizational_grammar::*;
pub use parameter::*;
pub use phase_current::*;
pub use physical::*;
pub use platform::*;
#[cfg(all(target_os = "linux", feature = "desktop-x11"))]
pub use platform_x11::*;
pub use presentation::*;
pub use prime_ecology::*;
pub use realization::*;
pub use receiver::*;
pub use receiver_current::*;
pub use receiver_ecology::*;
pub use receiver_phase_atlas::*;
pub use resource::*;
pub use sheaf_diffusion::*;
pub use simplicial::*;
pub use tube::*;
pub use wave_propagation::*;
pub use world::*;
