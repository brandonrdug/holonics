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
pub mod causal_reflection;
pub mod codec_recovery;
// The adapter from a recovered codec to `receiver_exact_compression::ObservedSystem`, and the
// cross-check between its Nerode congruence and `RecoveredCodec::shortest_separating_input`.
// Declared, never glob-exported: `ItemId`, `Observation`, `ReceiverId` and `Disagreement` collide
// across the engine's receiver modules and must be named at every call site.
pub mod codec_system;
pub mod causal_traversal;
// Reached explicitly rather than glob-exported for the same reason as
// `discrete_curvature`: the bridge names `read`, `step` and `revise`, and a glob would put those
// verbs in the crate root where nothing says what they read or step. `blueprint/THE_ASSEMBLY.md`.
pub mod curvature_bridge;
// Reached explicitly rather than glob-exported: a presentation face is a declared apparatus
// membrane, and flattening it into the crate root would let a caller reach a display type without
// naming that it is one. `blueprint/THE_PRESENTATION_ORGAN.md`.
pub mod certified_face;
pub mod communication;
// Declared, never glob-exported. `ReceiverId`, `Observation` and `ItemId` reach this module from
// `receiver_exact_compression` and collide at the crate root with `relational_geometry::ReceiverId`
// and with `graph_receiver`'s own vocabulary. `blueprint/THE_ASSEMBLY.md`, "what must not be built".
pub mod complex_system;
// The conditioning, the production it makes possible, and that production read back as a circuit,
// on one carrier with a map from every cell to the passage that founded it. Declared, never
// glob-exported: `ItemId`, `ReceiverId` and `Observation` reach it from
// `receiver_exact_compression` and collide at the crate root.
pub mod conditioned_derivation;
pub mod conic;
pub mod coupled_informant;
#[cfg(target_os = "linux")]
pub mod cuda_aperture;
#[cfg(target_os = "linux")]
pub mod cuda_relation;
pub mod device;
pub mod diffusion;
pub mod derivation_atlas;
// The derivation's layout read as a hinge incidence, realized as a closed oriented surface the
// curvature bridge can read, and the write-back that spends the returned curvature back into
// `local_star`'s own geometry. Declared, never glob-exported: it names `realize`, `flow` and
// `found`, which say nothing at the crate root about which carrier they belong to.
pub mod derivation_curvature;
// A foreign codec, recovered from its own declared statistics, entering the conditioning path by
// the seam `conditioned_derivation::FoundedMorphology::from_founded_words` declares for exactly
// that. Declared, never glob-exported: it names `present`, `intake` and `distinguish`, and all
// three are verbs that say nothing at the crate root about which carrier they belong to.
pub mod derivation_codec_intake;
// Integration through reflection on a derivation circuit: the routes, and the holonomy their
// disagreement retains. Declared, never glob-exported: it names `Route`, `AccumulationRule` and
// `accumulation`, and `Route`/`accumulation` say nothing at the crate root about which carrier
// they belong to.
pub mod derivation_integral;
// The moves a conditioned production made, read as substitutions and paid for by placement.
// Declared, never glob-exported: it names `MoveSpecies`, `OpenClass`, `ClassReading` and
// `substitutions`, and `OpenClass` collides with `placement`'s own while the verb `substitutions`
// says nothing at the crate root about which family it means.
pub mod derivation_skein;
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
// The canonical octet form of a `GradedCausalComplex`, so a rebase-invariants reading can be
// deposited and re-lit by a different part. Declared, never glob-exported: it names
// `encode_native_bytes` and `decode_native_bytes`, and a glob would put those verbs in the crate
// root where nothing says which form they are of. `blueprint/THE_ASSEMBLY.md` step 6.
pub mod graded_complex_form;
pub mod graph_receiver;
pub mod holonic_complex;
pub mod image;
pub mod implicit;
pub mod interaction;
pub mod inverse_transport;
pub mod live_presentation;
pub mod local_star;
pub mod mode;
// The declared-option modeling surface. Reached explicitly, like the other presentation membranes:
// an option is a receiver coordinate and every call site must name it as one.
pub mod model_surface;
pub mod observation_ecology;
pub mod organizational_grammar;
pub mod parameter;
pub mod phase_current;
pub mod physical;
pub mod placement;
pub mod platform;
#[cfg(all(target_os = "linux", feature = "desktop-x11"))]
pub mod platform_x11;
pub mod presentation;
// The declared display gauge and the body's one vector codec. Not glob-exported for the same
// reason as `certified_face`: colour is a gauge and must be named as one at every call site.
pub mod presentation_gauge;
pub mod prime_ecology;
pub mod realization;
pub mod leader_quadrature;
pub mod discrete_curvature;
pub mod running_integral;
pub mod rebase_invariants;
pub mod receiver;
pub mod receiver_exact_compression;
pub mod receiver_current;
pub mod receiver_ecology;
pub mod receiver_phase_atlas;
pub mod resource;
pub mod sheaf_diffusion;
pub mod simplicial;
pub mod skein;
// Declared, never glob-exported: `ReceiverId`, `Disagreement`, `Partition`, `Cover`, `Observation`
// and `ItemId` collide across the placement family, and a realizer founded by a substitution must
// be reached by naming which organ founded it. `blueprint/THE_ASSEMBLY.md` step 2.
pub mod substitution_realizers;
pub mod supported_realizers;
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
