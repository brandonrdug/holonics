//! **Landmark discovery: the faces where navigator paths converge.**
//!
//! [definition] Rebuild step 3 (#145). A **landmark** of a navigator family is a face where its
//! paths converge: a site's kind and its Doppler ratio, a Möbius navigator's attracting fixed point,
//! an identity (two constructions with one face), a constraint identity read through its partial
//! navigator, the primitive cycles (primes) of a return map, and the contexts of the shift navigator
//! where a source's paths converge (the receiving tree, [`context`]). Landmark discovery locates them
//! exactly over ℚ: an irrational landmark is carried as its constraint ([`QuadraticSurd`]), and a
//! float never enters. Each module cites the Lean declarations of `Compression/Landmark` it
//! realizes, and says where it is sharper than the Lean or departs from it, naming the #62 item.
//! The identity atlas, the constraint identities and the primitive cycles are held by Lean
//! `Compression/Landmark/{Identity, ConstraintIdentity, PrimitiveCycle}` alone: their unconsumed
//! Rust owners were retired on September 28, and the laws Lean does not yet hold are kept in their
//! records (the identity atlas's record of September 19 and the aeon record's A8).
//!
//! | Module | Law | Lean `Compression/Landmark` |
//! |---|---|---|
//! | [`quadratic`] | a quadratic root carried as `p + q√D`, with exact sign and order | — |
//! | [`site`] | reflection (`q < 0`), degenerate (`q = 0`), else rotation/null/boost by `a² − 4q`, each read from the eigenvalues ([`SiteKind`] is owned by `navigator::trace`); `(M − tr/2)² = disc/4`; `γ² = tr²/(4 det)`; the Doppler ratio as `k² − ak + 1 = 0`; counts `t_{n+2} = a t_{n+1} − q t_n` sandwiched by `kⁿ ≤ t_n ≤ 2kⁿ`; the torus count `\|qⁿ − t_n + 1\|` of an integer site, `\|t_n − 2\|` at `q = 1` | `SiteKind` |
//! | [`mobius`] | fixed points of `z ↦ (αz+β)/(γz+δ)` exactly; attraction ⇔ `tr ≠ 0`; the chart scaling `μ₋/μ₊`; velocity addition fixes `±c` and its iterates converge to `c` or `−c` | `FixedPoint` |
//! | [`context`] | the shift navigator's landmarks, the receiving tree: a node is a context where the source's paths converge; context-tree weighting over typed address letters, a mixture over the pruned trees' candidate standings with the stop prior, each node's arrivals the epochs of its section and its register capped by a carry; executed on a declared dyadic lattice with certified residuals, stored where paths part; the HNN reads it as the receiving parametron's storage (`hnn::receiving`) | `Context/{Tree, Standing, Epoch, Compaction, Capacity, Carrier, Address, LocalWeighing, ConvergenceFounding}` |
//!
//! [open] Owed in #62 (Lean `Compression/Landmark`): Gröbner completion and the face-kernel
//! equality, Richardson's undecidability, the necklace integrality and infinite Euler product of a
//! general nonnegative integer return map, the first-arrival sieve tower as a general law, and the
//! Lefschetz count of torus periodic points. Irreducible decomposition is out of scope.

pub mod context;
pub mod mobius;
pub mod quadratic;
pub mod site;

use crate::navigator::trace::SiteKind;
pub use mobius::{
    Attraction, FixedPoint, FixedPoints, MobiusNavigator, ProjectivePoint, doppler_chart,
    velocity_addition,
};
pub use quadratic::{QuadraticSurd, rational_square_root};
pub use site::{DopplerRatio, lorentz_factor_squared, torus_fixed_points};

use thiserror::Error;

use crate::ratio::{GaussianRat, Rat};

/// Every refusal of a landmark law. Bad input is a typed return, never a panic.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum LandmarkError {
    #[error("the radicand {radicand} is negative: no real quadratic field")]
    NegativeRadicand { radicand: Rat },
    #[error("the radicands {left} and {right} name two quadratic fields")]
    RadicandMismatch { left: Rat, right: Rat },
    #[error("zero has no inverse")]
    ZeroDivisor,
    #[error("a {kind:?} site has no Lorentz face: only a null or boost site has `γ² ≥ 1`")]
    NoLorentzFace { kind: SiteKind },
    #[error("the site ({trace}, {determinant}) is not an integer site, so no torus endomorphism")]
    NotAnIntegerSite { trace: Rat, determinant: Rat },
    #[error("a period of zero counts nothing: `M⁰ = 1` fixes every point")]
    ZeroPeriod,
    #[error("the site ({trace}, {determinant}) is not a boost of determinant one")]
    NotAUnitBoost { trace: Rat, determinant: Rat },
    #[error("a singular block is not a Möbius navigator")]
    SingularNavigator,
    #[error("the navigator's pole is at {point:?}")]
    Pole { point: GaussianRat },
    #[error("the navigator has no two finite fixed points to chart")]
    NoFixedPointChart,
    #[error(
        "the velocity {velocity} lies outside the open cone of characteristic {characteristic}"
    )]
    OutsideTheCone { velocity: Rat, characteristic: Rat },
}
