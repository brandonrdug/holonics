//! **Landmark discovery: the faces where navigator paths converge.**
//!
//! [definition] Rebuild step 3 (#145). A **landmark** of a navigator family is a face where its
//! paths converge: a site's kind and its Doppler ratio, a Möbius navigator's attracting fixed point,
//! an identity (two constructions with one face), a constraint identity read through its partial
//! navigator, and the primitive cycles (primes) of a return map. Landmark discovery locates them
//! exactly over ℚ: an irrational landmark is carried as its constraint ([`QuadraticSurd`]), and a
//! float never enters. Each module cites the Lean declarations of `Compression/Landmark` it
//! realizes, and says where it is sharper than the Lean or departs from it, naming the #62 item.
//!
//! | Module | Law | Lean `Compression/Landmark` |
//! |---|---|---|
//! | [`quadratic`] | a quadratic root carried as `p + q√D`, with exact sign and order | — |
//! | [`site`] | reflection (`q < 0`), degenerate (`q = 0`), else rotation/null/boost by `a² − 4q`, each read from the eigenvalues ([`SiteKind`] is owned by `navigator::trace`); `(M − tr/2)² = disc/4`; `γ² = tr²/(4 det)`; the Doppler ratio as `k² − ak + 1 = 0`; counts `t_{n+2} = a t_{n+1} − q t_n` sandwiched by `kⁿ ≤ t_n ≤ 2kⁿ`; the torus count `\|qⁿ − t_n + 1\|` of an integer site, `\|t_n − 2\|` at `q = 1` | `SiteKind` |
//! | [`mobius`] | fixed points of `z ↦ (αz+β)/(γz+δ)` exactly; attraction ⇔ `tr ≠ 0`; the chart scaling `μ₋/μ₊`; velocity addition fixes `±c` and its iterates converge to `c` or `−c` | `FixedPoint` |
//! | [`identity`] | an identity is two constructions with one face; charts certify exactly the identities of `V` exactly when their images are Zariski dense (`I(⋃ images) = I(V)`), checked per component; the search over a finite family | `Identity` |
//! | [`constraint`] | π (Machin) and `e` through their partial navigators; a window only with equal endpoint floors of Lean's enclosure | `ConstraintIdentity`, `Mathematics/RadixWindowReceiver` |
//! | [`primitive`] | `tr(Mⁿ) = Σ_(d\|n) d·p_d`, Möbius inversion, the Euler product, for `0/1` return maps only | `PrimitiveCycle` |
//!
//! [open] Owed in #62 (Lean `Compression/Landmark`): Gröbner completion and the face-kernel
//! equality, Richardson's undecidability, the necklace integrality and infinite Euler product of a
//! general nonnegative integer return map, the first-arrival sieve tower as a general law, and the
//! Lefschetz count of torus periodic points. Irreducible decomposition is out of scope.

pub mod constraint;
pub mod identity;
pub mod mobius;
pub mod primitive;
pub mod quadratic;
pub mod site;

use crate::navigator::trace::SiteKind;
pub use constraint::{ConstraintIdentity, RatioBlock, WindowCertificate, certify_window};
pub use identity::{
    Component, ComponentDimension, Construction, IdentityAtlas, IdentitySearch, IdentityVerdict,
    RationalChart,
};
pub use mobius::{
    Attraction, FixedPoint, FixedPoints, MobiusNavigator, ProjectivePoint, doppler_chart,
    velocity_addition,
};
pub use primitive::ReturnOccurrences;
pub use quadratic::{QuadraticSurd, rational_square_root};
pub use site::{DopplerRatio, lorentz_factor_squared, torus_fixed_points};

use thiserror::Error;

use crate::aeon::AeonError;
use crate::ratio::Rat;
use crate::ratio::algebraic::ExactValueError;
use crate::ratio::linear::ExactLinearError;

/// Every refusal of a landmark law. Bad input is a typed return, never a panic.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum LandmarkError {
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
    #[error(transparent)]
    Value(#[from] ExactValueError),
    #[error(transparent)]
    Aeon(#[from] AeonError),
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
    #[error("the navigator's pole is at {point}")]
    Pole { point: Rat },
    #[error("the navigator has no two finite fixed points to chart")]
    NoFixedPointChart,
    #[error(
        "the velocity {velocity} lies outside the open cone of characteristic {characteristic}"
    )]
    OutsideTheCone { velocity: Rat, characteristic: Rat },
    #[error("expected {expected} coordinates, found {found}")]
    VariableCount { expected: usize, found: usize },
    #[error("the degree bound {bound} of coordinate {variable} is below its degree {degree}")]
    DegreeBound {
        variable: usize,
        bound: u32,
        degree: u32,
    },
    #[error("chart `{chart}` has a zero denominator")]
    ZeroDenominator { chart: String },
    #[error("a configuration needs at least one component")]
    EmptyConfiguration,
    #[error(
        "component `{component}` is declared a {dimension:?}, but no nonzero generator in the \
         coordinates {coordinates:?} alone bounds its dimension"
    )]
    UncertifiedDimension {
        component: String,
        dimension: ComponentDimension,
        coordinates: Vec<usize>,
    },
    #[error("chart `{chart}` lands in no component of the configuration")]
    ChartOutsideConfiguration { chart: String },
    #[error("no chart covers the component `{component}`: its identities would be invented")]
    UncoveredComponent { component: String },
    #[error("a search needs at least one construction")]
    EmptyFamily,
    #[error("a radix of {radix} reads no digits")]
    Radix { radix: u32 },
    #[error("the window at offset {offset} of length {length} passes the largest exponent")]
    WindowExtent { offset: u32, length: u32 },
    #[error("occurrence {occurrence} returns to {image}, outside {size} occurrences")]
    MapImage {
        occurrence: usize,
        image: usize,
        size: usize,
    },
    #[error("a return map is square, not {rows} × {columns}")]
    NotSquare { rows: usize, columns: usize },
    #[error("entry ({row}, {column}) is {entry}: only a 0/1 return map has primitive cycles")]
    NotZeroOne {
        row: usize,
        column: usize,
        entry: Rat,
    },
    #[error("the count at length {length} is not a nonnegative integer")]
    NonIntegralCount { length: usize },
}
