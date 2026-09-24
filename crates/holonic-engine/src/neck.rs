//! **The neck station: the pinhole into which flux converges and out of which it diverges.**
//!
//! [definition] This module owns item **T6** of
//! `docs/plans/THE_TUBE_CARRIES_RELEASE_THROUGH_NECKS_FOLDS_AND_JUNCTIONS.md`. It is the
//! executable half of
//! `formal/elementary-holonics/ElementaryHolonics/Transport/Neck.lean`, namespace
//! `Soma.Holonics.Transport.Neck`.
//!
//! [project-postulate] Brandon, September 19: **a neck is a pinhole** — an intermediary
//! singularity into which flux converges and from which it diverges into the next medium, as light
//! converges into the lens of an eye and diverges through the aqueous medium onto the retina. The
//! general object is the **tube**; a tower is what one instantaneous frame of it shows; a
//! staircase is its passage between grains or difference orders. A neck is therefore a
//! **station of the existing tube**, not a second tube: [`NeckTube`] implements
//! [`StationedTower`](holonics::restriction::tube::StationedTower) and the holonomy around a neck is
//! `continuing_tube`'s own [`check_circuit_holonomy`](holonics::restriction::tube::check_circuit_holonomy).
//!
//! # Three widths, three types
//!
//! [definition] Geometric cross-section, receiver uncertainty and analytic domain width are
//! **different quantities** and this owner keeps them in different Rust types with different
//! domains, so they cannot be mixed by arithmetic:
//!
//! * [`GeometricSection`] — `A(s)`, an exact nonnegative rational with a declared unit lineage.
//! * [`ReceiverUncertaintyWidth`] — a wrapper over `receiver_release`'s own
//!   [`ReceiverWidth`](holonics::law::receiver::ReceiverWidth), so the diameter here **is** that
//!   owner's diameter and release is that owner's width-zero condition.
//! * [`AnalyticWidth`] — the distance from the real axis to the nearest pole, taken from
//!   [`pole_atlas`](crate::causal_chord::pole_atlas) as a **squared** rational or as a named
//!   algebraic factor. No square root appears on any deciding path: for an irreducible
//!   `x² + b x + c` with `4c − b² > 0` the squared half-width is `(4c − b²)/4` exactly, and a
//!   factor of degree above two that no rational decides is returned in its own `undecided` list
//!   rather than chosen. **A second, structural arm**
//!   ([`analytic_width_of_real_spectrum`]) decides the same width from a placement instead of a
//!   pole: when the caller's generator carries a [`RealSpectrumLicence`] every eigenvalue is
//!   real, so every pole is, the strip has closed and the squared half-width is exactly `0` — at
//!   any extent, with no characteristic polynomial formed. This owner does not decide which
//!   licence a generator carries; that reading belongs to
//!   [`crate::holonic_interaction::HolonicInteraction::structural_placement`] and the licence is
//!   carried on the certificate so what the width rests on stays visible on the wire.
//!
//! [definition] They are related **only** through a declared [`ConstitutiveLink`], which names its
//! own domain and returns a residual. Nothing in this owner converts one width into another
//! without such a declaration.
//!
//! # Convergence in and divergence out, from one law
//!
//! [proved-derived; implemented-exact] Under a steady conservation law on a tube with stations
//! `s_0 < … < s_{n−1}`, cross-sections `A_i` and current densities `j_i`, the flux is
//! `Φ_i = A_i · j_i`. With no source, `Φ` is constant, so
//!
//! ```text
//!   j_i = Φ / A_i
//! ```
//!
//! rises exactly as the section narrows and falls after it: that is the pinhole, and
//! [`TubeProfile::speedup`] returns it **only** when the declared sources all vanish. Lean:
//! `Transport/Neck.lean::density_of_constant_flux` and
//! `Transport/Neck.lean::speedup_of_narrowing`, whose hypotheses are explicit, with
//! `Transport/Neck.lean::no_speedup_of_negative_flux` showing that dropping the positive-flux
//! hypothesis reverses the conclusion. With
//! sources, sinks, wall diffusion or a shock the owner returns the per-station **transport
//! residual** instead of asserting any speed-up: [`TubeProfile::station_balance`] builds the
//! one-dimensional chain complex through
//! [`ResistiveNetwork`](crate::junction_law::ResistiveNetwork) and hands it to
//! [`check_junction`](crate::junction_law::check_junction), so the divergence/source balance is
//! `junction_law`'s and is not re-implemented here.
//!
//! [definition] The complex is the physical one. A control volume sits **between** consecutive
//! cross-sections, so the balance cells are the `n − 1` gaps and the flux cells are the `n`
//! cross-sections; two exterior nodes carry the inflow and the outflow so that the first and last
//! cross-sections are branches like every other. `junction_law`'s divergence at a gap is
//! `Φ_i − Φ_{i+1}`, the inflow minus the outflow, so the residual this owner returns is negated
//! once into the plan's own orientation `Φ_{i+1} − Φ_i − σ_i`, with `σ_i` the net source injected
//! into the gap. That single sign is documented here and is the only arithmetic this owner adds to
//! the junction reading. Lean: `Transport/Neck.lean::residual_eq_zero_iff` and
//! `Transport/Neck.lean::flux_constant_of_sourceless_balance`.
//!
//! # The neck, and what re-opens after it
//!
//! [definition] The neck is `argmin A_i`. Its typed reading is [`NeckReading`]:
//! `Open` while the section exceeds the receiver's declared grain; `Pinhole` when the section is a
//! single point at that grain **while the interior is still plural**, which is exactly
//! `receiver_release`'s release condition — width zero at the receiver, plurality retained inside;
//! and `Closed` at a zero section, where the flux must vanish or the residual is returned.
//! [`TubeProfile::reopening`] reports what widens after it.
//!
//! # The optical instance: étendue survives the focus that the geometric width does not
//!
//! [proved-derived; implemented-exact] [`RayTransfer`] is an exact `2×2` rational ray-transfer
//! matrix on `(height, angle)`. Free propagation and a thin lens are unimodular; a refracting
//! interface has determinant `n₁/n₂`. A declared input bundle is an
//! [`ExactZonotope`](crate::receiver_release::ExactZonotope) box — half-height `y₀`, half-angle
//! `θ₀` — and its transverse half-extent after a transfer is
//! `receiver_release`'s own `coordinate_half_extent`, which for the box is `|A| y₀ + |B| θ₀`. The
//! **focus** is the station where that vanishes: for a point source `y₀ = 0` it is exactly `B = 0`.
//! At that station the angular half-extent is still positive and the **reduced étendue**
//! `n · (phase area)` is unchanged — the geometric width has gone to zero while the bundle is
//! still plural inside. That is "a point at the receiver's grain while plural inside", made
//! exact. Lean: `Transport/Neck.lean::focus_has_zero_extent`,
//! `Transport/Neck.lean::etendue_survives_the_focus`, `Transport/Neck.lean::phaseArea_comp` and
//! `Transport/Neck.lean::reducedEtendue_interface`.
//!
//! # Parametric orientation
//!
//! [proved-derived; implemented-exact] [`TubeProfile::reparametrized`] carries the reading along a
//! strictly increasing rational reparametrization of the station parameter: the sections, current
//! densities, fluxes and the neck index are unchanged, and only the station coordinates move.
//! [`TubeProfile::reversed`] runs the chain backwards: the station order reverses, the current
//! density changes sign — flux is a signed quantity through an oriented face — and the neck index
//! reflects. The orientation bit is `junction_law`'s
//! [`OrientationBit`](crate::junction_law::OrientationBit).
//!
//! # No universal certainty gate
//!
//! [definition] A [`NeckCertificate`] names the receiver scope it was taken in and is a reading.
//! It does not gate the output of a generated face, and this owner exposes no function that
//! consumes one in order to permit or forbid anything.
//!
//! # Floats
//!
//! [implemented-exact] No `f32` and no `f64` appears in this owner or in its tests.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use holonics::geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::algebraic::CausalCellId;
use crate::causal_chord::{ChordRefusal, PoleAtlas, PoleReading, pole_atlas};
use holonics::restriction::tower::{Tower, TowerFaceOutcome, TowerRefusal};
use holonics::restriction::tube::horizon::FaceReading;
use holonics::restriction::tube::HolonomyVerdict;
use holonics::restriction::tube::horizon::HorizonDeclaration;
use holonics::restriction::tube::horizon::Observer;
use holonics::restriction::tube::StationedTower;
use holonics::restriction::tube::TubeOutcome;
use holonics::restriction::tube::TubeRefusal;
use holonics::restriction::tube::check_circuit_holonomy;
use holonics::restriction::tube::horizon::horizon_reach;
use holonics::restriction::tube::horizon::two_axis_width;
use holonics::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::iwasawa_tower::{IwasawaLevel, IwasawaRefusal, LambdaPresentation};
use crate::jet_staircase::{FiniteJet, StaircaseRefusal};
use crate::junction_law::{
    Interface, JunctionField, JunctionRefusal, JunctionVerdict, OrientationBit, ResistiveNetwork,
    Side, check_junction,
};
use holonics::rational_polynomial::RationalPolynomial;
use holonics::law::receiver::DiameterNorm;
use holonics::law::receiver::ExactFace;
use holonics::law::receiver::Horizon;
use holonics::law::receiver::LinearReading;
use holonics::law::receiver::ReceiverWidth;
use holonics::law::receiver::WidthRefusal;
use crate::receiver_release::{CompatibleFamily, ExactZonotope, width_enclosed};
use crate::topological_receiver::{
    ClosedPolygon, ProjectionDirection, TopologicalError, linking_number,
};

/// The wire schema this owner's serialized values carry.
pub const NECK_SCHEMA: &str = "holonic-engine.neck.v1";

// ===============================================================================================
// ceilings
// ===============================================================================================

/// The largest station count a [`TubeProfile`] may declare.
///
/// The station balance builds a chain complex with one node per gap plus two exterior nodes and
/// one branch per station, and `junction_law` reduces a matrix over it. The ceiling is checked in
/// [`TubeProfile::declare`], before any vector is sized by the count.
pub const STATION_CEILING: usize = 1024;

/// The largest optical train, in elements, a declaration may name.
pub const OPTICAL_ELEMENT_CEILING: usize = 1024;

// ===============================================================================================
// refusals
// ===============================================================================================

/// Every way this owner declines, by name.
///
/// Not `Clone`, `PartialEq` or `Eq`: three of the owners it composes return refusals that are
/// none of those, and this owner carries their refusal whole rather than flattening it to a
/// string in order to land a derive.
#[derive(Debug, Error)]
pub enum NeckRefusal {
    #[error("a cross-section of {area} is negative, and a negative section is not a section")]
    NegativeSection { area: String },
    #[error("a tube needs at least two stations to have a neck between them; {declared} declared")]
    TooFewStations { declared: usize },
    #[error("the declared station count {declared} is past the ceiling {ceiling}")]
    StationsBeyondCeiling { declared: usize, ceiling: usize },
    #[error(
        "the profile declares {stations} stations, {sections} sections, {densities} current \
         densities and {sources} gap sources; it needs {stations}, {stations} and {gaps}"
    )]
    ProfileShapeMismatch {
        stations: usize,
        sections: usize,
        densities: usize,
        sources: usize,
        gaps: usize,
    },
    #[error("the station parameter is not strictly increasing at position {at}")]
    StationsNotIncreasing { at: usize },
    #[error("a speed-up reading needs a sourceless tube; station gap {at} declares {injected}")]
    SpeedupNeedsNoSource { at: usize, injected: String },
    #[error("station {at} has a zero section, so no current density divides into it")]
    ZeroSectionHasNoDensity { at: usize },
    #[error("a wall loss of {loss} is negative; a dissipative exchange does not restore flux")]
    NegativeWallLoss { loss: String },
    #[error("a ray transfer needs a 2x2 matrix; {rows}x{columns} declared")]
    RayTransferNotTwoByTwo { rows: usize, columns: usize },
    #[error("a ray transfer of determinant {determinant} is not unimodular")]
    RayTransferNotUnimodular { determinant: String },
    #[error("a thin lens of zero focal length has no ray transfer")]
    ZeroFocalLength,
    #[error("a refractive index of {index} is not strictly positive")]
    NonPositiveIndex { index: String },
    #[error("the declared optical train carries {declared} elements, past the ceiling {ceiling}")]
    OpticalBeyondCeiling { declared: usize, ceiling: usize },
    #[error("the two-axis horizon declined: {reason}")]
    Horizon { reason: String },
    #[error("a ray bundle needs a nonnegative half-height and half-angle; {which} is {value}")]
    NegativeBundleExtent { which: &'static str, value: String },
    #[error("a ray bundle with no extent at all is a single ray, not a bundle")]
    DegenerateBundle,
    #[error("the constitutive link relates a width to itself, which declares nothing")]
    LinkIsIdentity,
    #[error("the analytic width has no pole to read: the denominator is a nonzero constant")]
    NoPoleToRead,
    #[error("exact linear algebra declined: {0}")]
    Linear(#[from] ExactLinearError),
    #[error("the junction law declined: {0}")]
    Junction(#[from] JunctionRefusal),
    #[error("the width owner declined: {0}")]
    Width(#[from] WidthRefusal),
    #[error("the causal chord declined: {0}")]
    Chord(#[from] ChordRefusal),
    #[error("the jet staircase declined: {0}")]
    Staircase(#[from] StaircaseRefusal),
    #[error("the Iwasawa tower declined: {0}")]
    Iwasawa(#[from] IwasawaRefusal),
    #[error("the topological receiver declined: {0}")]
    Topological(#[from] TopologicalError),
}

// ===============================================================================================
// 1. three widths, three types
// ===============================================================================================

/// **(a) The geometric cross-section `A(s)` at one station.**
///
/// [definition] An exact nonnegative rational with a declared unit lineage. Zero is admitted —
/// that is a closed neck — and a negative value is refused by name.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "GeometricSectionWire")]
pub struct GeometricSection {
    area: Rat,
    units: String,
}

#[derive(Deserialize)]
struct GeometricSectionWire {
    area: Rat,
    units: String,
}

impl TryFrom<GeometricSectionWire> for GeometricSection {
    type Error = NeckRefusal;

    fn try_from(wire: GeometricSectionWire) -> Result<Self, Self::Error> {
        Self::declare(wire.area, wire.units)
    }
}

impl GeometricSection {
    /// Declare it. A negative area is refused.
    pub fn declare(area: Rat, units: impl Into<String>) -> Result<Self, NeckRefusal> {
        if area.is_negative() {
            return Err(NeckRefusal::NegativeSection {
                area: area.to_string(),
            });
        }
        Ok(Self {
            area,
            units: units.into(),
        })
    }

    pub fn area(&self) -> &Rat {
        &self.area
    }

    pub fn units(&self) -> &str {
        &self.units
    }

    pub fn is_closed(&self) -> bool {
        self.area.is_zero()
    }
}

/// **(b) The receiver's uncertainty width**, which is `receiver_release`'s own width.
///
/// [definition] A wrapper, not a re-founding: the diameter, the norm and the witness are that
/// owner's and are read back through it. Release is
/// [`ReceiverWidth::releasable_at`](holonics::law::receiver::ReceiverWidth::releasable_at).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReceiverUncertaintyWidth {
    width: ReceiverWidth,
    domain: String,
}

impl ReceiverUncertaintyWidth {
    /// Wrap a width taken by `receiver_release`, with the domain the caller read it in.
    pub fn declare(width: ReceiverWidth, domain: impl Into<String>) -> Self {
        Self {
            width,
            domain: domain.into(),
        }
    }

    /// The width this reading is: `receiver_release`'s object, whole.
    pub fn width(&self) -> &ReceiverWidth {
        &self.width
    }

    pub fn domain(&self) -> &str {
        &self.domain
    }

    /// Release at a declared tolerance, delegated.
    pub fn releases_at(&self, tolerance: &Rat) -> bool {
        self.width.releasable_at(tolerance)
    }
}

/// How an analytic half-width was certified.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum AnalyticCertificate {
    /// A pole on the real axis itself: the strip has closed.
    RationalPoleOnAxis { pole: Rat },
    /// An irreducible `x² + b x + c` with negative discriminant. The squared half-width is
    /// `(4c − b²)/4`, exactly, and no square root is taken.
    ConjugatePair { linear: Rat, constant: Rat },
    /// A quadratic `a x² + b x + c` with nonnegative discriminant: its roots are real whether or
    /// not any rational names them, so the strip has closed. Decided by the discriminant's sign.
    RealQuadraticRoots {
        leading: Rat,
        linear: Rat,
        constant: Rat,
    },
    /// **The spectrum is on the real axis by structure, so the strip has closed without a pole
    /// being computed.** The licence names the theorem; `extent` is the chart it holds on, and it
    /// is carried because a placement over an empty chart places nothing.
    StructurallyPlacedOnTheRealAxis {
        licence: RealSpectrumLicence,
        extent: usize,
    },
}

/// **Why a spectrum is known real without any root being isolated.**
///
/// [definition] This owner does not decide which licence a generator carries — that is
/// [`crate::holonic_interaction::HolonicInteraction::structural_placement`]'s reading. It carries
/// the name so the certificate says what it rests on, and so a caller reading the width back off
/// the wire can see that no pole was formed.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum RealSpectrumLicence {
    /// `A = −M G` with `G ≻ 0` symmetric and `M ⪰ 0` symmetric: `AᵀG = GA`, so `A` is
    /// self-adjoint in the `G`-pairing, `S = G A` is symmetric, and the pair `(S, G)` is
    /// simultaneously diagonalizable by congruence. Every eigenvalue is real and `≤ 0`, so every
    /// pole of `C (sI − A)⁻¹ B` is real and the squared half-width is exactly `0`.
    GSelfAdjointNegativeSemidefinite,
}

/// **(c) The analytic width: the squared distance from the real axis to the nearest pole.**
///
/// [definition] Squared, always, so no square root ever reaches a deciding path. Factors of degree
/// above two whose roots no rational decides are returned in [`Self::undecided`] rather than
/// chosen or approximated.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct AnalyticWidth {
    squared_half_width: Rat,
    attaining: AnalyticCertificate,
    undecided: Vec<RationalPolynomial>,
}

impl AnalyticWidth {
    /// The squared distance from the real axis to the nearest decided pole.
    pub fn squared_half_width(&self) -> &Rat {
        &self.squared_half_width
    }

    pub fn attaining(&self) -> &AnalyticCertificate {
        &self.attaining
    }

    /// Factors this reading did not decide. A nonempty list means the returned half-width is an
    /// upper bound over the decided part only, and the accessor says so rather than the value.
    pub fn undecided(&self) -> &[RationalPolynomial] {
        &self.undecided
    }

    /// Whether every factor of the atlas was decided.
    pub fn is_complete(&self) -> bool {
        self.undecided.is_empty()
    }
}

/// **Read the analytic width off a pole atlas.**
///
/// Composes [`pole_atlas`](crate::causal_chord::pole_atlas): the atlas' squarefree factors are
/// walked, a rational root contributes squared distance zero, a quadratic `a x² + b x + c`
/// contributes `(4ac − b²)/(4a²)` when its discriminant is negative and zero when it is not (real
/// roots need no rational to name them), and a factor of degree above two is left undecided.
pub fn analytic_width(atlas: &PoleAtlas) -> Result<AnalyticWidth, NeckRefusal> {
    let mut best: Option<(Rat, AnalyticCertificate)> = None;
    let mut undecided = Vec::new();
    for factor in &atlas.factors {
        if factor.degree == 0 {
            continue;
        }
        if let Some(pole) = factor.rational_poles.first() {
            best = Some((
                Rat::zero(),
                AnalyticCertificate::RationalPoleOnAxis { pole: pole.clone() },
            ));
            continue;
        }
        let coefficients = factor.factor.coefficients();
        if factor.degree == 2 && coefficients.len() == 3 && !coefficients[2].is_zero() {
            let constant = coefficients[0].clone();
            let linear = coefficients[1].clone();
            let leading = coefficients[2].clone();
            let four = Rat::from_integer(BigInt::from(4));
            let discriminant = &(&linear * &linear) - &(&(&four * &leading) * &constant);
            if !discriminant.is_negative() {
                best = Some((
                    Rat::zero(),
                    AnalyticCertificate::RealQuadraticRoots {
                        leading,
                        linear,
                        constant,
                    },
                ));
                continue;
            }
            // Im² of the conjugate pair: (4ac − b²)/(4a²).
            let squared = &(-discriminant) / &(&(&four * &leading) * &leading);
            let replace = match &best {
                None => true,
                Some((current, _)) => &squared < current,
            };
            if replace {
                // The certificate names the monic form x² + (b/a) x + (c/a).
                best = Some((
                    squared,
                    AnalyticCertificate::ConjugatePair {
                        linear: &linear / &leading,
                        constant: &constant / &leading,
                    },
                ));
            }
            continue;
        }
        undecided.push(factor.factor.clone());
    }
    let Some((squared_half_width, attaining)) = best else {
        return Err(NeckRefusal::NoPoleToRead);
    };
    Ok(AnalyticWidth {
        squared_half_width,
        attaining,
        undecided,
    })
}

/// **The analytic width of a structurally placed spectrum — a certificate, not a pole reading.**
///
/// [proved-standard] When a caller's generator carries a [`RealSpectrumLicence`], every
/// eigenvalue of `A` is real; the poles of `C (sI − A)⁻¹ B` are a subset of `σ(A)`, so every pole
/// is real and the squared distance from the real axis to the nearest one is exactly `0`. **The
/// strip has closed**, at any extent, without a characteristic polynomial being formed — which is
/// the whole point: this is the arm that decides a face the pole atlas cannot reach.
///
/// `extent` is the chart the placement holds on. A placement over an empty chart places nothing,
/// and the refusal is [`NeckRefusal::NoPoleToRead`] — the same refusal an empty atlas earns, for
/// the same reason.
pub fn analytic_width_of_real_spectrum(
    licence: RealSpectrumLicence,
    extent: usize,
) -> Result<AnalyticWidth, NeckRefusal> {
    if extent == 0 {
        return Err(NeckRefusal::NoPoleToRead);
    }
    Ok(AnalyticWidth {
        squared_half_width: Rat::zero(),
        attaining: AnalyticCertificate::StructurallyPlacedOnTheRealAxis { licence, extent },
        undecided: Vec::new(),
    })
}

/// Build the atlas from a declared denominator and read its width in one step.
pub fn analytic_width_of_denominator(
    denominator: &RationalPolynomial,
) -> Result<AnalyticWidth, NeckRefusal> {
    let atlas = pole_atlas(denominator, PoleReading::Named)?;
    analytic_width(&atlas)
}

/// Which of the three widths a constitutive link names.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum WidthFace {
    /// The geometric cross-section `A`.
    Geometric,
    /// The receiver's uncertainty diameter.
    ReceiverUncertainty,
    /// The squared analytic half-width.
    Analytic,
}

/// **The only thing that relates two widths: a declared constitutive equation with a domain.**
///
/// [definition] `to = coefficient · from`, over the declared domain. The domain is carried and is
/// not checked by this owner: it is the caller's statement of where the relation holds, and the
/// residual is what the reading returns.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct ConstitutiveLink {
    lineage: String,
    domain: String,
    from: WidthFace,
    to: WidthFace,
    coefficient: Rat,
}

impl ConstitutiveLink {
    /// Declare it. A link from a face to itself declares nothing and is refused.
    pub fn declare(
        lineage: impl Into<String>,
        domain: impl Into<String>,
        from: WidthFace,
        to: WidthFace,
        coefficient: Rat,
    ) -> Result<Self, NeckRefusal> {
        if from == to {
            return Err(NeckRefusal::LinkIsIdentity);
        }
        Ok(Self {
            lineage: lineage.into(),
            domain: domain.into(),
            from,
            to,
            coefficient,
        })
    }

    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    pub fn domain(&self) -> &str {
        &self.domain
    }

    pub fn from(&self) -> WidthFace {
        self.from
    }

    pub fn to(&self) -> WidthFace {
        self.to
    }

    pub fn coefficient(&self) -> &Rat {
        &self.coefficient
    }
}

/// The three widths as one reading over one source, each still in its own type.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WidthTriple {
    pub geometric: GeometricSection,
    pub receiver: Option<ReceiverUncertaintyWidth>,
    pub analytic: Option<AnalyticWidth>,
}

impl WidthTriple {
    fn face_value(&self, face: WidthFace) -> Option<Rat> {
        match face {
            WidthFace::Geometric => Some(self.geometric.area.clone()),
            WidthFace::ReceiverUncertainty => self
                .receiver
                .as_ref()
                .map(|width| width.width.diameter().clone()),
            WidthFace::Analytic => self
                .analytic
                .as_ref()
                .map(|width| width.squared_half_width.clone()),
        }
    }
}

/// What a constitutive link's reading returned.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct LinkResidual {
    /// `coefficient · from`.
    pub predicted: Rat,
    /// The target face's own value.
    pub observed: Rat,
    /// `observed − predicted`.
    pub residual: Rat,
    /// The domain the link declared.
    pub domain: String,
}

/// **Check a declared link over one source's three widths, and return the residual.**
///
/// A face the triple does not carry makes the reading unavailable; the return is `None` and no
/// value is invented for it.
pub fn check_constitutive_link(
    link: &ConstitutiveLink,
    widths: &WidthTriple,
) -> Option<LinkResidual> {
    let from = widths.face_value(link.from)?;
    let observed = widths.face_value(link.to)?;
    let predicted = &link.coefficient * &from;
    Some(LinkResidual {
        residual: &observed - &predicted,
        predicted,
        observed,
        domain: link.domain.clone(),
    })
}

// ===============================================================================================
// 2. the tube profile: convergence in and divergence out, from one law
// ===============================================================================================

/// **A neck reading's continuing source: stations, sections, current densities and gap sources.**
///
/// [definition] `stations[i]` is the longitudinal parameter, strictly increasing.
/// `sections[i]` is `A_i` and `current_density[i]` is `j_i`, both at station `i`, so the flux
/// through station `i` is `Φ_i = A_i · j_i`. `sources[i]` is the net source injected into the
/// control volume **between** stations `i` and `i+1`, so there are `n − 1` of them.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "TubeProfileWire")]
pub struct TubeProfile {
    lineage: String,
    stations: Vec<Rat>,
    sections: Vec<GeometricSection>,
    current_density: Vec<Rat>,
    sources: Vec<Rat>,
}

#[derive(Deserialize)]
struct TubeProfileWire {
    lineage: String,
    stations: Vec<Rat>,
    sections: Vec<GeometricSection>,
    current_density: Vec<Rat>,
    sources: Vec<Rat>,
}

impl TryFrom<TubeProfileWire> for TubeProfile {
    type Error = NeckRefusal;

    fn try_from(wire: TubeProfileWire) -> Result<Self, Self::Error> {
        Self::declare(
            wire.lineage,
            wire.stations,
            wire.sections,
            wire.current_density,
            wire.sources,
        )
    }
}

impl TubeProfile {
    /// Declare it. The station count is bounded against [`STATION_CEILING`] **before** any vector
    /// is sized by it, the station parameter must be strictly increasing, and the four declared
    /// lengths must agree.
    pub fn declare(
        lineage: impl Into<String>,
        stations: Vec<Rat>,
        sections: Vec<GeometricSection>,
        current_density: Vec<Rat>,
        sources: Vec<Rat>,
    ) -> Result<Self, NeckRefusal> {
        if stations.len() > STATION_CEILING {
            return Err(NeckRefusal::StationsBeyondCeiling {
                declared: stations.len(),
                ceiling: STATION_CEILING,
            });
        }
        if stations.len() < 2 {
            return Err(NeckRefusal::TooFewStations {
                declared: stations.len(),
            });
        }
        let gaps = stations.len() - 1;
        if sections.len() != stations.len()
            || current_density.len() != stations.len()
            || sources.len() != gaps
        {
            return Err(NeckRefusal::ProfileShapeMismatch {
                stations: stations.len(),
                sections: sections.len(),
                densities: current_density.len(),
                sources: sources.len(),
                gaps,
            });
        }
        for at in 1..stations.len() {
            if stations[at] <= stations[at - 1] {
                return Err(NeckRefusal::StationsNotIncreasing { at });
            }
        }
        Ok(Self {
            lineage: lineage.into(),
            stations,
            sections,
            current_density,
            sources,
        })
    }

    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    pub fn stations(&self) -> &[Rat] {
        &self.stations
    }

    pub fn sections(&self) -> &[GeometricSection] {
        &self.sections
    }

    pub fn current_density(&self) -> &[Rat] {
        &self.current_density
    }

    pub fn sources(&self) -> &[Rat] {
        &self.sources
    }

    pub fn station_count(&self) -> usize {
        self.stations.len()
    }

    /// `Φ_i = A_i · j_i`, the flux through station `i`.
    pub fn flux(&self, station: usize) -> Option<Rat> {
        Some(&self.sections.get(station)?.area * self.current_density.get(station)?)
    }

    /// Every station's flux.
    pub fn fluxes(&self) -> Vec<Rat> {
        (0..self.stations.len())
            .map(|station| {
                &self.sections[station].area * &self.current_density[station]
            })
            .collect()
    }

    /// **The neck: `argmin A_i`, first attaining.**
    pub fn neck_index(&self) -> usize {
        let mut best = 0;
        for (at, section) in self.sections.iter().enumerate() {
            if section.area < self.sections[best].area {
                best = at;
            }
        }
        best
    }

    /// **What re-opens after the neck**: the first station past the neck whose section strictly
    /// exceeds the neck's, with the exact widening, or `None` when nothing after it widens.
    pub fn reopening(&self) -> Option<(usize, Rat)> {
        let neck = self.neck_index();
        let minimum = &self.sections[neck].area;
        for at in neck + 1..self.sections.len() {
            if &self.sections[at].area > minimum {
                return Some((at, &self.sections[at].area - minimum));
            }
        }
        None
    }

    /// **The typed reading at the neck, at a declared receiver grain.**
    ///
    /// `interior_plurality` is a **caller declaration, carried and not verified**: what the caller
    /// says the section still holds inside, below the receiver's grain. This owner has no way to
    /// derive it from sections and densities alone. A consumer that can compute it should — the
    /// optical train does through [`OpticalTrain::plural_at`], and `holonic_chain` does from the
    /// ranks of the media beside the neck — and pass the computed value here.
    pub fn neck_reading(&self, grain: &Rat, interior_plurality: &Rat) -> NeckReading {
        let neck = self.neck_index();
        let area = self.sections[neck].area.clone();
        if area.is_zero() {
            return NeckReading::Closed {
                station: neck,
                flux: self.flux(neck).unwrap_or_else(Rat::zero),
            };
        }
        if &area <= grain {
            NeckReading::Pinhole {
                station: neck,
                section: area,
                grain: grain.clone(),
                interior_plurality: interior_plurality.clone(),
            }
        } else {
            NeckReading::Open {
                station: neck,
                section: area,
                grain: grain.clone(),
            }
        }
    }

    /// **`j_i = Φ / A_i`, and it rises exactly as the section narrows.**
    ///
    /// Available **only** on a sourceless tube: with any declared source the law that implies the
    /// speed-up does not hold and the refusal names the offending gap. A zero section is refused
    /// by name rather than divided into.
    pub fn speedup(&self) -> Result<SpeedupReading, NeckRefusal> {
        if let Some((at, source)) = self
            .sources
            .iter()
            .enumerate()
            .find(|(_, source)| !source.is_zero())
        {
            return Err(NeckRefusal::SpeedupNeedsNoSource {
                at,
                injected: source.to_string(),
            });
        }
        if let Some((at, _)) = self
            .sections
            .iter()
            .enumerate()
            .find(|(_, section)| section.area.is_zero())
        {
            return Err(NeckRefusal::ZeroSectionHasNoDensity { at });
        }
        let fluxes = self.fluxes();
        let flux = fluxes[0].clone();
        let constant = fluxes.iter().all(|value| *value == flux);
        let implied: Vec<Rat> = self
            .sections
            .iter()
            .map(|section| &flux / &section.area)
            .collect();
        let neck = self.neck_index();
        // Monotone into the neck and out of it, checked on the implied densities rather than
        // inferred from the word "narrowing".
        let rises_into = (1..=neck).all(|at| implied[at] >= implied[at - 1]);
        let falls_after =
            (neck + 1..implied.len()).all(|at| implied[at] <= implied[at - 1]);
        Ok(SpeedupReading {
            flux,
            flux_is_constant: constant,
            implied_density: implied,
            neck,
            rises_into_the_neck: rises_into,
            falls_after_the_neck: falls_after,
        })
    }

    /// **The per-gap transport residual, computed by `junction_law`.**
    ///
    /// The complex: one node per control volume between consecutive stations, two exterior nodes
    /// for the ends, one branch per station carrying `Φ_i`. `check_junction` takes the interface
    /// whose joint is every control volume; its divergence at a gap is `Φ_i − Φ_{i+1}`, so the
    /// returned residual is that reading negated into `Φ_{i+1} − Φ_i − σ_i`.
    pub fn station_balance(&self) -> Result<StationBalance, NeckRefusal> {
        let stations = self.stations.len();
        let gaps = stations - 1;
        // Nodes: `0 … gaps-1` are the control volumes, `gaps` is the inlet, `gaps+1` the outlet.
        let inlet = gaps;
        let outlet = gaps + 1;
        let mut branches = Vec::with_capacity(stations);
        branches.push((inlet, 0usize, Rat::one()));
        for gap in 1..gaps {
            branches.push((gap - 1, gap, Rat::one()));
        }
        branches.push((gaps - 1, outlet, Rat::one()));
        let network = ResistiveNetwork::declare(
            format!("{}|control-volumes", self.lineage),
            gaps + 2,
            &branches,
        )?;
        let operator = network.operator();
        let fluxes = self.fluxes();
        // The junction reading's source is the divergence's own orientation, which is inflow minus
        // outflow; the profile declares the injected source, so it enters negated. Exterior nodes
        // carry whatever the ends carry and are not part of the joint.
        let mut source = vec![Rat::zero(); operator.extent(0)];
        for (gap, injected) in self.sources.iter().enumerate() {
            source[gap] = -injected.clone();
        }
        source[inlet] = -fluxes[0].clone();
        source[outlet] = fluxes[stations - 1].clone();
        let joint: BTreeSet<CausalCellId> =
            (0..gaps).map(|gap| operator.cells(0)[gap]).collect();
        let sides = operator
            .cells(1)
            .iter()
            .enumerate()
            .map(|(at, cell)| {
                (
                    *cell,
                    if at == 0 { Side::Left } else { Side::Right },
                )
            })
            .collect();
        let interface = Interface::declare(
            format!("{}|neck-balance", self.lineage),
            operator,
            0,
            sides,
            joint,
        )?;
        let potential = vec![Rat::zero(); operator.extent(0)];
        let verdict = check_junction(
            operator,
            &interface,
            &JunctionField {
                potential: &potential,
                field: &fluxes,
                source: &source,
            },
            network.units(),
        )?;
        // `Φ_{i+1} − Φ_i − σ_i`: the junction reading negated once into the plan's orientation.
        let residual = (0..gaps)
            .map(|gap| &(&fluxes[gap + 1] - &fluxes[gap]) - &self.sources[gap])
            .collect();
        Ok(StationBalance {
            verdict,
            residual,
            gaps,
        })
    }

    /// **Carry the reading along a strictly increasing reparametrization of the station
    /// parameter.** Everything transverse is unchanged; only the coordinates move.
    pub fn reparametrized(&self, stations: Vec<Rat>) -> Result<Self, NeckRefusal> {
        Self::declare(
            format!("{}|reparametrized", self.lineage),
            stations,
            self.sections.clone(),
            self.current_density.clone(),
            self.sources.clone(),
        )
    }

    /// **Run the chain backwards.**
    ///
    /// The station parameter is negated and reversed so it stays strictly increasing, the sections
    /// and gap sources reverse, and the current density reverses **and changes sign**: flux
    /// through an oriented face is signed, and reversing the orientation flips it.
    pub fn reversed(&self) -> Result<Self, NeckRefusal> {
        let stations = self
            .stations
            .iter()
            .rev()
            .map(|value| -value.clone())
            .collect();
        let sections = self.sections.iter().rev().cloned().collect();
        let current_density = self
            .current_density
            .iter()
            .rev()
            .map(|value| -value.clone())
            .collect();
        let sources = self.sources.iter().rev().map(|value| -value.clone()).collect();
        Self::declare(
            format!("{}|reversed", self.lineage),
            stations,
            sections,
            current_density,
            sources,
        )
    }

    /// The orientation bit a reversal carries, which is `junction_law`'s. A reversal of the
    /// station parameter is one reflection of the longitudinal axis, and
    /// `junction_law::reflection_circuit_determinant(1) = −1` is that bit; the witness is the pair
    /// of end stations whose order the reversal exchanged.
    pub fn reversal_orientation(&self) -> OrientationBit {
        OrientationBit::Reversing {
            witness: vec![(
                format!("{}|station-0", self.lineage),
                format!("{}|station-{}", self.lineage, self.stations.len() - 1),
            )],
        }
    }
}

/// The typed reading at the neck.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub enum NeckReading {
    /// The section exceeds the receiver's grain: the tube is open here.
    Open {
        station: usize,
        section: Rat,
        grain: Rat,
    },
    /// **The pinhole.** A single point at the receiver's grain while plural inside — the width-zero
    /// condition of `receiver_release` with the plurality retained, which is release.
    Pinhole {
        station: usize,
        section: Rat,
        grain: Rat,
        interior_plurality: Rat,
    },
    /// A zero section. The flux through it is returned rather than assumed to vanish: if it is
    /// nonzero the declaration is inconsistent and the value is the evidence.
    Closed { station: usize, flux: Rat },
}

impl NeckReading {
    /// The station this reading is at.
    pub fn station(&self) -> usize {
        match self {
            Self::Open { station, .. }
            | Self::Pinhole { station, .. }
            | Self::Closed { station, .. } => *station,
        }
    }

    /// The arm's name, for a receipt.
    pub fn arm(&self) -> &'static str {
        match self {
            Self::Open { .. } => "open",
            Self::Pinhole { .. } => "pinhole",
            Self::Closed { .. } => "closed",
        }
    }
}

/// What the sourceless speed-up reading returned.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct SpeedupReading {
    /// The flux at the first station.
    pub flux: Rat,
    /// Whether the declared fluxes really are constant along the tube.
    pub flux_is_constant: bool,
    /// `Φ / A_i` at every station.
    pub implied_density: Vec<Rat>,
    /// The neck's index.
    pub neck: usize,
    /// Whether the implied density is nondecreasing up to the neck.
    pub rises_into_the_neck: bool,
    /// Whether it is nonincreasing after it.
    pub falls_after_the_neck: bool,
}

/// What the station balance returned.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct StationBalance {
    /// `junction_law`'s own verdict, whole.
    pub verdict: JunctionVerdict,
    /// `Φ_{i+1} − Φ_i − σ_i` at every control volume.
    pub residual: Vec<Rat>,
    /// How many control volumes were read.
    pub gaps: usize,
}

impl StationBalance {
    /// Whether every control volume balanced.
    pub fn is_balanced(&self) -> bool {
        self.residual.iter().all(Zero::is_zero)
    }
}

// ===============================================================================================
// 3. the neck is a station of the existing tube
// ===============================================================================================

/// The transverse section a neck tube presents at one station: one chart, carrying the flux.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NeckSection;

impl Tower for NeckSection {
    type Index = usize;
    type Face = Rat;

    fn refines(&self, coarse: &usize, fine: &usize) -> bool {
        coarse == fine
    }

    fn carries(&self, chart: &usize, _face: &Rat) -> bool {
        *chart == 0
    }

    fn restrict(&self, coarse: &usize, fine: &usize, face: &Rat) -> TowerFaceOutcome<Self> {
        if coarse == fine {
            Ok(face.clone())
        } else {
            Err(TowerRefusal::NotARefinement {
                coarse: *coarse,
                fine: *fine,
            })
        }
    }
}

/// **The neck as a station of `continuing_tube`'s tube, not of a second one.**
///
/// [definition] The face carried along the tube is the flux. One longitudinal step adds the gap's
/// declared source — signed, so it cancels on a round trip — and subtracts the gap's declared
/// **wall loss**, which is nonnegative and subtracted in *either* direction. A sealed wall
/// therefore has identity holonomy around the neck, and a dissipative one does not: that defect is
/// the chain's irreversibility read as tube holonomy, and `check_circuit_holonomy` is what returns
/// it.
///
/// `follows` holds between any two declared stations because the steady flux law is invertible;
/// the orientation of the chain is carried by [`TubeProfile::reversed`] and
/// [`OrientationBit`](crate::junction_law::OrientationBit), not by the reachability relation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NeckTube {
    profile: TubeProfile,
    wall_loss: Vec<Rat>,
    section: NeckSection,
}

impl NeckTube {
    /// Declare the tube over a profile and a per-gap nonnegative wall loss.
    pub fn declare(profile: TubeProfile, wall_loss: Vec<Rat>) -> Result<Self, NeckRefusal> {
        let gaps = profile.stations.len() - 1;
        if wall_loss.len() != gaps {
            return Err(NeckRefusal::ProfileShapeMismatch {
                stations: profile.stations.len(),
                sections: profile.sections.len(),
                densities: profile.current_density.len(),
                sources: wall_loss.len(),
                gaps,
            });
        }
        if let Some(loss) = wall_loss.iter().find(|loss| loss.is_negative()) {
            return Err(NeckRefusal::NegativeWallLoss {
                loss: loss.to_string(),
            });
        }
        Ok(Self {
            profile,
            wall_loss,
            section: NeckSection,
        })
    }

    /// A sealed tube: every wall loss zero.
    pub fn sealed(profile: TubeProfile) -> Result<Self, NeckRefusal> {
        let gaps = profile.stations.len() - 1;
        Self::declare(profile, vec![Rat::zero(); gaps])
    }

    pub fn profile(&self) -> &TubeProfile {
        &self.profile
    }

    pub fn wall_loss(&self) -> &[Rat] {
        &self.wall_loss
    }

    /// The holonomy of the circuit that runs from a station to the neck and back, read by
    /// `continuing_tube`'s own checker on the declared flux face.
    pub fn holonomy_around_the_neck(
        &self,
        from: usize,
        face: Rat,
    ) -> TubeOutcome<Self, holonics::restriction::tube::HolonomyVerdict<usize, usize, Rat>> {
        let neck = self.profile.neck_index();
        check_circuit_holonomy(self, &[from, neck, from], &[0usize], &[(0usize, face)])
    }
}

impl StationedTower for NeckTube {
    type Station = usize;
    type Section = NeckSection;

    fn follows(&self, earlier: &usize, later: &usize) -> bool {
        *earlier < self.profile.stations.len() && *later < self.profile.stations.len()
    }

    fn section(&self, station: &usize) -> Option<&NeckSection> {
        if *station < self.profile.stations.len() {
            Some(&self.section)
        } else {
            None
        }
    }

    fn transport(
        &self,
        earlier: &usize,
        later: &usize,
        chart: &usize,
        face: &Rat,
    ) -> TubeOutcome<Self, Rat> {
        if *chart != 0 {
            return Err(TubeRefusal::Section(TowerRefusal::FaceNotCarried {
                chart: *chart,
                face: face.clone(),
            }));
        }
        if !self.follows(earlier, later) {
            return Err(TubeRefusal::NotAStep {
                earlier: *earlier,
                later: *later,
            });
        }
        let mut carried = face.clone();
        if earlier <= later {
            for gap in *earlier..*later {
                carried = &carried + &self.profile.sources[gap] - &self.wall_loss[gap];
            }
        } else {
            for gap in (*later..*earlier).rev() {
                carried = &carried - &self.profile.sources[gap] - &self.wall_loss[gap];
            }
        }
        Ok(carried)
    }
}

/// Whether a holonomy verdict is the identity one, without the caller matching on the enum.
pub fn holonomy_is_identity(verdict: &HolonomyVerdict<usize, usize, Rat>) -> bool {
    verdict.is_identity()
}

/// The receiver that reads a neck tube's flux face, as `continuing_tube`'s own `FaceReading`.
///
/// [definition] The return is `receiver_release`'s [`ExactFace`], so the diameter law is that
/// owner's and is not written a second time here.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FluxReading {
    receiver: String,
}

impl FluxReading {
    pub fn declare(receiver: impl Into<String>) -> Self {
        Self {
            receiver: receiver.into(),
        }
    }
}

impl FaceReading<NeckTube> for FluxReading {
    fn name(&self) -> &str {
        &self.receiver
    }

    fn read(&self, _station: &usize, _chart: &usize, face: &Rat) -> Result<ExactFace, WidthRefusal> {
        Ok(ExactFace::Vector(vec![face.clone()]))
    }
}

/// **The neck's receiver uncertainty width over the two-axis horizon `(h, k)`.**
///
/// [definition] Composes `continuing_tube`'s [`horizon_reach`] and [`two_axis_width`], which are
/// `receiver_release`'s own width taken over everything the declared horizon reaches. The `(h, k)`
/// pair is `receiver_release`'s [`Horizon`] and is the longitudinal station and the grain index —
/// **not** the time/entropy pair. The returned width is wrapped so a caller cannot confuse it with
/// the geometric section: they meet only through a [`ConstitutiveLink`].
pub fn neck_two_axis_width(
    tube: &NeckTube,
    observer_station: usize,
    horizon: Horizon,
    entry_flux: Rat,
    receiver: &FluxReading,
) -> Result<ReceiverUncertaintyWidth, NeckRefusal> {
    let stations: Vec<usize> = (0..tube.profile.stations.len()).collect();
    let declaration = HorizonDeclaration::declare(
        Observer::at(observer_station, 0usize),
        horizon,
        stations,
        vec![0usize],
        vec![(0usize, entry_flux.clone())],
    )
    .map_err(|refusal| NeckRefusal::Horizon {
        reason: format!("{refusal:?}"),
    })?;
    let reach = horizon_reach(tube, &declaration, &entry_flux, &[(0usize, entry_flux.clone())])
        .map_err(|refusal| NeckRefusal::Horizon {
            reason: format!("{refusal:?}"),
        })?;
    let width = two_axis_width(receiver, &reach, DiameterNorm::Supremum)?;
    Ok(ReceiverUncertaintyWidth::declare(
        width,
        format!(
            "the two-axis horizon (h = {}, k = {}) at station {observer_station}",
            horizon.longitudinal(),
            horizon.index()
        ),
    ))
}

// ===============================================================================================
// 4. the optical instance
// ===============================================================================================

/// **An exact `2×2` rational ray-transfer matrix on `(height, angle)`.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct RayTransfer {
    lineage: String,
    matrix: ExactRatMatrix,
    determinant: Rat,
}

impl RayTransfer {
    /// Declare an arbitrary `2×2` transfer; the determinant is computed, not declared.
    pub fn declare(
        lineage: impl Into<String>,
        matrix: ExactRatMatrix,
    ) -> Result<Self, NeckRefusal> {
        if matrix.rows() != 2 || matrix.columns() != 2 {
            return Err(NeckRefusal::RayTransferNotTwoByTwo {
                rows: matrix.rows(),
                columns: matrix.columns(),
            });
        }
        let determinant = &(matrix.get(0, 0)? * matrix.get(1, 1)?)
            - &(matrix.get(0, 1)? * matrix.get(1, 0)?);
        Ok(Self {
            lineage: lineage.into(),
            matrix,
            determinant,
        })
    }

    /// Declare a transfer that must be unimodular; a non-unimodular one is refused by name.
    pub fn unimodular(
        lineage: impl Into<String>,
        matrix: ExactRatMatrix,
    ) -> Result<Self, NeckRefusal> {
        let transfer = Self::declare(lineage, matrix)?;
        if !transfer.determinant.is_one() {
            return Err(NeckRefusal::RayTransferNotUnimodular {
                determinant: transfer.determinant.to_string(),
            });
        }
        Ok(transfer)
    }

    /// Free propagation over a declared reduced distance: `[[1, d], [0, 1]]`, determinant `1`.
    pub fn free_space(distance: &Rat) -> Result<Self, NeckRefusal> {
        Self::declare(
            "optical|free-space",
            ExactRatMatrix::new(vec![
                vec![Rat::one(), distance.clone()],
                vec![Rat::zero(), Rat::one()],
            ])?,
        )
    }

    /// A thin lens of declared focal length: `[[1, 0], [−1/f, 1]]`, determinant `1`. A zero focal
    /// length is refused rather than divided by.
    pub fn thin_lens(focal: &Rat) -> Result<Self, NeckRefusal> {
        if focal.is_zero() {
            return Err(NeckRefusal::ZeroFocalLength);
        }
        Self::declare(
            "optical|thin-lens",
            ExactRatMatrix::new(vec![
                vec![Rat::one(), Rat::zero()],
                vec![-(Rat::one() / focal), Rat::one()],
            ])?,
        )
    }

    /// A planar refracting interface between two media: `[[1, 0], [0, n₁/n₂]]`, determinant
    /// `n₁/n₂`. **Not** unimodular, and the type carries the determinant rather than hiding it —
    /// what is conserved across it is the reduced étendue `n · (phase area)`.
    pub fn refracting_interface(from_index: &Rat, to_index: &Rat) -> Result<Self, NeckRefusal> {
        for index in [from_index, to_index] {
            if !index.is_positive() {
                return Err(NeckRefusal::NonPositiveIndex {
                    index: index.to_string(),
                });
            }
        }
        Self::declare(
            "optical|interface",
            ExactRatMatrix::new(vec![
                vec![Rat::one(), Rat::zero()],
                vec![Rat::zero(), from_index / to_index],
            ])?,
        )
    }

    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    pub fn matrix(&self) -> &ExactRatMatrix {
        &self.matrix
    }

    pub fn determinant(&self) -> &Rat {
        &self.determinant
    }

    pub fn is_unimodular(&self) -> bool {
        self.determinant.is_one()
    }

    /// `next ∘ self`: the ray meets `self` first. Determinants multiply, and that is checked here
    /// rather than assumed.
    pub fn then(&self, next: &Self) -> Result<Self, NeckRefusal> {
        let composed = Self::declare(
            format!("{} -> {}", self.lineage, next.lineage),
            next.matrix.multiply(&self.matrix)?,
        )?;
        debug_assert_eq!(
            composed.determinant,
            &self.determinant * &next.determinant,
            "invariant: the determinant of a composite is the product"
        );
        Ok(composed)
    }
}

/// **A declared input ray bundle: a box in `(height, angle)`, carried as `receiver_release`'s own
/// enclosure.**
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RayBundle {
    lineage: String,
    half_height: Rat,
    half_angle: Rat,
    index: Rat,
    hull: ExactZonotope,
}

impl RayBundle {
    /// Declare it. Both half-extents must be nonnegative and at least one strictly positive: a
    /// bundle with no extent at all is a single ray and has no width to follow.
    pub fn declare(
        lineage: impl Into<String>,
        half_height: Rat,
        half_angle: Rat,
        index: Rat,
    ) -> Result<Self, NeckRefusal> {
        if half_height.is_negative() {
            return Err(NeckRefusal::NegativeBundleExtent {
                which: "half-height",
                value: half_height.to_string(),
            });
        }
        if half_angle.is_negative() {
            return Err(NeckRefusal::NegativeBundleExtent {
                which: "half-angle",
                value: half_angle.to_string(),
            });
        }
        if half_height.is_zero() && half_angle.is_zero() {
            return Err(NeckRefusal::DegenerateBundle);
        }
        if !index.is_positive() {
            return Err(NeckRefusal::NonPositiveIndex {
                index: index.to_string(),
            });
        }
        let hull = ExactZonotope::box_hull(
            vec![Rat::zero(), Rat::zero()],
            &[half_height.clone(), half_angle.clone()],
        )?;
        Ok(Self {
            lineage: lineage.into(),
            half_height,
            half_angle,
            index,
            hull,
        })
    }

    /// A point source: zero half-height, a declared angular spread. The focus of a train acting on
    /// it is exactly where the `B` element vanishes.
    pub fn point_source(
        lineage: impl Into<String>,
        half_angle: Rat,
        index: Rat,
    ) -> Result<Self, NeckRefusal> {
        Self::declare(lineage, Rat::zero(), half_angle, index)
    }

    pub fn half_height(&self) -> &Rat {
        &self.half_height
    }

    pub fn half_angle(&self) -> &Rat {
        &self.half_angle
    }

    pub fn index(&self) -> &Rat {
        &self.index
    }

    /// The enclosure, as `receiver_release` carries it.
    pub fn hull(&self) -> &ExactZonotope {
        &self.hull
    }

    /// The compatible family this bundle is, in `receiver_release`'s own type.
    pub fn family(&self) -> CompatibleFamily {
        CompatibleFamily::enclosed(self.lineage.clone(), self.hull.clone())
    }
}

/// One station of an optical train.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpticalStation {
    /// What the ray has passed through by here.
    pub lineage: String,
    /// The cumulative transfer.
    pub transfer: RayTransfer,
    /// The refractive index of the medium here.
    pub index: Rat,
    /// The transverse half-extent, taken by `receiver_release`'s own width on the mapped hull.
    pub transverse_half_extent: Rat,
    /// The angular half-extent, same reading on the other coordinate.
    pub angular_half_extent: Rat,
    /// `receiver_release`'s width of the height reading over the mapped family.
    pub receiver_width: ReceiverWidth,
    /// Four times the absolute determinant of the two generators: the phase-space area. A
    /// point-source bundle carries one generator and therefore zero area — correctly, and the
    /// field says so rather than inventing one.
    pub phase_area: Rat,
    /// `n · phase_area`: the reduced phase-space area.
    pub reduced_etendue: Rat,
    /// **`n · det(ABCD)`, the étendue invariant.** Unimodular elements inside one medium leave it
    /// alone; across an interface the determinant is `n₁/n₂` exactly as the index becomes `n₂`,
    /// so the product is the *entry* index at every station — including at a focus, where the
    /// transverse extent has vanished.
    pub etendue_invariant: Rat,
}

/// A whole optical train, station by station.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct OpticalTrain {
    stations: Vec<OpticalStation>,
}

impl OpticalTrain {
    pub fn stations(&self) -> &[OpticalStation] {
        &self.stations
    }

    /// **The focus: the first station where the transverse half-extent vanishes.**
    pub fn focus(&self) -> Option<usize> {
        self.stations
            .iter()
            .position(|station| station.transverse_half_extent.is_zero())
    }

    /// **Every station where the transverse half-extent vanishes.** For a point source that is the
    /// object point and its images: the bundle is a point at each of them and plural between, and
    /// the list returns all of them rather than choosing one.
    pub fn foci(&self) -> Vec<usize> {
        self.stations
            .iter()
            .enumerate()
            .filter(|(_, station)| station.transverse_half_extent.is_zero())
            .map(|(at, _)| at)
            .collect()
    }

    /// **Whether the étendue invariant `n · det` is the same at every station** — conserved
    /// through the neck, including at the focus where the geometric width is zero.
    pub fn etendue_conserved(&self) -> bool {
        let Some(first) = self.stations.first() else {
            return false;
        };
        self.stations
            .iter()
            .all(|station| station.etendue_invariant == first.etendue_invariant)
    }

    /// Whether the reduced phase-space area is the same at every station. For a two-generator
    /// bundle this is the literal étendue; for a point source it is zero throughout.
    pub fn reduced_area_conserved(&self) -> bool {
        let Some(first) = self.stations.first() else {
            return false;
        };
        self.stations
            .iter()
            .all(|station| station.reduced_etendue == first.reduced_etendue)
    }

    /// Whether the bundle is still plural at a station whose transverse extent has vanished: the
    /// angular half-extent is strictly positive there. That is "a point at the receiver's grain
    /// while plural inside".
    pub fn plural_at(&self, station: usize) -> Option<bool> {
        let entry = self.stations.get(station)?;
        Some(entry.transverse_half_extent.is_zero() && entry.angular_half_extent.is_positive())
    }
}

/// **Run a declared bundle through a declared train of elements, exactly.**
///
/// Each element carries the refractive index of the medium it leads into, so a refracting
/// interface's determinant and the medium's index move together and the reduced étendue can be
/// checked across it.
pub fn optical_train(
    bundle: &RayBundle,
    elements: &[(String, RayTransfer, Rat)],
) -> Result<OpticalTrain, NeckRefusal> {
    if elements.len() > OPTICAL_ELEMENT_CEILING {
        return Err(NeckRefusal::OpticalBeyondCeiling {
            declared: elements.len(),
            ceiling: OPTICAL_ELEMENT_CEILING,
        });
    }
    let identity = RayTransfer::declare("optical|entry", ExactRatMatrix::identity(2)?)?;
    let mut cumulative = identity;
    let mut index = bundle.index.clone();
    let mut stations = Vec::with_capacity(elements.len() + 1);
    stations.push(optical_station("entry", &cumulative, &index, bundle)?);
    for (name, element, medium_index) in elements {
        if !medium_index.is_positive() {
            return Err(NeckRefusal::NonPositiveIndex {
                index: medium_index.to_string(),
            });
        }
        cumulative = cumulative.then(element)?;
        index = medium_index.clone();
        stations.push(optical_station(name, &cumulative, &index, bundle)?);
    }
    Ok(OpticalTrain { stations })
}

fn optical_station(
    name: &str,
    cumulative: &RayTransfer,
    index: &Rat,
    bundle: &RayBundle,
) -> Result<OpticalStation, NeckRefusal> {
    let mapped = bundle.hull.mapped(&cumulative.matrix)?;
    let transverse = mapped.coordinate_half_extent(0)?;
    let angular = mapped.coordinate_half_extent(1)?;
    // The height reading, taken by `receiver_release` itself over the mapped family.
    let reading = LinearReading {
        receiver: format!("{name}|height"),
        matrix: ExactRatMatrix::new(vec![vec![Rat::one(), Rat::zero()]])?,
    };
    let family = CompatibleFamily::enclosed(format!("{name}|bundle"), mapped.clone());
    let receiver_width = width_enclosed(&reading, &family, DiameterNorm::Supremum)?;
    // The phase-space area of a two-generator zonotope is `4 |det[g₁ g₂]|`.
    let generators = mapped.generators();
    let phase_area = if generators.len() == 2 {
        let left = &generators[0].column;
        let right = &generators[1].column;
        let determinant = &(&left[0] * &right[1]) - &(&left[1] * &right[0]);
        &Rat::from_integer(BigInt::from(4)) * &determinant.abs()
    } else {
        Rat::zero()
    };
    Ok(OpticalStation {
        lineage: name.to_owned(),
        etendue_invariant: index * cumulative.determinant(),
        transfer: cumulative.clone(),
        index: index.clone(),
        transverse_half_extent: transverse,
        angular_half_extent: angular,
        receiver_width,
        reduced_etendue: index * &phase_area,
        phase_area,
    })
}

// ===============================================================================================
// 5. the neck invariants, assembled over one source, each with its domain
// ===============================================================================================

/// The jet order at the neck, read from `jet_staircase`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct JetOrderAtNeck {
    /// The order of vanishing of `A(s) − A_min` at the neck. A lens pinhole is `1`; a cusp is
    /// higher. `None` when every declared coefficient vanished and the order is undecided at the
    /// declared jet order.
    pub order: Option<usize>,
    /// What the jet was taken of.
    pub of: String,
    /// The jet order the reading was taken at, so `None` above is bounded rather than bare.
    pub read_to: usize,
}

/// **Read the jet order at the neck**: the order of vanishing of `A(s) − A_min`, from
/// `jet_staircase`'s own [`FiniteJet::vanishing_order`]. The order is a property of the declared
/// truncation and of nothing else: `Transport/Neck.lean::neck_jet_order_is_a_truncation_reading`
/// over `Transport/JetStaircase.lean::truncate_eq_iff`.
pub fn jet_order_at_neck(
    section_jet: &FiniteJet,
    minimum: &Rat,
    of: impl Into<String>,
) -> JetOrderAtNeck {
    let shifted = section_jet.shifted_by(minimum);
    JetOrderAtNeck {
        order: shifted.vanishing_order(),
        of: of.into(),
        read_to: section_jet.order(),
    }
}

/// The growth exponent at a pinch, from `iwasawa_tower`'s own specialization.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct PinchGrowth {
    pub prime: u64,
    pub level: u32,
    /// `e_n`: a growth exponent of an order, which is what that owner returns and calls it.
    pub growth_exponent: u64,
}

/// Read the growth exponent of a declared `Λ`-presentation at a declared level.
pub fn pinch_growth(
    presentation: &LambdaPresentation,
    prime: u64,
    level: u32,
) -> Result<PinchGrowth, NeckRefusal> {
    let iwasawa_level = IwasawaLevel::new(prime, level)?;
    let specialization = presentation.specialize(&iwasawa_level)?;
    Ok(PinchGrowth {
        prime,
        level,
        growth_exponent: specialization.growth_exponent(),
    })
}

/// The linking number across a declared embedding, from `topological_receiver`.
pub fn neck_linking(
    left: &ClosedPolygon,
    right: &ClosedPolygon,
    direction: &ProjectionDirection,
) -> Result<i64, NeckRefusal> {
    Ok(linking_number(left, right, direction)?.linking_number)
}

/// **A neck certificate: a reading with its declared receiver scope, and no gate.**
///
/// [definition] It names the receiver it was taken for. Nothing in this owner consumes a
/// certificate in order to permit or forbid the output of a generated face, and there is no
/// function here that takes one and returns a permission.
#[derive(Clone, Debug, PartialEq, Eq, Serialize)]
pub struct NeckCertificate {
    /// The receiver whose scope this reading is inside.
    pub receiver_scope: String,
    /// What the reading says.
    pub statement: String,
    /// The station it was taken at.
    pub station: usize,
}

/// **Every neck invariant assembled over the same source, each with its declared domain.**
///
/// [definition] Absent invariants are `None` and are named in [`Self::open_invariants`]; nothing
/// is defaulted. The prime/p-adic neck, the pinching analyticity strip, the vortex interaction and
/// the whip are `[interpretation]`: `growth` is the one that falls out exactly, through
/// `iwasawa_tower`'s own specialization, and the remaining three are listed by
/// [`Self::open_invariants`] with the owners they would compose.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NeckInvariants {
    pub lineage: String,
    pub station: usize,
    pub widths: WidthTriple,
    /// The holonomy around the neck, from `continuing_tube`.
    pub holonomy_is_identity: Option<bool>,
    /// The linking number, when an embedding was declared.
    pub linking: Option<i64>,
    /// The growth exponent at a pinch, when a `Λ`-presentation was declared.
    pub growth: Option<PinchGrowth>,
    /// The jet order at the neck, from `jet_staircase`.
    pub jet_order: JetOrderAtNeck,
    /// The declared domain of every invariant present, by name.
    pub domains: BTreeMap<String, String>,
}

impl NeckInvariants {
    /// The invariants this reading did **not** take, by name, with the owner each would compose.
    /// A list, not a refusal: an absent reading is an open fibre, not a failure.
    pub fn open_invariants(&self) -> Vec<(&'static str, &'static str)> {
        let mut open = Vec::new();
        if self.widths.receiver.is_none() {
            open.push((
                "receiver uncertainty width",
                "receiver_release::width_enclosed",
            ));
        }
        if self.widths.analytic.is_none() {
            open.push(("analytic width", "causal_chord::pole_atlas"));
        }
        if self.holonomy_is_identity.is_none() {
            open.push(("holonomy", "continuing_tube::check_circuit_holonomy"));
        }
        if self.linking.is_none() {
            open.push(("linking", "topological_receiver::linking_number"));
        }
        if self.growth.is_none() {
            open.push(("growth exponent at a pinch", "iwasawa_tower::specialize"));
        }
        open
    }
}

#[cfg(test)]
mod tests;
