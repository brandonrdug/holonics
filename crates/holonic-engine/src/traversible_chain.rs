//! The chain of interactions, over exact rationals — the arithmetic half of
//! `blueprint/THE_TRAVERSIBLE_CHAIN.md`.
//!
//! [`holonic_structure`] owns the shape: a link that weighs and gates separately, a chain with both
//! ends open that retains what did not connect, and the cocycle law as a trait contract. This module
//! supplies the carrier that shape is instantiated at, and every number in it is a `Rat`.
//!
//! # The junction law is the whip, and it was already built
//!
//! ```text
//!   Γ = (Y_i − Y_t) / (Y_i + Y_t)          reflection
//!   τ = 2 Y_i       / (Y_i + Y_t)          transmission
//! ```
//!
//! is Fresnel at normal incidence, the transmission-line reflection coefficient, and the Smith
//! chart — one law — and `analytic_field::exact_scalar_interface_coefficients` already computes it
//! exactly over `Rat`, refusing non-positive admittance. A taper whose admittances change slowly is
//! **adiabatic**: every link transmits nearly whole, each is a rebase with a small remainder, and
//! the crack is the composed ratio. An abrupt step is a **compression**, and *the reflected wave is
//! its retained remainder* — reflection is not loss, it is the retained fiber of a junction that did
//! not match.
//!
//! # ★ THE LINK IS TWO-COMPONENT — 2026-08-15
//!
//! The transport was a scalar and it was wrong twice over.
//!
//! **First it was the amplitude transmission, which does not compose.** Measured on `Y = 1 → 2 → 4`:
//! `τ(1,2)·τ(2,4) = 2/3 · 2/3 = 4/9` against a direct `τ(1,4) = 2/5`. The general defect is
//!
//! ```text
//!   τ_ij τ_jk − τ_ik  =  2 Y_i (Y_i−Y_j)(Y_j−Y_k) / [(Y_i+Y_j)(Y_j+Y_k)(Y_i+Y_k)]
//! ```
//!
//! which vanishes only where one of the two junctions is already matched.
//!
//! **Then it was the admittance ratio `ζ = Y_t/Y_i`, which composes and carries nothing back.**
//! `ζ` is an exact coboundary `Y_i⁻¹ Y_t`, so its holonomy around any closed chain is identically
//! one — not small, not measured, *identically*, because the source's own admittance cancels
//! against itself. A carrier whose only invariant cannot fail has not been instrumented.
//!
//! **What composes AND retains the return is a matrix**, and it is the standard interface transfer
//! matrix written over exact rationals:
//!
//! ```text
//!            1  [ 1+ρ   1−ρ ]                  1                    M₂₁
//!   M(ρ) =  ───  [           ]         τ  =  ─────  ,      Γ  =  ─────           ρ = Y_t / Y_i
//!            2  [ 1−ρ   1+ρ ]                 M₁₁                  M₁₁
//!
//!   M(ρ₁)·M(ρ₂) = M(ρ₁ρ₂)        det M(ρ) = ρ        Mᵀ J M = ρ J   with  J = diag(1,−1)
//! ```
//!
//! [`Crossing`] carries `M` and **derives** `τ` and `Γ` from it; [`TransferMatrix`] implements
//! `Composes`, so `Chain::compose` is matrix multiplication, exact and associative, carrying the
//! reflected amplitude *through* the composition instead of beside it.
//!
//! ## What that bought, and what it did not — stated so neither is quoted wrong
//!
//! **It bought a composition law for the return.** The scalar carrier had no composite `Γ` at all:
//! each link's reflection sat on that link and the chain could not say what the whole interface
//! reflected. The matrix returns it, and the classical laws
//!
//! ```text
//!   Γ_ik = (Γ_ij + Γ_jk) / (1 + Γ_ij Γ_jk)              τ_ik = τ_ij τ_jk / (1 + Γ_ij Γ_jk)
//! ```
//!
//! **fall out of the matrix product and are not implemented separately** — they are asserted as
//! consequences in `the_reflection_composes_by_the_addition_law_and_the_transmission_by_its_denominator`,
//! against a direct junction rather than against a restatement of themselves.
//!
//! **It bought an exact conserved form.** `Mᵀ J M = ρ J` makes each link an exact isometry between
//! admittance fibers, with `g_Y = Y·J`, so `Mᵀ g_{Y_i} M = g_{Y_t}`. It is a real condition:
//! [`TransferMatrix::conserved_form`] returns `Obstructed` on a matrix outside the family and
//! exhibits the three entries that decided it.
//!
//! **It bought `is_rebase`.** `Chain::is_rebase` read `unconnected.is_empty()`, which records only
//! what a caller handed to `Chain::reflect`, so `1 → 2 → 4` — reflecting at both links — reported a
//! clean pass. The remainder is now `M₂₁` of the *composed* transport, and that chain reports
//! `false`.
//!
//! **It did NOT buy holonomy, and this module says so rather than implying it.** With no phase
//! element between interfaces the family `{M(ρ)}` is abelian and one-parameter — `M` is determined
//! by `ρ` — so a closed chain returns `ρ = 1` and its holonomy is the identity *by construction*.
//! That receipt could not have come out otherwise and carries no evidence. Holonomy needs a link
//! that does not commute with `M(ρ)` — a propagation phase, or a lumped series/shunt element in the
//! `(voltage, current)` chart — and **this module owns none of them.** The abelian-ness is measured
//! rather than assumed in `the_interface_family_is_abelian_which_is_why_its_holonomy_is_forced`.
//!
//! # An admittance is what a site accepts, and it is derived from the material
//!
//! [`Admittance`] is not an authored bound. It is *how much of an arriving current a site can take*,
//! and the leader-star case makes it concrete: the incident admittance is what the current carries,
//! the transmitted admittance is what the site shares with it. A site sharing nothing has admittance
//! zero, which is **not a small number to compare against a threshold** — it is outside the
//! constructor's domain, so no traveling section exists there and the chain terminates by type.
//!
//! That is the whole reason this replaces a count. `DEFAULT_LEADER_APERTURE` had exactly two
//! settings: a finite count, which refuses at `count + 1` on every material measured, or
//! `usize::MAX`, which never refuses and makes `omitted = complete − selected = 0` structurally. A
//! count is not a viscosity. An admittance is.
//!
//! # The horizon law, checkable here
//!
//! `Γ` and `τ` are **invariant under a common rescaling of both admittances** and the energy terms
//! are not. So is the whole matrix, since `M` depends only on `ρ`. That is the horizon law on real
//! arithmetic: magnitudes do not cross a frame boundary, ratios do. It is tested below in both
//! directions.
//!
//! # One receipt that is not evidence, stated so it is not quoted as such
//!
//! `ExactScalarInterfaceCoefficients::energy_residual` is **identically zero for this convention**,
//! algebraically:
//!
//! ```text
//!   Y_i − Y_i Γ² − Y_t τ²  =  Y_i[(Y_i+Y_t)² − (Y_i−Y_t)² − 4 Y_i Y_t] / (Y_i+Y_t)²  =  0
//! ```
//!
//! so a run reporting it as zero has reported a definition. `T + Γ² = 1` is the same identity in the
//! power chart and is equally not evidence. `CLAUDE.md`'s tautology rule governs: a receipt that
//! could not have come out otherwise carries no evidence. The junction is lossless by construction,
//! and what a traversal actually loses is the **reflected population**, which is why that is what
//! [`holonic_structure::Chain`] retains — now on both routes, the caller's and the transport's own.

use holonic_structure::{Chain, ChainEnd, Composes, Hand, Relating};
use num_traits::{One, Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::analytic_field::{
    AnalyticFieldError, ExactScalarInterfaceCoefficients, exact_scalar_interface_coefficients,
};

#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum TraversibleChainError {
    /// A site that shares nothing with the arriving current has no admittance. This is a domain
    /// refusal, not a small value: there is no traveling section to fabricate.
    #[error("an admittance must be positive; {0} is not")]
    NonpositiveAdmittance(Rat),
    #[error("the junction refused: {0}")]
    Junction(#[from] AnalyticFieldError),
    /// A junction so mismatched that its service rounds leave the chronology carrier. Reported
    /// rather than clamped: a dilation past the carrier is a fact about the material.
    #[error("the junction's service rounds exceed the chronology carrier")]
    ServiceRoundsExceedCarrier,
}

/// What a site accepts of an arriving current. Positive by construction.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct Admittance(Rat);

impl Admittance {
    /// Admit a positive rational. Non-positive is refused by name rather than clamped.
    pub fn declared(value: Rat) -> Result<Self, TraversibleChainError> {
        if !value.is_positive() {
            return Err(TraversibleChainError::NonpositiveAdmittance(value));
        }
        Ok(Self(value))
    }

    /// The admittance a shared population gives an arriving one: `shared : arriving`, held as a
    /// ratio and never divided into a verdict.
    ///
    /// Both counts come from the material. A site sharing nothing returns the refusal rather than
    /// zero, which is what makes an unreachable site a **typed terminus** instead of a comparison.
    pub fn from_shared(shared: u64, arriving: u64) -> Result<Self, TraversibleChainError> {
        let value = Rat::new(shared.into(), arriving.max(1).into());
        Self::declared(value)
    }

    pub const fn value(&self) -> &Rat {
        &self.0
    }
}

/// The two-component transport of a junction — the exact interface transfer matrix.
///
/// ```text
///            1  [ 1+ρ   1−ρ ]        [ M₁₁  M₁₂ ]
///   M(ρ) =  ───  [           ]   =   [          ]        ρ = Y_t / Y_i
///            2  [ 1−ρ   1+ρ ]        [ M₂₁  M₂₂ ]
/// ```
///
/// The state it acts on is the pair `(forward amplitude, returned amplitude)`. `M₂₁` is **the half
/// that came back**: it is zero exactly at a matched junction, and it is what every scalar carrier
/// this module has had dropped.
///
/// Entries are held individually and [`TransferMatrix::compose`] is the **general** `2×2` product,
/// not a shortcut through `ρ`. That the product stays inside the one-parameter family — and stays
/// symmetric — is therefore a *measurement* on this carrier rather than a definition, and the
/// symmetry is load-bearing: `T = 1 − Γ²` and `1/T = Σ Γ^{2n}` hold **only** for `M₁₁ = M₂₂`,
/// `M₁₂ = M₂₁`, which is why [`TransferMatrix::is_symmetric`] exists.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransferMatrix {
    through: Rat,
    into_forward: Rat,
    returned: Rat,
    into_returned: Rat,
}

impl TransferMatrix {
    /// The junction whose transmitted admittance stands in ratio `ρ` to its incident one.
    ///
    /// `ρ` is not required positive here — that refusal belongs to [`Admittance`], and duplicating
    /// it would put one law in two places. What a positive `ρ` guarantees is that `M₁₁ = (1+ρ)/2`
    /// is strictly positive, which is what makes `τ` and `Γ` defined at every real junction.
    pub fn of_ratio(ratio: &Rat) -> Self {
        let two = Rat::from_integer(2.into());
        let sum = (Rat::one() + ratio) / &two;
        let difference = (Rat::one() - ratio) / two;
        Self {
            through: sum.clone(),
            into_forward: difference.clone(),
            returned: difference,
            into_returned: sum,
        }
    }

    /// A transport presented entry by entry, by a receiver this module did not build.
    ///
    /// This exists so the family's own properties can be **falsified**: a matrix built here need
    /// not be symmetric, need not conserve `J`, and need not be invertible, and the tests below use
    /// exactly that to show the family's laws are conditions rather than tautologies.
    pub const fn of_entries(
        through: Rat,
        into_forward: Rat,
        returned: Rat,
        into_returned: Rat,
    ) -> Self {
        Self {
            through,
            into_forward,
            returned,
            into_returned,
        }
    }

    /// `M₁₁`. `τ = 1/M₁₁`.
    pub const fn through(&self) -> &Rat {
        &self.through
    }

    /// `M₁₂` — what an arriving returned amplitude contributes to the forward one.
    pub const fn into_forward(&self) -> &Rat {
        &self.into_forward
    }

    /// `M₂₁` — **the returned component**, and the chain's remainder. `Γ = M₂₁/M₁₁`.
    pub const fn returned(&self) -> &Rat {
        &self.returned
    }

    /// `M₂₂`.
    pub const fn into_returned(&self) -> &Rat {
        &self.into_returned
    }

    /// `det M = M₁₁M₂₂ − M₁₂M₂₁`. For a junction this is exactly the admittance ratio `ρ`, which is
    /// the entire content of the scalar carrier this replaced.
    pub fn determinant(&self) -> Rat {
        &self.through * &self.into_returned - &self.into_forward * &self.returned
    }

    /// Whether `M₁₁ = M₂₂` and `M₁₂ = M₂₁`. The interface family is symmetric; a general `2×2` is
    /// not, and the power identities below need this.
    pub fn is_symmetric(&self) -> bool {
        self.through == self.into_returned && self.into_forward == self.returned
    }

    /// `τ = 1/M₁₁`. `None` when the forward diagonal vanishes, which no junction produces.
    pub fn transmission(&self) -> Option<Rat> {
        if self.through.is_zero() {
            return None;
        }
        Some(Rat::one() / &self.through)
    }

    /// `Γ = M₂₁/M₁₁`. `None` on the same degenerate diagonal.
    pub fn reflection(&self) -> Option<Rat> {
        if self.through.is_zero() {
            return None;
        }
        Some(&self.returned / &self.through)
    }

    /// `T = det M / M₁₁²` — the share of incident power that crosses.
    ///
    /// For a symmetric matrix this equals `1 − Γ²`, and that equality is the whole reason the
    /// multiple-reflection sum closes. It is asserted where symmetry is asserted, never assumed.
    pub fn power_transmission(&self) -> Option<Rat> {
        if self.through.is_zero() {
            return None;
        }
        Some(self.determinant() / (&self.through * &self.through))
    }

    /// The inverse, when the determinant does not vanish. For `M(ρ)` it is `M(1/ρ)` — the junction
    /// traversed the other way.
    pub fn inverse(&self) -> Option<Self> {
        let determinant = self.determinant();
        if determinant.is_zero() {
            return None;
        }
        Some(Self {
            through: &self.into_returned / &determinant,
            into_forward: -(&self.into_forward / &determinant),
            returned: -(&self.returned / &determinant),
            into_returned: &self.through / &determinant,
        })
    }

    /// `Mᵀ J M` against `ρ J`, with `J = diag(1, −1)`.
    ///
    /// This is the chain's conservation law: a transport satisfying it is an exact isometry between
    /// admittance fibers `g_Y = Y·J`, since `Mᵀ (Y_i J) M = Y_i ρ J = Y_t J`. It is **not** an
    /// identity of `2×2` matrices — the analogous statement for the antisymmetric form is, which is
    /// why that one would carry no information — so a returned `Obstructed` is a real refusal.
    pub fn conserved_form(&self) -> ConservedForm {
        let forward = &self.through * &self.through - &self.returned * &self.returned;
        let returned = &self.into_forward * &self.into_forward
            - &self.into_returned * &self.into_returned;
        let cross = &self.through * &self.into_forward - &self.returned * &self.into_returned;
        if cross.is_zero() && forward == -&returned {
            ConservedForm::Scaled(forward)
        } else {
            ConservedForm::Obstructed {
                cross,
                forward,
                returned,
            }
        }
    }
}

/// What `Mᵀ J M` returned. Plural and exhibited rather than a verdict.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ConservedForm {
    /// `Mᵀ J M = ρ J`. The transport is an exact isometry between admittance fibers and `ρ` is the
    /// scale it carries between them — the same `ρ` as the determinant, which is a fact about the
    /// family rather than a definition.
    Scaled(Rat),
    /// `Mᵀ J M` is not a multiple of `J`. The three entries that decided it are returned: `cross` is
    /// the off-diagonal that had to vanish, and `forward + returned` is the trace that had to.
    Obstructed {
        cross: Rat,
        forward: Rat,
        returned: Rat,
    },
}

impl ConservedForm {
    pub const fn scale(&self) -> Option<&Rat> {
        match self {
            Self::Scaled(scale) => Some(scale),
            Self::Obstructed { .. } => None,
        }
    }
}

impl Composes for TransferMatrix {
    /// The cocycle defect, carried as `direct · composed⁻¹`. Closed is exactly the identity matrix
    /// — never "close to", because these are exact rationals and there is nothing to tolerance.
    type Defect = Self;

    /// **The half that came back**, `M₂₁`. Undivided: the reflection `Γ = M₂₁/M₁₁` has the same
    /// zero set, and reporting the entry keeps the chain's remainder in the transport's own units.
    type Remainder = Rat;

    fn identity() -> Self {
        Self::of_ratio(&Rat::one())
    }

    fn compose(&self, next: &Self) -> Self {
        Self {
            through: &self.through * &next.through + &self.into_forward * &next.returned,
            into_forward: &self.through * &next.into_forward
                + &self.into_forward * &next.into_returned,
            returned: &self.returned * &next.through + &self.into_returned * &next.returned,
            into_returned: &self.returned * &next.into_forward
                + &self.into_returned * &next.into_returned,
        }
    }

    fn defect(direct: &Self, composed: &Self) -> Self {
        match composed.inverse() {
            Some(inverse) => direct.compose(&inverse),
            // A singular composed transport cannot be divided into. Return the direct transport
            // itself as the deviation rather than fabricating a quotient. No junction reaches this:
            // `det M(ρ) = ρ > 0`, so it is reachable only through `of_entries`.
            None => direct.clone(),
        }
    }

    fn closed(defect: &Self) -> bool {
        *defect == Self::identity()
    }

    fn remainder(&self) -> Rat {
        self.returned.clone()
    }

    fn is_empty(remainder: &Rat) -> bool {
        remainder.is_zero()
    }
}

/// The admittance ratio `ζ = Y_t/Y_i` — the **determinant face** of [`TransferMatrix`].
///
/// It composes, and that is exactly why it is not the transport: `det` is multiplicative, so a
/// chain of ratios closes as a cocycle, and `det` is precisely the operation that **deletes** the
/// returned component. `ζ` is an exact coboundary `Y_i⁻¹Y_t`, so the holonomy of every closed chain
/// read on this face is identically one.
///
/// It is retained as a **reading** — [`Crossing::admittance_ratio`] — and is never a
/// `Relating::Transport`. Its `Composes::Remainder` is `()` and `is_empty` is unconditionally
/// `true`, which is the lie the matrix replaced, kept visible here in the type rather than hidden in
/// a chain.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransportRatio(Rat);

impl TransportRatio {
    pub const fn of(ratio: Rat) -> Self {
        Self(ratio)
    }

    pub const fn value(&self) -> &Rat {
        &self.0
    }
}

impl Composes for TransportRatio {
    /// The cocycle defect, carried as `direct / composed`. Closed is exactly one.
    type Defect = Rat;

    /// **Nothing, and that is the point.** This face has already deleted the returned component; it
    /// cannot report a remainder it does not carry, and a chain built on it would call every
    /// traversal a rebase.
    type Remainder = ();

    fn identity() -> Self {
        Self(Rat::one())
    }

    fn compose(&self, next: &Self) -> Self {
        Self(&self.0 * &next.0)
    }

    fn defect(direct: &Self, composed: &Self) -> Rat {
        if composed.0.is_zero() {
            // A composed transport of zero cannot be divided into. Return the direct transport
            // itself as the deviation rather than fabricating a quotient.
            return direct.0.clone();
        }
        &direct.0 / &composed.0
    }

    fn closed(defect: &Rat) -> bool {
        defect.is_one()
    }

    fn remainder(&self) {}

    fn is_empty(_remainder: &()) -> bool {
        true
    }
}

/// One crossing of a junction: the two-component transport it carries, and which way it turned.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Crossing {
    coefficients: ExactScalarInterfaceCoefficients,
    transport: TransferMatrix,
    hand: Hand,
}

impl Crossing {
    /// Meet a site. The hand is read off the transport's returned entry: a site that accepts *less*
    /// than the current carries opposes it (`Anti`), one that accepts more coheres, and an exact
    /// match is the **matched junction** — no reflection at all, which is the founding orthogonal
    /// case rather than a null.
    pub fn meet(
        incident: &Admittance,
        transmitted: &Admittance,
    ) -> Result<Self, TraversibleChainError> {
        // The physical face, computed by the field owner. It is retained for cross-check and for
        // `reach`; **the composition never reads it**, and the sweep below requires it to agree
        // with the matrix entry by entry.
        let coefficients =
            exact_scalar_interface_coefficients(incident.0.clone(), transmitted.0.clone())?;
        let transport = TransferMatrix::of_ratio(&(&transmitted.0 / &incident.0));
        let hand = if transport.returned().is_zero() {
            Hand::Ortho
        } else if transport.returned().is_positive() {
            Hand::Anti
        } else {
            Hand::Cohere
        };
        Ok(Self {
            coefficients,
            transport,
            hand,
        })
    }

    /// The physical face of this one junction, from `analytic_field`. It does **not** compose — the
    /// amplitude transmission on it is the quantity whose product is not the composite's — and it is
    /// here as the independent computation the matrix is checked against.
    pub const fn coefficients(&self) -> &ExactScalarInterfaceCoefficients {
        &self.coefficients
    }

    /// ★ THE TRANSPORT — the interface transfer matrix, which composes and carries the return.
    pub const fn transport(&self) -> &TransferMatrix {
        &self.transport
    }

    /// The admittance ratio `ζ = Y_t/Y_i`, as the determinant face of the transport. A reading, not
    /// the transport: see [`TransportRatio`].
    pub fn admittance_ratio(&self) -> TransportRatio {
        TransportRatio(self.transport.determinant())
    }

    /// What crossed, as an amplitude: `τ = 1/M₁₁`, **derived from the transport**.
    ///
    /// It does not compose on its own — the product of two amplitude transmissions is not the
    /// transmission of the composite interface — but it no longer needs to, because the composite's
    /// `τ` is `1/M₁₁` of the composed matrix.
    pub fn transmission(&self) -> Rat {
        self.transport
            .transmission()
            .expect("M11 = (1+rho)/2 with rho positive by Admittance, so it never vanishes")
    }

    /// What did not cross, retained: `Γ = M₂₁/M₁₁`, **derived from the transport**. Reflection is
    /// not loss; it is the fiber of a junction that did not match, and it is exactly the population
    /// a count-valued aperture deletes.
    pub fn reflection(&self) -> Rat {
        self.transport
            .reflection()
            .expect("M11 = (1+rho)/2 with rho positive by Admittance, so it never vanishes")
    }

    /// Whether this junction matched whole — a rebase with no remainder at this link. Read off the
    /// transport's returned entry rather than declared beside it.
    pub fn is_matched(&self) -> bool {
        self.transport.returned().is_zero()
    }

    /// The share of the incident power that crosses: `det M / M₁₁²`, exact.
    ///
    /// Equal to `4 Y_i Y_t / (Y_i + Y_t)²` at a single junction, and — because the matrix composes —
    /// equal to the composite's own share on a whole chain, which the per-link scalar could not
    /// give. It is a **ratio**, so it crosses a frame boundary; the admittances it came from do not.
    pub fn power_transmission(&self) -> Rat {
        self.transport
            .power_transmission()
            .expect("M11 = (1+rho)/2 with rho positive by Admittance, so it never vanishes")
    }

    /// How many service rounds a current needs to pass this junction: `⌈1 / T⌉ = ⌈M₁₁² / det M⌉`.
    ///
    /// **The denominator is the multiple-reflection sum, and the matrix makes that derivable rather
    /// than declared.** For a symmetric transport `T = 1 − Γ²`, so
    ///
    /// ```text
    ///   1/T  =  1/(1 − Γ²)  =  Σ_{n≥0} Γ^{2n}
    /// ```
    ///
    /// — the current passing, returning, returning again, summed. `|Γ| < 1` at every real junction,
    /// so the sum is finite and its truncation carries an exact rational tail rather than a
    /// tolerance. `the_multiple_reflection_sum_is_the_service_round_denominator` exhibits the tail.
    ///
    /// **CORRECTED 2026-08-15: this claimed to be the same law as `receiver_current`'s and it is
    /// NOT.** The earlier text read *"a mismatched interface is the same statement about the same
    /// thing"* about `receiver_current:551`'s `⌈co-present population / capacity⌉`. The two
    /// disagree on real inputs:
    ///
    /// ```text
    ///     (R, M)      this, ⌈(R+M)²/4RM⌉      receiver_current, ⌈pop/cap⌉
    ///     (9, 9)              1                          1
    ///     (60, 1)            16                         60
    ///     (1, 76)            20                          1
    ///     (2, 500)           64                          1
    /// ```
    ///
    /// And the disagreement is **deliberate on this side**: `junction.rs` argues the symmetric
    /// physics — *under-filling a surface is a mismatch exactly as over-filling it is* — while a
    /// population-over-capacity ratio is one-sided by construction. Two laws, one name, and only the
    /// newer one knew about the older. `receiver_current` cites neither this module nor
    /// `CountedCrossing`.
    ///
    /// **Neither is withdrawn here.** Which one a given passage obeys is a question about that
    /// passage's material, and asserting the equivalence from one side was the error.
    ///
    /// A matched junction is exactly one round. Nothing here compares against a threshold — the
    /// count comes out of the admittances, and where it exceeds a declared chronology horizon the
    /// arrival **defers**, retained, rather than being refused.
    pub fn service_rounds(&self) -> Result<u64, TraversibleChainError> {
        let transmitted = self.power_transmission();
        let rounds = (Rat::one() / transmitted).ceil().to_integer();
        u64::try_from(rounds).map_err(|_| TraversibleChainError::ServiceRoundsExceedCarrier)
    }
}

impl Relating for Crossing {
    /// The reach WEIGHS. Here it is the admittance the current arrived carrying: a mass that bends
    /// what follows and decides nothing.
    type Weight = Rat;
    type Transport = TransferMatrix;

    fn reach(&self) -> &Rat {
        &self.coefficients.incident_admittance
    }

    fn hand(&self) -> Hand {
        self.hand
    }

    fn transport(&self) -> &TransferMatrix {
        &self.transport
    }
}

// The junction law over integer populations MOVED to `holonic_structure::CountedCrossing` on
// 2026-08-15, and re-exported here so every consumer of this module is unchanged.
//
// It moved because `soma/membrane` needs the same law for its co-present seam closure and cannot
// see this crate — `membrane` depends on `holonic-structure`, not on the engine. Two crates that
// cannot see each other both needing one law is the definition of a substrate carrier. The exact
// rational chart stays here, and the parity gate between the two charts stays here with it — and
// since 2026-08-15 that gate compares the transfer matrix entry by entry, not only its faces.
pub use holonic_structure::CountedCrossing;

/// Why a traversal stopped, or what still stands where it paused. Both are testimony; neither is an
/// absence.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum Standing {
    /// The current still carries this admittance and the traversal has not been continued.
    Carrying(Rat),
    /// No site here admits a traveling section. The chain ends because the material does, not
    /// because a count ran out.
    NoTravelingSection,
    /// The chain returned to a node it already holds. Its holonomy is the reading; going round
    /// again composes the same loop.
    LoopClosed,
    /// What reflected at an attempt that did not cross.
    Reflected(Rat),
}

/// A chain of crossings over the exact carrier.
pub type InteractionChain<N> = Chain<N, Crossing, Standing>;

/// Found a traversal at a source carrying a declared admittance.
pub fn found<N>(source: N, carrying: &Admittance, prior: Standing) -> InteractionChain<N> {
    Chain::founded(
        source,
        ChainEnd::Continues(prior),
        Standing::Carrying(carrying.0.clone()),
    )
}

#[cfg(test)]
mod tests {
    use super::*;
    use holonic_structure::{DeclaredGauge, Disposition};
    use num_bigint::BigInt;

    fn admittance(numerator: i64, denominator: i64) -> Admittance {
        Admittance::declared(Rat::new(numerator.into(), denominator.into())).expect("positive")
    }

    fn whole(value: i64) -> Admittance {
        Admittance::declared(Rat::from_integer(value.into())).expect("positive")
    }

    fn rational(numerator: i64, denominator: i64) -> Rat {
        Rat::new(numerator.into(), denominator.into())
    }

    /// A chain of real crossings over a declared admittance profile, so no test builds a chain out
    /// of authored transports.
    fn chain_over(profile: &[i64]) -> InteractionChain<i64> {
        let source = whole(profile[0]);
        let mut chain = found(profile[0], &source, Standing::NoTravelingSection);
        for pair in profile.windows(2) {
            let crossing = Crossing::meet(&whole(pair[0]), &whole(pair[1])).expect("admits");
            chain.carry(
                crossing,
                pair[1],
                Standing::Carrying(Rat::from_integer(pair[1].into())),
            );
        }
        chain
    }

    #[test]
    fn a_site_that_shares_nothing_is_refused_by_type_rather_than_compared() {
        // Zero shared features is not "a small admittance to test against a bound". It is outside
        // the domain, and the refusal names the value.
        let refusal = Admittance::from_shared(0, 12).expect_err("zero shared is refused");
        assert!(matches!(
            refusal,
            TraversibleChainError::NonpositiveAdmittance(_)
        ));
        // One shared feature admits. There is no aperture between the two.
        assert!(Admittance::from_shared(1, 12).is_ok());
    }

    #[test]
    fn a_matched_junction_transmits_whole_and_reflects_nothing() {
        let carried = admittance(3, 4);
        let site = admittance(3, 4);
        let crossing = Crossing::meet(&carried, &site).expect("matched");
        assert!(crossing.is_matched());
        assert!(crossing.reflection().is_zero());
        assert_eq!(crossing.transmission(), Rat::one());
        // The transport is the identity matrix, which is the same statement one floor down.
        assert_eq!(*crossing.transport(), TransferMatrix::identity());
        // A matched junction is the founding hand: cohere-null with nothing reflected, which is the
        // most transport there is rather than the least.
        assert_eq!(crossing.hand(), Hand::Ortho);
        assert!(crossing.hand().is_quarter_turn());
    }

    #[test]
    fn a_mismatched_junction_retains_what_did_not_cross() {
        // The current carries more than the site accepts: Y_i = 1, Y_t = 1/3.
        let crossing = Crossing::meet(&admittance(1, 1), &admittance(1, 3)).expect("admits");
        assert_eq!(crossing.reflection(), rational(1, 2));
        assert_eq!(crossing.transmission(), rational(3, 2));
        assert!(!crossing.is_matched());
        assert_eq!(crossing.hand(), Hand::Anti);
        // And the returned entry is on the transport itself, which is what a chain will compose.
        assert_eq!(*crossing.transport().returned(), rational(1, 3));
    }

    #[test]
    fn the_coefficients_are_invariant_under_a_common_rescaling_and_the_energy_is_not() {
        // THE HORIZON LAW, on real arithmetic. Both admittances scaled by four.
        let plain = Crossing::meet(&admittance(1, 1), &admittance(1, 3)).expect("admits");
        let scaled = Crossing::meet(&admittance(4, 1), &admittance(4, 3)).expect("admits");

        // The ratios cross the frame boundary: bit-identical, not merely close.
        assert_eq!(plain.reflection(), scaled.reflection());
        assert_eq!(plain.transmission(), scaled.transmission());
        // And the whole transport does, since the matrix depends only on the ratio. That is a
        // stronger reading than the two faces separately and it is what the matrix made sayable.
        assert_eq!(plain.transport(), scaled.transport());

        // The magnitude does not: the reach is the admittance, and it moved by exactly the factor.
        assert_eq!(scaled.reach(), &(plain.reach() * Rat::from_integer(4.into())));
        assert_ne!(plain.reach(), scaled.reach());
    }

    #[test]
    fn the_service_rounds_come_out_of_the_admittances_and_a_match_costs_one() {
        // A matched junction carries the whole current in one pass.
        let matched = Crossing::meet(&admittance(7, 1), &admittance(7, 1)).expect("matched");
        assert_eq!(matched.power_transmission(), Rat::one());
        assert_eq!(matched.service_rounds().expect("finite"), 1);

        // A leader carrying ten features meeting a section that shares one: T = 4·10·1/121, so the
        // junction needs four passes. Nothing was compared against a bound to get that number.
        let sparse = Crossing::meet(&admittance(10, 1), &admittance(1, 1)).expect("admits");
        assert_eq!(sparse.power_transmission(), rational(40, 121));
        assert_eq!(sparse.service_rounds().expect("finite"), 4);

        // THE VISCOSITY. The same one shared feature against a region that has grown to a hundred
        // costs twenty-six passes. As a leader's region grows, a poor match becomes expensive on
        // its own — which is the negative feedback the count-valued aperture could not supply.
        let grown = Crossing::meet(&admittance(100, 1), &admittance(1, 1)).expect("admits");
        assert_eq!(grown.service_rounds().expect("finite"), 26);
        assert!(grown.service_rounds().expect("finite") > sparse.service_rounds().expect("finite"));
    }

    #[test]
    fn the_service_rounds_are_invariant_under_a_common_rescaling() {
        // The horizon law again, on the quantity that actually gates admission: the dilation is a
        // function of the RATIO of the admittances, so rescaling both leaves it bit-identical.
        //
        // **The rescaling is declared through `DeclaredGauge`, which cannot be constructed from
        // material its transformation left alone.** Before this the test asserted two equalities
        // under a transformation and never showed the transformation acted — the exact shape the
        // grading rules convict, and the reason that carrier exists. The `expect` below is the
        // second arm, made structural rather than remembered.
        let before = vec![admittance(10, 1), admittance(1, 1)];
        let after = vec![admittance(70, 1), admittance(7, 1)];
        let gauge = DeclaredGauge::of(before, after).expect("the sevenfold rescaling acts on both");
        assert_eq!(gauge.witness(), &[0, 1], "both admittances moved");

        let plain = Crossing::meet(&gauge.before()[0], &gauge.before()[1]).expect("admits");
        let scaled = Crossing::meet(&gauge.after()[0], &gauge.after()[1]).expect("admits");
        assert_eq!(plain.power_transmission(), scaled.power_transmission());
        assert_eq!(
            plain.service_rounds().expect("finite"),
            scaled.service_rounds().expect("finite")
        );
    }

    /// The same gauge read through the carrier's own projection reader, which is what makes the
    /// pair of readings one statement instead of two: **the ratio survives and the magnitude does
    /// not, exhibited side by side over one declared orbit.**
    #[test]
    fn one_declared_rescaling_separates_what_crosses_the_horizon_from_what_does_not() {
        let gauge = DeclaredGauge::of(
            vec![admittance(1, 1), admittance(1, 3), admittance(10, 1)],
            vec![admittance(4, 1), admittance(4, 3), admittance(40, 1)],
        )
        .expect("the fourfold rescaling acts on every member");
        assert_eq!(gauge.witness(), &[0, 1, 2], "every admittance moved");

        // WHAT CROSSES: the crossing against a fixed partner scaled by the same factor. Its whole
        // transport depends only on the ratio, so the matrix is bit-identical entry by entry.
        let partner = |y: &Admittance| {
            Crossing::meet(y, &Admittance::declared(y.value() * Rat::from_integer(3.into())).expect("positive"))
                .expect("admits")
                .transport()
                .clone()
        };
        assert!(
            gauge.projection_moved(partner).is_empty(),
            "the transport is a function of the ratio alone"
        );

        // WHAT DOES NOT: the admittance itself is a magnitude and moves at every member. Required,
        // or the emptiness above is a statement about an orbit that never happened.
        assert_eq!(
            gauge.projection_moved(|y: &Admittance| y.value().clone()),
            vec![0, 1, 2],
            "the magnitudes move, so the invariance above is not vacuous"
        );
    }

    #[test]
    fn the_integer_law_and_the_exact_law_agree_on_every_swept_pair() {
        // THE PARITY GATE, run rather than ignored. The device face and the host face are the same
        // statement, so they are checked against each other across a swept material rather than
        // asserted to agree in prose. Since 2026-08-15 it also compares the TRANSFER MATRIX entry
        // by entry, so the two charts agree on the transport and not only on its faces.
        let mut swept = 0usize;
        let mut mismatched = 0usize;
        for incident in 1..=24u64 {
            for transmitted in 1..=24u64 {
                let counted = CountedCrossing::meet(incident, transmitted).expect("positive");
                let exact = Crossing::meet(
                    &Admittance::declared(Rat::from_integer(incident.into())).expect("positive"),
                    &Admittance::declared(Rat::from_integer(transmitted.into())).expect("positive"),
                )
                .expect("admits");

                // The reflection pair, undivided, equals the exact coefficient once divided.
                let (numerator, denominator) = counted.reflection_pair();
                assert_eq!(
                    Rat::new(numerator.into(), denominator.into()),
                    exact.reflection(),
                    "reflection at ({incident}, {transmitted})"
                );

                // The transmitted share likewise.
                let (share_numerator, share_denominator) = counted.power_transmission_pair();
                assert_eq!(
                    Rat::new(share_numerator.into(), share_denominator.into()),
                    exact.power_transmission(),
                    "power at ({incident}, {transmitted})"
                );

                // ★ THE MATRIX ITSELF, entry by entry, across the two charts.
                let ((diagonal, off_diagonal), matrix_denominator) = counted.transfer_pair();
                let diagonal = Rat::new(
                    BigInt::from(diagonal),
                    BigInt::from(matrix_denominator),
                );
                let off_diagonal = Rat::new(
                    BigInt::from(off_diagonal),
                    BigInt::from(matrix_denominator),
                );
                assert_eq!(*exact.transport().through(), diagonal);
                assert_eq!(*exact.transport().into_returned(), diagonal);
                assert_eq!(*exact.transport().returned(), off_diagonal);
                assert_eq!(*exact.transport().into_forward(), off_diagonal);

                // And the quantity that actually gates admission agrees as an integer.
                assert_eq!(
                    u128::from(exact.service_rounds().expect("finite")),
                    counted.service_rounds(),
                    "service rounds at ({incident}, {transmitted})"
                );
                assert_eq!(counted.is_matched(), exact.is_matched());
                if !exact.is_matched() {
                    mismatched += 1;
                }
                swept += 1;
            }
        }
        // The sweep must actually have run; a parity gate over an empty material is the check that
        // cannot fail. And the off-diagonal must be non-zero somewhere, or the matrix comparison
        // would be a comparison of identity matrices.
        assert_eq!(swept, 576);
        assert_eq!(mismatched, 552);
    }

    #[test]
    fn a_match_is_one_round_and_the_zero_population_is_a_terminus_on_the_device_face_too() {
        assert_eq!(
            CountedCrossing::meet(9, 9).expect("positive").service_rounds(),
            1
        );
        assert!(CountedCrossing::meet(9, 9).expect("positive").is_matched());
        // Nothing shared is not a small number here either. It is outside the domain.
        assert_eq!(CountedCrossing::meet(9, 0), None);
        assert_eq!(CountedCrossing::meet(0, 9), None);
    }

    /// ★ The matrix and the field owner's own junction law are two computations of one object, and
    /// the foil pins the convention: building the matrix from the **inverted** ratio negates every
    /// reflection, so the sweep would fail if `ρ` were `Y_i/Y_t`.
    #[test]
    fn the_matrix_face_and_the_physical_face_agree_and_the_inverted_convention_does_not() {
        let mut swept = 0usize;
        let mut foil_disagreed = 0usize;
        for incident in 1..=16i64 {
            for transmitted in 1..=16i64 {
                let crossing = Crossing::meet(&whole(incident), &whole(transmitted)).expect("meets");

                // Derived from the matrix against computed by `analytic_field`.
                assert_eq!(
                    crossing.reflection(),
                    crossing.coefficients().reflection,
                    "reflection at ({incident}, {transmitted})"
                );
                assert_eq!(
                    crossing.transmission(),
                    crossing.coefficients().transmission,
                    "transmission at ({incident}, {transmitted})"
                );
                // The hand is read off the transport and must agree with the physical face's sign.
                let expected = if crossing.coefficients().reflection.is_zero() {
                    Hand::Ortho
                } else if crossing.coefficients().reflection.is_positive() {
                    Hand::Anti
                } else {
                    Hand::Cohere
                };
                assert_eq!(crossing.hand(), expected);

                // THE FOIL. `ρ = Y_i/Y_t` is the other convention and it is wrong here.
                let inverted = TransferMatrix::of_ratio(&rational(incident, transmitted));
                if incident != transmitted {
                    assert_ne!(
                        inverted.reflection().expect("nonzero diagonal"),
                        crossing.reflection(),
                        "the inverted convention must not agree at ({incident}, {transmitted})"
                    );
                    foil_disagreed += 1;
                } else {
                    // At a match both conventions give the identity, so this is the one place the
                    // foil cannot fire — reported rather than hidden.
                    assert_eq!(inverted, *crossing.transport());
                }
                swept += 1;
            }
        }
        assert_eq!(swept, 256);
        assert_eq!(foil_disagreed, 240);
    }

    /// ★ THE COMPOSITION, on real crossings. The composed transport of `i → j → k` **is** the
    /// transport of the direct junction `i → k`, and the amplitude transmission provably is not.
    #[test]
    fn real_crossings_compose_through_the_matrix_and_the_composite_is_the_direct_junction() {
        let first = Crossing::meet(&whole(1), &whole(2)).expect("a junction");
        let second = Crossing::meet(&whole(2), &whole(4)).expect("a junction");
        let direct = Crossing::meet(&whole(1), &whole(4)).expect("a junction");

        let composed = first.transport().compose(second.transport());
        assert_eq!(composed, *direct.transport());
        assert_eq!(
            composed.transmission().expect("nonzero diagonal"),
            direct.transmission()
        );
        assert_eq!(
            composed.reflection().expect("nonzero diagonal"),
            direct.reflection()
        );

        // THE ARM THAT MAKES IT A TEST: the per-link amplitude transmission does not compose.
        let transmission_product = first.transmission() * second.transmission();
        assert_ne!(
            transmission_product,
            direct.transmission(),
            "the amplitude transmission must NOT compose"
        );
        assert_eq!(transmission_product, rational(4, 9));
        assert_eq!(direct.transmission(), rational(2, 5));

        // Neither junction matched, so the chain genuinely reflected at every link.
        assert!(!first.is_matched());
        assert!(!second.is_matched());

        // And it holds across a swept material, not only at this triple. The composed matrix must
        // equal the direct junction's for every ordered triple of distinct admittances.
        let mut swept = 0usize;
        for i in 1..=8i64 {
            for j in 1..=8i64 {
                for k in 1..=8i64 {
                    let through = Crossing::meet(&whole(i), &whole(j))
                        .expect("meets")
                        .transport()
                        .compose(
                            Crossing::meet(&whole(j), &whole(k))
                                .expect("meets")
                                .transport(),
                        );
                    assert_eq!(
                        through,
                        *Crossing::meet(&whole(i), &whole(k)).expect("meets").transport(),
                        "composition failed at ({i}, {j}, {k})"
                    );
                    swept += 1;
                }
            }
        }
        assert_eq!(swept, 512);
    }

    /// ★ THE TWO COMPOSITION LAWS THE PLAN NAMED — and they are **consequences of the matrix
    /// product**, not separate implementations. Nothing in this module computes them; this test
    /// asserts they hold of what the matrix already returns.
    #[test]
    fn the_reflection_composes_by_the_addition_law_and_the_transmission_by_its_denominator() {
        let mut swept = 0usize;
        let mut naive_reflection_failed = 0usize;
        let mut naive_transmission_failed = 0usize;
        for i in 1..=8i64 {
            for j in 1..=8i64 {
                for k in 1..=8i64 {
                    let left = Crossing::meet(&whole(i), &whole(j)).expect("meets");
                    let right = Crossing::meet(&whole(j), &whole(k)).expect("meets");
                    let direct = Crossing::meet(&whole(i), &whole(k)).expect("meets");

                    let (left_reflection, right_reflection) = (left.reflection(), right.reflection());
                    let denominator = Rat::one() + &left_reflection * &right_reflection;
                    assert!(!denominator.is_zero(), "|Γ| < 1 so the denominator is positive");

                    // Γ_ik = (Γ_ij + Γ_jk) / (1 + Γ_ij Γ_jk)
                    assert_eq!(
                        (&left_reflection + &right_reflection) / &denominator,
                        direct.reflection(),
                        "the reflection addition law failed at ({i}, {j}, {k})"
                    );
                    // τ_ik = τ_ij τ_jk / (1 + Γ_ij Γ_jk), zero phase between the interfaces
                    assert_eq!(
                        left.transmission() * right.transmission() / &denominator,
                        direct.transmission(),
                        "the transmission law failed at ({i}, {j}, {k})"
                    );

                    // THE ARM. Without the denominator the laws are wrong, and where they are is
                    // counted rather than asserted pointwise — the two loci are different and a
                    // pointwise assertion got that wrong on the first run.
                    if &left_reflection + &right_reflection != direct.reflection() {
                        naive_reflection_failed += 1;
                    }
                    if left.transmission() * right.transmission() != direct.transmission() {
                        naive_transmission_failed += 1;
                    }
                    swept += 1;
                }
            }
        }
        assert_eq!(swept, 512);

        // ★ THE TWO LOCI ARE NOT THE SAME, and that is the finding rather than a bookkeeping
        // detail. Solving each agreement condition exactly:
        //
        //   Γ_ij + Γ_jk = Γ_ik   ⟺   Γ_ij Γ_jk = 0  or  Γ_ij + Γ_jk = 0
        //                        ⟺   i = j          or  j = k  or  i = k
        //   τ_ij τ_jk   = τ_ik   ⟺   Γ_ij Γ_jk = 0
        //                        ⟺   i = j          or  j = k
        //
        // — because `Γ_ij + Γ_jk = 0` reduces to `2j(i − k) = 0`. So the naive sum is *also*
        // correct on the out-and-back `i = k`, where the two returns cancel and the true composite
        // reflection is zero. Over 8³ that is 176 agreements against 120.
        assert_eq!(naive_reflection_failed, 336);
        assert_eq!(naive_transmission_failed, 392);
    }

    /// ★ THE CONSERVED FORM on real material, with a foil outside the family.
    #[test]
    fn the_conserved_form_is_exhibited_on_real_material_and_a_foil_is_obstructed() {
        let mut swept = 0usize;
        for incident in 1..=12i64 {
            for transmitted in 1..=12i64 {
                let crossing = Crossing::meet(&whole(incident), &whole(transmitted)).expect("meets");
                let ratio = rational(transmitted, incident);
                // Mᵀ J M = ρ J, with ρ the admittance ratio — and the SAME ρ as the determinant,
                // which is a property of the family rather than a definition.
                assert_eq!(
                    crossing.transport().conserved_form(),
                    ConservedForm::Scaled(ratio.clone())
                );
                assert_eq!(crossing.transport().determinant(), ratio);
                assert_eq!(*crossing.admittance_ratio().value(), ratio);
                assert!(crossing.transport().is_symmetric());
                swept += 1;
            }
        }
        assert_eq!(swept, 144);

        // A composed chain is still an isometry, and its scale is the product of the links'.
        let composed = chain_over(&[1, 3, 7, 2]).compose();
        assert_eq!(
            composed.conserved_form(),
            ConservedForm::Scaled(Rat::from_integer(2.into()))
        );

        // THE FOIL. A general 2×2 does not conserve J, and the obstruction is exhibited entry by
        // entry rather than returned as a verdict.
        let foreign = TransferMatrix::of_entries(
            Rat::from_integer(1.into()),
            Rat::from_integer(2.into()),
            Rat::from_integer(3.into()),
            Rat::from_integer(4.into()),
        );
        assert_eq!(
            foreign.conserved_form(),
            ConservedForm::Obstructed {
                cross: Rat::from_integer((-10).into()),
                forward: Rat::from_integer((-8).into()),
                returned: Rat::from_integer((-12).into()),
            }
        );
        assert_eq!(foreign.conserved_form().scale(), None);
        assert!(!foreign.is_symmetric());
    }

    /// ★ `is_rebase` STOPS LYING. Three arms, and the third is the one that was not expected.
    #[test]
    fn a_chain_that_reflects_at_every_link_is_not_a_rebase_and_a_matched_chain_is() {
        // ARM ONE — the monotone taper 1 → 2 → 4. Every link reflects, the caller never called
        // `reflect`, and the OLD reading (`unconnected.is_empty()`) returned true here.
        let taper = chain_over(&[1, 2, 4]);
        assert!(taper.unconnected().is_empty());
        assert_eq!(taper.hops(), 2);
        assert!(taper.links().iter().all(|link| !link.is_matched()));
        assert!(!taper.is_rebase());
        // The remainder is exhibited, not counted: it is the composite's own returned entry,
        // M₂₁ = (1 − 4)/2 for the composite junction 1 → 4.
        assert_eq!(taper.remainder(), rational(-3, 2));
        assert_eq!(
            taper.compose().reflection().expect("nonzero diagonal"),
            rational(-3, 5)
        );

        // ARM TWO — a genuinely matched chain, which must still read as a rebase.
        let matched = chain_over(&[2, 2, 2, 2]);
        assert!(matched.links().iter().all(Crossing::is_matched));
        assert!(matched.is_rebase());
        assert_eq!(matched.compose(), TransferMatrix::identity());
        assert!(matched.remainder().is_zero());
        assert_eq!(matched.disposition(), Disposition::Reached);

        // ARM THREE, and it did NOT fall out as the plan implied. A chain that reflects at every
        // link and returns to its own admittance — 1 → 3 → 1 — composes to a rebase, because with
        // ZERO PHASE between the two interfaces the returns cancel exactly and the composite really
        // is matched. A zero-thickness layer is invisible; this is physics, not a residual defect,
        // and the rule is that the COMPOSITE's return decides, never "some link reflected".
        let out_and_back = chain_over(&[1, 3, 1]);
        assert!(out_and_back.links().iter().all(|link| !link.is_matched()));
        assert_eq!(out_and_back.compose(), TransferMatrix::identity());
        assert!(out_and_back.is_rebase());

        // And the caller's route still stands beside the transport's: an attempt that never crossed
        // refuses the rebase claim even on a chain whose composition is clean.
        let mut with_attempt = chain_over(&[2, 2]);
        assert!(with_attempt.is_rebase());
        with_attempt.reflect(9, Standing::Reflected(rational(4, 5)));
        assert!(!with_attempt.is_rebase());
    }

    /// ★ `1/T = Σ Γ^{2n}` — derivable from the matrix rather than declared, and the derivation
    /// **needs the symmetry**, which the foil shows.
    #[test]
    fn the_multiple_reflection_sum_is_the_service_round_denominator() {
        for (incident, transmitted) in [(10i64, 1i64), (1, 76), (3, 7), (100, 1)] {
            let crossing = Crossing::meet(&whole(incident), &whole(transmitted)).expect("meets");
            let reflection = crossing.reflection();
            let transmission = crossing.power_transmission();
            // T = 1 − Γ², which holds because the transport is symmetric.
            assert!(crossing.transport().is_symmetric());
            assert_eq!(
                Rat::one() - &reflection * &reflection,
                transmission,
                "T = 1 − Γ² failed at ({incident}, {transmitted})"
            );

            // The sum, truncated with its EXACT rational tail retained. Nothing is toleranced.
            let target = Rat::one() / &transmission;
            let mut partial = Rat::zero();
            let mut power = Rat::one();
            let mut previous = Rat::zero();
            for term in 0..6u32 {
                partial += &power;
                power = &power * &reflection * &reflection;
                let tail = &power / &transmission;
                assert_eq!(
                    &partial + &tail,
                    target,
                    "term {term} of the reflection sum at ({incident}, {transmitted})"
                );
                // The partial sum climbs toward the target and never reaches it: every retained
                // term is a further round trip, and the tail is what is still bouncing.
                assert!(partial > previous);
                assert!(partial < target);
                previous = partial.clone();
            }

            // And that target is exactly what `service_rounds` takes the ceiling of.
            assert_eq!(
                u64::try_from(target.ceil().to_integer()).expect("fits"),
                crossing.service_rounds().expect("finite")
            );
        }

        // THE FOIL. Drop the symmetry and the identity fails: for M = [[2,1],[1,3]],
        // det/M₁₁² = 5/4 while 1 − Γ² = 3/4.
        let asymmetric = TransferMatrix::of_entries(
            Rat::from_integer(2.into()),
            Rat::from_integer(1.into()),
            Rat::from_integer(1.into()),
            Rat::from_integer(3.into()),
        );
        assert!(!asymmetric.is_symmetric());
        let reflection = asymmetric.reflection().expect("nonzero diagonal");
        assert_eq!(
            asymmetric.power_transmission().expect("nonzero diagonal"),
            rational(5, 4)
        );
        assert_eq!(Rat::one() - &reflection * &reflection, rational(3, 4));
        assert_ne!(
            asymmetric.power_transmission().expect("nonzero diagonal"),
            Rat::one() - &reflection * &reflection
        );
    }

    /// ★ THE HONEST BOUNDARY. The interface family is abelian and one-parameter, so a closed chain's
    /// holonomy is the identity **by construction**. This test measures the abelian-ness — which is
    /// a real property of the general `2×2` product restricted to this family — and then states that
    /// the holonomy receipt carries no evidence, rather than reporting it as one.
    #[test]
    fn the_interface_family_is_abelian_which_is_why_its_holonomy_is_forced() {
        let mut swept = 0usize;
        for i in 1..=6i64 {
            for j in 1..=6i64 {
                for k in 1..=6i64 {
                    let left = Crossing::meet(&whole(i), &whole(j)).expect("meets");
                    let right = Crossing::meet(&whole(j), &whole(k)).expect("meets");
                    // The general 2×2 product, both orders. Inside the family they agree.
                    assert_eq!(
                        left.transport().compose(right.transport()),
                        right.transport().compose(left.transport()),
                        "the family must commute at ({i}, {j}, {k})"
                    );
                    swept += 1;
                }
            }
        }
        assert_eq!(swept, 216);

        // THE ARM. The carrier itself does not commute — so the commutativity above is a fact about
        // the interface family and not about the multiplication.
        let one = TransferMatrix::of_entries(
            Rat::from_integer(1.into()),
            Rat::from_integer(1.into()),
            Rat::zero(),
            Rat::from_integer(1.into()),
        );
        let other = TransferMatrix::of_entries(
            Rat::from_integer(1.into()),
            Rat::zero(),
            Rat::from_integer(1.into()),
            Rat::from_integer(1.into()),
        );
        assert_ne!(one.compose(&other), other.compose(&one));

        // A closed chain of real junctions: its composition is the identity and its holonomy is the
        // identity. THAT RECEIPT COULD NOT HAVE COME OUT OTHERWISE — the composed ratio is
        // Y_source/Y_source — so it is recorded as a definition, not as a measured flatness. A
        // non-trivial holonomy needs a link outside the family, like the two above; this module
        // owns none.
        let mut loop_chain = chain_over(&[1, 3, 7]);
        let closing = Crossing::meet(&whole(7), &whole(1)).expect("meets");
        loop_chain.carry(closing, 1, Standing::LoopClosed);
        assert_eq!(loop_chain.compose(), TransferMatrix::identity());
        assert_eq!(
            loop_chain.holonomy(),
            Some(TransferMatrix::identity()),
            "forced, not measured"
        );
        assert!(TransferMatrix::closed(
            &loop_chain.holonomy().expect("closed chain")
        ));
    }

    /// The determinant face is the old scalar carrier, and it composes for exactly the reason it
    /// carries nothing: `det` is multiplicative, and it is the operation that deletes `M₂₁`.
    #[test]
    fn the_admittance_ratio_is_the_determinant_and_the_determinant_deletes_the_return() {
        let first = Crossing::meet(&whole(1), &whole(2)).expect("meets");
        let second = Crossing::meet(&whole(2), &whole(4)).expect("meets");
        let direct = Crossing::meet(&whole(1), &whole(4)).expect("meets");

        // The cocycle on the determinant face, from REAL crossings rather than authored ratios.
        let composed = first.admittance_ratio().compose(&second.admittance_ratio());
        assert_eq!(composed.value(), direct.admittance_ratio().value());
        assert!(TransportRatio::closed(&TransportRatio::defect(
            &direct.admittance_ratio(),
            &composed
        )));
        // det of the composed matrix is the composed det — multiplicativity, on real material.
        assert_eq!(
            first.transport().compose(second.transport()).determinant(),
            first.transport().determinant() * second.transport().determinant()
        );

        // And the deletion, in the type: this face reports an empty remainder for a chain that
        // demonstrably reflected. It is retained as a reading and is never a `Relating::Transport`,
        // which is what stops it reaching `Chain::is_rebase`.
        assert!(TransportRatio::is_empty(&composed.remainder()));
        assert!(!direct.is_matched());
        assert_eq!(direct.reflection(), rational(-3, 5));
    }

    #[test]
    fn composition_is_associative_which_is_what_licenses_the_scan() {
        // A chain composes as a prefix product, so it may be cut anywhere and its halves composed
        // on separate channels. That is the cocycle law read as a parallelization licence — and it
        // is checked on REAL crossings, because associativity of authored values is a fact about
        // multiplication rather than about junctions.
        let first = Crossing::meet(&whole(3), &whole(2)).expect("meets");
        let second = Crossing::meet(&whole(2), &whole(5)).expect("meets");
        let third = Crossing::meet(&whole(5), &whole(7)).expect("meets");

        let left_first = first
            .transport()
            .compose(second.transport())
            .compose(third.transport());
        let right_first = first
            .transport()
            .compose(&second.transport().compose(third.transport()));
        assert_eq!(left_first, right_first);

        // Split three ways and rejoin: the same transport, which is what a scan across lanes
        // returns. And it is the direct junction 3 → 7, so the scan is answering the real question.
        let joined = TransferMatrix::identity()
            .compose(first.transport())
            .compose(
                &TransferMatrix::identity()
                    .compose(second.transport())
                    .compose(third.transport()),
            );
        assert_eq!(joined, left_first);
        assert_eq!(
            joined,
            *Crossing::meet(&whole(3), &whole(7)).expect("meets").transport()
        );
        // The chain carrier agrees with the hand-composed product.
        assert_eq!(chain_over(&[3, 2, 5, 7]).compose(), joined);
    }

    #[test]
    fn the_transport_composes_as_a_cocycle_and_its_failure_is_returned_rather_than_tested() {
        let through = chain_over(&[2, 3, 5]);
        // The direct junction is the declared transport, and the chain agrees with it exactly, so
        // the defect is the identity.
        let direct = Crossing::meet(&whole(2), &whole(5)).expect("meets");
        assert!(TransferMatrix::closed(
            &through.defect_against(direct.transport())
        ));

        // Where a declared transport disagrees the deviation is returned as a transport, not as a
        // verdict — and it is itself an interface matrix, whose ratio is what separates the two.
        let disagreeing = Crossing::meet(&whole(2), &whole(10)).expect("meets");
        let defect = through.defect_against(disagreeing.transport());
        assert!(!TransferMatrix::closed(&defect));
        assert_eq!(defect, TransferMatrix::of_ratio(&Rat::from_integer(2.into())));
        assert_eq!(defect.determinant(), Rat::from_integer(2.into()));
    }

    #[test]
    fn a_chain_of_matched_junctions_is_a_rebase_and_composes_to_the_identity() {
        let carried = admittance(2, 1);
        let mut chain = found("source", &carried, Standing::NoTravelingSection);
        for at in ["first", "second", "third"] {
            let crossing = Crossing::meet(&carried, &carried).expect("matched");
            chain.carry(crossing, at, Standing::Carrying(carried.value().clone()));
        }
        assert_eq!(chain.disposition(), Disposition::Reached);
        assert!(chain.is_rebase());
        // Three matched links, each transmitting whole: the adiabatic taper, composed.
        assert_eq!(chain.compose(), TransferMatrix::identity());
        assert_eq!(chain.compose().determinant(), Rat::one());
    }

    #[test]
    fn a_chain_that_reflects_is_a_condensation_and_the_remainder_is_exhibited() {
        let carried = admittance(1, 1);
        let mut chain = found("source", &carried, Standing::NoTravelingSection);
        let crossed = Crossing::meet(&carried, &admittance(1, 1)).expect("matched");
        chain.carry(crossed, "crossed", Standing::Carrying(carried.value().clone()));

        let turned_away = Crossing::meet(&carried, &admittance(1, 9)).expect("admits");
        chain.reflect(
            "did not cross",
            Standing::Reflected(turned_away.reflection()),
        );
        chain.terminate(Standing::NoTravelingSection);

        // Not a rebase, because something reflected — and what reflected is on the chain by name
        // with its exact value, which is the difference between a certified remainder and a lost
        // one.
        assert!(!chain.is_rebase());
        assert_eq!(chain.unconnected().len(), 1);
        assert_eq!(
            chain.unconnected()[0].reflected,
            Standing::Reflected(rational(4, 5))
        );
        // The composed transport is clean — the crossed link matched — so the two routes to a
        // remainder are genuinely independent and this chain exercises only the caller's.
        assert!(chain.remainder().is_zero());
    }

    #[test]
    fn a_traversal_that_never_crossed_says_which_way_it_failed() {
        let carried = admittance(1, 1);
        // Nothing crossed and the traversal was not continued: the potential still stands.
        let open = found("source", &carried, Standing::NoTravelingSection);
        assert_eq!(open.disposition(), Disposition::Untouched);

        // Nothing crossed and the material admitted nothing: it landed and caused nothing.
        let mut closed = found("source", &carried, Standing::NoTravelingSection);
        closed.terminate(Standing::NoTravelingSection);
        assert_eq!(closed.disposition(), Disposition::Saturated);
    }
}
