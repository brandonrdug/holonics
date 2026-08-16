//! The link, which is a relating and not a pointer.
//!
//! The substrate already owns this law. `soma/body/src/arrow.rs` reads a relating from a pole as
//! `Arrow { reach, aim, cross }` — *"the reach WEIGHS (the elevation), never gates"*, the aim
//! GATES, and the hand is one of three turns rather than a bool. That law never reached the
//! traversal carriers: `BranchLineage`'s link is `Option<Arc<BranchNode<T>>>` with `extent: usize`,
//! and [`crate::RelationSpan`] is `{ start, len }` — a raw address and a count, with the relation
//! deleted.
//!
//! **The traversal structures addressed by index while the substrate one floor down addressed by
//! turn.** This module is where they meet. It is a trait rather than a dependency edge onto `body`
//! so the device-side law is untouched and no numeric carrier is forced upward.
//!
//! # What a link must carry
//!
//! ```text
//!   reach       WEIGHS. The cost/mass. It bends what later crosses it; it never decides admission.
//!   hand        GATES. Three turns, never a bool and never a magnitude compare.
//!   transport   COMPOSES. The ratio carried across the junction.
//! ```
//!
//! The separation is the whole point and it is `arrow.rs`'s: a carrier that lets a weight gate has
//! promoted a magnitude into a decision, which is the defect the horizon law names.

use serde::{Deserialize, Serialize};

/// Which way the relating turns, read in the pole's frame.
///
/// Mirrors `body::Aim` and carries its ruling: there is no "nothing" here, only which way the turn
/// bites. `Ortho` is **cohere-null with the cross maximal** — the pure orthogonal turn, the founding
/// hand — and is never to be read as an absent relation.
#[derive(
    Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize,
)]
pub enum Hand {
    /// The aims align — the in-plane hand.
    Cohere,
    /// The aims oppose — the other in-plane hand.
    Anti,
    /// Cohere-null, cross maximal. The founding hand, mis-read as nothing because the cohere face
    /// is null.
    Ortho,
}

impl Hand {
    /// The hand reversed. `Ortho` is its own reverse: the founding turn has no opposed in-plane
    /// face to swap to.
    pub const fn reversed(self) -> Self {
        match self {
            Self::Cohere => Self::Anti,
            Self::Anti => Self::Cohere,
            Self::Ortho => Self::Ortho,
        }
    }

    /// Whether this hand is the exactly-orthogonal one — the quarter turn, `aim = 0`.
    ///
    /// **THIS IS NOT THE FOUNDING PREDICATE AND WAS MISNAMED `founds` UNTIL 2026-08-15.** A hand is
    /// a species and carries no magnitudes, so it cannot decide founding: `body::Arrow::founds` is
    /// the *cone* `cross² ≥ aim²`, an arc-annulus about the Thales circle, while this is the knife
    /// edge at its centre. On one measured run the cone admits 2,672 contacts and the edge admits
    /// only those with `aim` exactly zero.
    ///
    /// The collision was written in the same session that derived *the founding is not a knife edge
    /// but a lens*, which is why the name is now the mechanism: **ask a hand what species it is, and
    /// ask an arrow whether it founds.**
    pub const fn is_quarter_turn(self) -> bool {
        matches!(self, Self::Ortho)
    }
}

/// One link of a chain: a relating read from a pole.
pub trait Relating {
    /// What the link weighs. A mass, a cost, a reach — it bends, and it may not gate.
    type Weight;
    /// What the link carries across the junction. Composes along the chain.
    type Transport;

    fn reach(&self) -> &Self::Weight;
    fn hand(&self) -> Hand;
    fn transport(&self) -> &Self::Transport;
}

/// A transport that composes along a chain, and whose failure to close is retained.
///
/// The law is the cocycle, measured on this body's own material 2026-08-14:
///
/// ```text
///   r(i,j) · r(j,k) = r(i,k)
/// ```
///
/// which says a chain of ratios composes path-independently and that the absolute values were
/// gauge. It is the same law as the whip's `Γ = (Z₂ − Z₁)/(Z₂ + Z₁)` chained along a taper: the
/// adiabatic case is the exact cocycle, an abrupt step is where it breaks, and **the break is
/// holonomy**.
///
/// `defect` is required to *return* the deviation rather than a verdict about it. A carrier that
/// answers "did it close" with a bool has collapsed the residual into a face, which is the
/// substitution this framework refuses everywhere else.
///
/// # The transport must also say what came back — added 2026-08-15
///
/// [`Composes::compose`] alone describes only the half that continued. A carrier that composes
/// perfectly and cannot say what it turned back has **quotiented without keeping its fiber**, and
/// the observable consequence was measured: [`crate::Chain::is_rebase`] read
/// `unconnected.is_empty()`, which records only what a *caller* chose to hand to
/// [`crate::Chain::reflect`], so a chain that reflected at every one of its own links reported a
/// clean pass.
///
/// [`Composes::remainder`] closes that. It is the transport's **own** returned component, derived
/// from the composed transport rather than reported alongside it, so a chain cannot claim a
/// zero remainder that its composition contradicts.
pub trait Composes: Sized {
    /// The deviation between two transports that should have agreed.
    type Defect;

    /// What a transport turned back rather than carried. This is a **retained fiber**, not a
    /// magnitude: an implementation returns the returned component itself, and
    /// [`Composes::is_empty`] is the only place it is collapsed to a verdict.
    type Remainder;

    /// The transport that changes nothing — a rebase with no remainder.
    fn identity() -> Self;

    /// Carry this transport, then the next.
    fn compose(&self, next: &Self) -> Self;

    /// What separates a directly declared transport from one composed through intermediates.
    /// Zero defect is the exact cocycle; anything else is holonomy and is the chain's remainder.
    fn defect(direct: &Self, composed: &Self) -> Self::Defect;

    /// Whether a defect is the zero one. Reported beside the defect, never in place of it.
    fn closed(defect: &Self::Defect) -> bool;

    /// What this transport turned back. Derived from the transport itself, so it survives
    /// composition instead of living beside it.
    fn remainder(&self) -> Self::Remainder;

    /// Whether a remainder is the empty one — the **rebase** species. Reported beside the
    /// remainder, never in place of it.
    fn is_empty(remainder: &Self::Remainder) -> bool;
}
