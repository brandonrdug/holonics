//! **Release: one decision law with arms** (THE_REBUILD U3; #73, #148).
//!
//! [definition] **The contract.** Every emission of the machine is a [`ReleaseReturn`] of one
//! decision law, and this module is its one owner. A release decides what a receiver emits from a
//! reading over a compatible fibre; the arms are what it may return:
//!
//! | Arm | The act | What checks it |
//! |---|---|---|
//! | **threshold commit**: `Released`, with `Widen` its named proposal | a width over a compatible fibre, decided at a declared tolerance by the caller's declared law ([`DecisionLaw`]; its data form [`DecisionRule`]) | [`release`]: `Released` inside the law's own tolerance (`ReleaseLaw.sound`), `Widen` wide enough for the width (`ReleaseLaw.widenSound`) |
//! | **certified draw**: `Drawn` | a declared key `u ∈ [0, 1)` read by the inverse CDF of an exact interval face ([`draw`], [`draw_exact`]) | the certificate `Σ_(j<i) upper_j ≤ u < Σ_(j≤i) lower_j` (`certified_inverseCDF_class`), decided through [`release`] at tolerance zero |
//! | **probe**: `Ask` | the named observation the owner computed and offered ([`ObservationProbe`]), carrying the partition of the fibre it is chosen by ([`ProbePartition`]) | [`release`]: only an offered probe; [`ProbePartition::new`]: one fibre's partitions, the probe's strictly more informative than its comparison's |
//! | **typed refusal**: `Hold`, `Unresolved`, `NoContinuationBridges` | nothing is emitted: the plural fibre is kept (`Hold`); a key the enclosure leaves plural keeps its unresolved draw mass with its exact crossing bounds (`Unresolved`); no admitted continuation reaches the receiver's section (`NoContinuationBridges`, the stop law's refusal when no stop fits the aperture) | unconstrained, as in Lean: which one is the caller's declared law |
//!
//! Malformed operands (an empty or unnormalizable face, a key outside `[0, 1)`, a forged width) are
//! not decisions: they are returned as [`DrawRefusal`] or [`WidthRefusal`] content, never as an arm.
//!
//! [proved-derived; formal-checked] **The join: a certified draw is a release at tolerance zero.**
//! A declared draw is a different act from deciding at a tolerance. Its key is an exterior declared
//! input (the release's key, a navigator's initial configuration read at the receiver), and what it
//! emits is one class of the face, not the face. Its decision is nevertheless the same law. The
//! reading is the key's class, `R_u(q) = inverseCDF_q(u)`, over the compatible fibre of the interval
//! face (every normalized exact face inside the bounds). A class has no grain coarser than itself, so
//! the tolerance is zero (the discrete metric on the alphabet), and releasing at zero is constancy
//! on the fibre (`width_eq_zero_iff`). The certificate is the enclosure route to width zero
//! (`width_le_of_bounds`). Lean `Compression/Landmark/Context/Population.certified_draw_is_released_at_zero_tolerance`
//! proves that the holding law at tolerance zero releases the class reading over every finite family
//! of compatible faces, and `plural_draw_is_held` that it holds once two compatible faces part.
//! [`draw`] runs exactly that: it declares the class reading's width (zero when certified; otherwise
//! one, the discrete diameter's band), assembles [`LawfulOptions`] at tolerance zero, and takes the
//! holding rule's decision through [`release`]. `Released` returns as `Drawn` with the key and its
//! certified cell `[prior_upper, through_lower)`; `Hold` returns as `Unresolved` with the crossing
//! bounds. **The separating term between the two acts is the key**: a width decision has no key, so
//! [`release`] refuses a declared law that returns `Drawn` or `Unresolved`
//! ([`WidthRefusal::DrawNotOffered`]).
//!
//! [proved-derived; formal-checked] **The probe's criterion is information, compared exactly.** A
//! probe is worth the information its outcome carries about the fibre, `I(Θ; Y | h, do(a))`, zero
//! for a probe whose outcome is the same under every member. With the fibre read uniform, an
//! observation partitions it into the classes `c` of members sharing an outcome, and its
//! information is `I = log₂|Θ| − (1/|Θ|) Σ_c |c| log₂|c|`. Over one fibre, `I > I′` exactly when
//! `∏_c |c|^|c| < ∏_c′ |c′|^|c′|`, a comparison of integers in which no logarithm is formed (Lean
//! `Compression/Landmark/Context/Population.partitionInformation_lt_iff`). [`ProbePartition`] carries
//! the probe's class sizes and those of the move it is compared against, and it exists only where
//! both partition one nonempty fibre into nonempty classes and the probe's product is strictly below
//! its comparison's: an offered probe always separates the fibre more than the move it would
//! replace. The criterion is information, not a residual width.
//!
//! [established-bounded] **What the draw does not claim.** The certificate is sufficient, not
//! necessary: normalization can make every compatible face agree where the prefix bounds still
//! straddle the key, and that key is `Unresolved`. The inverse-CDF theorem certifies each emitted
//! class. It does not turn the certified submeasure into the full mixture: over a point face the
//! certified cells partition `[0, 1)` and the drawn class follows the face, while over an interval
//! face the unresolved keys are mass the release does not emit. No claim of distributional
//! equality rests on the draw. `P_release = P_scored` is the face identity of the population's
//! release view (`receiver::population::PopulationRelease`), which the draw reads.
//!
//! [definition] **The consumers.** The HNN's release (`hnn::reference`, the CUDA port) is a
//! threshold commit at its receiving phases' grain. The population's release pipeline
//! (`receiver::population::{releasing, text_release}`) returns this law's arms: the family draw
//! (`Population::select_family`), one certified draw per response cell, the stop law and the
//! typed refusals (`receiver::population::Population::release_response`). The chaser
//! (`receiver::population::chaser`, THE_REBUILD U3's second loop) returns two of its arms: the
//! certified capture is `Released` at tolerance zero on the capture-within-`m` reading over the
//! population's selected fibre (width zero is the capture basin's certificate over every member),
//! and the probe is `Ask` with its [`ProbePartition`]. Its cornering commit is a separate arm,
//! declared as such in its owner: the comparison of the probe's concession with the price `d·|Θ|` of
//! a tick is the Bellman stop law's one-step reading, and **the price is the separating term**, which
//! no width or tolerance of this law carries.
//!
//! | Lean | Rust |
//! |---|---|
//! | `width`, `width_nonneg`, `abs_sub_le_width`, `width_mono`, `width_eq_zero_iff` | [`crate::receiver::face::width_over_readings`], [`crate::receiver::face::ReceiverWidth`] (`the_width_is_monotone_under_fibre_inclusion`, `width_zero_is_constancy_on_the_fibre`) |
//! | `width_le_of_bounds` | [`crate::receiver::face::ReceiverWidth::declared`], a width an owner bounded (the HNN's receiving fibres; [`draw`]'s certificate) |
//! | `releasable_at_every_tolerance_iff_width_zero`, `Releasable` | [`crate::receiver::face::ReceiverWidth::releasable_at`] (`width_zero_releases_at_every_tolerance`) |
//! | `NonExpansive`, `width_nonExpansive_factor`, `expansive_factor_increases_width` | `a_non_expansive_coarser_reading_has_no_larger_width`, `an_expansive_factor_widens_the_reading` |
//! | `ReleaseReturn` | [`ReleaseReturn`] (its `releaseCoarser` has no Rust realization: no owner builds a coarser receiver) |
//! | `ReleaseLaw`, `ReleaseLaw.sound`, `ReleaseLaw.widenSound` | [`DecisionLaw`] and [`release`]; its data form [`DecisionRule`] |
//! | `holdingLaw` | the rule [`draw`] decides with, `DecisionRule(Release, Hold)` at tolerance zero |
//! | `no_default_among_the_lawful_returns` | `two_lawful_laws_return_different_arms` |
//! | `future_stable_event_with_unstable_timing`, `timingInsufficiency` | `an_event_is_future_stable_while_its_timing_is_not`, `the_coarse_event_reading_does_not_determine_the_timing` |
//! | `Horizon`, `Horizon.Within`, `horizonWithin_is_not_total` | [`crate::receiver::face::Horizon`] (`the_horizon_has_two_coordinates_that_are_not_one_scale`) |
//! | `Population.certified_inverseCDF_class` | [`draw`]'s certificate, [`CertifiedDraw`] |
//! | `Population.{certified_draw_is_released_at_zero_tolerance, plural_draw_is_held}` | [`draw`]: `Drawn` through `Released`, `Unresolved` through `Hold` |
//! | `Population.{partitionInformation, partitionInformation_lt_iff}` | [`ProbePartition`] and [`partition_product`] (the probe's criterion, `the_probe_partition_compares_information_by_its_product`) |
//!
//! [definition] **Retired September 28** (U3; history at `1bdacc8f`). The exact zonotope enclosure
//! and its `h`-step image under a linearization, the enumerated and enclosed compatible families,
//! the two probe searches, the coarsening tower search and the factored readings had no consumer:
//! the contract's fibres are receiving faces, interval face enclosures and enumerated candidates,
//! never an affine image of a box. Their laws are kept in Lean (`width`, `width_le_of_bounds`,
//! `width_mono`, `coarser_receiver_factors`, `NonExpansive`, `width_nonExpansive_factor`,
//! `expansive_factor_increases_width`) and in
//! [RECEIVER_HOLARCHY](../../../../docs/RECEIVER_HOLARCHY.md#width-and-release) (the zonotope's
//! image and its sup-norm diameter, the probe searches and the tower search).
//!
//! [implemented-exact] **No floats.** Every width, tolerance, key, bound and mass is an exact `Rat`.

use num_bigint::BigUint;
use num_traits::{One, Zero};
use thiserror::Error;

use crate::ratio::Rat;
use crate::ratio::algebraic::ExactInterval;
use crate::receiver::face::{
    DiameterNorm, ReceiverWidth, ReleasedClaim, WidenClaim, WidthRefusal, WidthWitness,
};

// -------------------------------------------------------------------------------------------
// the probe
// -------------------------------------------------------------------------------------------

/// **The probe an owner offers**: the named observation whose outcome would separate the fibre, and
/// the partition it is chosen by. The owner that computed it offers it through
/// [`LawfulOptions::assemble`]; a law may ask only for the probe offered.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ObservationProbe {
    /// The observation's declared name.
    pub observation: String,
    /// The fibre's partition by its outcomes, against the compared move's (module header).
    pub partition: ProbePartition,
}

/// [proved-derived; formal-checked] **The partition a probe is chosen by** (module header): the
/// class sizes of the fibre's partition by the probe's outcomes, and those of the partition it is
/// compared against. It is constructed only by [`Self::new`], so every value partitions one nonempty
/// fibre into nonempty classes and separates it strictly more than its comparison (Lean
/// `Population.partitionInformation_lt_iff`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ProbePartition {
    classes: Vec<usize>,
    against: Vec<usize>,
}

impl ProbePartition {
    /// The probe's classes against the compared ones; refused unless both partition one nonempty
    /// fibre into nonempty classes ([`WidthRefusal::ProbeClasses`]) and
    /// `∏_c |c|^|c| < ∏_c′ |c′|^|c′|` ([`WidthRefusal::ProbeNotInformative`]).
    pub fn new(classes: Vec<usize>, against: Vec<usize>) -> Result<Self, WidthRefusal> {
        let members = |sizes: &[usize]| -> Option<usize> {
            if sizes.is_empty() || sizes.contains(&0) {
                return None;
            }
            sizes.iter().try_fold(0usize, |total, &size| total.checked_add(size))
        };
        match (members(&classes), members(&against)) {
            (Some(left), Some(right)) if left == right => {}
            (left, right) => {
                return Err(WidthRefusal::ProbeClasses {
                    classes: left.unwrap_or(0),
                    against: right.unwrap_or(0),
                });
            }
        }
        let (product, compared) = (partition_product(&classes), partition_product(&against));
        if product >= compared {
            return Err(WidthRefusal::ProbeNotInformative {
                product: product.to_string(),
                against: compared.to_string(),
            });
        }
        Ok(Self { classes, against })
    }

    /// The probe's class sizes.
    pub fn classes(&self) -> &[usize] {
        &self.classes
    }

    /// The compared partition's class sizes.
    pub fn against(&self) -> &[usize] {
        &self.against
    }

    /// The fibre's size `|Θ|`, the members both partitions hold.
    pub fn fibre(&self) -> usize {
        self.classes.iter().sum()
    }

    /// `∏_c |c|^|c|` over the probe's classes.
    pub fn product(&self) -> BigUint {
        partition_product(&self.classes)
    }

    /// `∏_c′ |c′|^|c′|` over the compared classes, strictly above [`Self::product`].
    pub fn against_product(&self) -> BigUint {
        partition_product(&self.against)
    }
}

/// **`∏_c |c|^|c|` over a partition's class sizes** (module header): over one fibre, the smaller
/// product is the partition carrying the more information.
pub fn partition_product(sizes: &[usize]) -> BigUint {
    sizes.iter().fold(BigUint::from(1u32), |product, &size| {
        product * BigUint::from(size).pow(size as u32)
    })
}

// -------------------------------------------------------------------------------------------
// the certified draw
// -------------------------------------------------------------------------------------------

/// Exact bounds at a class the key may cross: the enclosure places the class's inverse-CDF cell on
/// both sides of the key.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CrossingBounds {
    /// Zero-based class whose cell may contain the key.
    pub class: usize,
    /// Upper bound on the cumulative mass strictly before `class`.
    pub prior_upper: Rat,
    /// Lower bound on the cumulative mass through `class`.
    pub through_lower: Rat,
}

/// **A certified draw**: every compatible face lands the declared key in `class`, and every key in
/// the certified cell `[prior_upper, through_lower)` does too.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CertifiedDraw {
    /// The declared key.
    pub key: Rat,
    /// The drawn class.
    pub class: usize,
    /// Upper bound on the cumulative mass strictly before `class`: the cell's left end.
    pub prior_upper: Rat,
    /// Lower bound on the cumulative mass through `class`: the cell's right end.
    pub through_lower: Rat,
}

/// **A key the enclosure leaves plural**: the classes whose cells cross it, with their exact
/// bounds. Nothing is emitted; the draw mass stays unresolved.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UnresolvedDraw {
    /// The declared key.
    pub key: Rat,
    /// Every class the key may land in.
    pub crossings: Vec<CrossingBounds>,
}

/// Malformed draw operands, returned as content. None of these is a decision.
#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum DrawRefusal {
    /// A face with no class.
    #[error("a face must contain at least one class")]
    EmptyFace,
    /// A class whose lower bound (or exact mass) is negative.
    #[error("class {class} has negative mass bound {bound}")]
    NegativeMass { class: usize, bound: Rat },
    /// A class whose upper bound exceeds one.
    #[error("class {class} has mass bound {bound} above one")]
    MassAboveOne { class: usize, bound: Rat },
    /// Interval bounds that enclose no normalized face.
    #[error("the lower bounds total {lower_total} and the upper bounds {upper_total}; no normalized face lies between")]
    InvalidNormalization { lower_total: Rat, upper_total: Rat },
    /// An exact face that does not sum to one.
    #[error("the exact face sums to {total}, not exactly one")]
    NotNormalized { total: Rat },
    /// A key outside `[0, 1)`.
    #[error("the key {key} lies outside [0, 1)")]
    KeyOutOfRange { key: Rat },
    /// The decision law refused the draw's own width (unreachable through [`draw`]'s declarations).
    #[error("the release law refused the draw: {0}")]
    Law(String),
}

/// The declared name of the rule a draw is decided by (Lean `holdingLaw` at tolerance zero).
pub const CERTIFIED_DRAW_RULE: &str = "certified draw: release at tolerance zero, else hold";

/// **The certified draw of a declared key from an exact interval face** (module header).
///
/// For class `i` the certificate is `Σ_(j<i) upper_j ≤ key < Σ_(j≤i) lower_j`
/// (`Population.certified_inverseCDF_class`). A key the bounds leave plural returns
/// [`ReleaseReturn::Unresolved`] with every crossing class's exact bounds; it is never forced into
/// a class. The decision is taken through [`release`] at tolerance zero.
pub fn draw(face: &[ExactInterval], key: &Rat) -> Result<ReleaseReturn, DrawRefusal> {
    if face.is_empty() {
        return Err(DrawRefusal::EmptyFace);
    }
    if key < &Rat::zero() || key >= &Rat::one() {
        return Err(DrawRefusal::KeyOutOfRange { key: key.clone() });
    }
    let mut lower_total = Rat::zero();
    let mut upper_total = Rat::zero();
    for (class, mass) in face.iter().enumerate() {
        if mass.lower < Rat::zero() {
            return Err(DrawRefusal::NegativeMass {
                class,
                bound: mass.lower.clone(),
            });
        }
        if mass.upper > Rat::one() {
            return Err(DrawRefusal::MassAboveOne {
                class,
                bound: mass.upper.clone(),
            });
        }
        lower_total += &mass.lower;
        upper_total += &mass.upper;
    }
    if lower_total > Rat::one() || upper_total < Rat::one() {
        return Err(DrawRefusal::InvalidNormalization {
            lower_total,
            upper_total,
        });
    }
    decide(face.len(), inverse_cdf(face, key))
}

/// **The certified draw from an exact face** (a family's own normalized face): the point enclosure
/// of each mass, after the exact face is checked nonnegative and normalized.
pub fn draw_exact(face: &[Rat], key: &Rat) -> Result<ReleaseReturn, DrawRefusal> {
    if face.is_empty() {
        return Err(DrawRefusal::EmptyFace);
    }
    let mut total = Rat::zero();
    let mut points = Vec::with_capacity(face.len());
    for (class, mass) in face.iter().enumerate() {
        if mass < &Rat::zero() {
            return Err(DrawRefusal::NegativeMass {
                class,
                bound: mass.clone(),
            });
        }
        total += mass;
        points.push(ExactInterval::point(mass.clone()));
    }
    if total != Rat::one() {
        return Err(DrawRefusal::NotNormalized { total });
    }
    draw(&points, key)
}

/// The inverse-CDF reading of a validated face: the certified class, or every crossing class.
fn inverse_cdf(face: &[ExactInterval], key: &Rat) -> Result<CertifiedDraw, UnresolvedDraw> {
    let mut lower_prefix = Rat::zero();
    let mut upper_prefix = Rat::zero();
    let mut crossings = Vec::new();
    for (class, mass) in face.iter().enumerate() {
        let prior_upper = upper_prefix.clone();
        let through_lower = &lower_prefix + &mass.lower;
        if &prior_upper <= key && key < &through_lower {
            return Ok(CertifiedDraw {
                key: key.clone(),
                class,
                prior_upper,
                through_lower,
            });
        }
        if &lower_prefix <= key && key < &(&upper_prefix + &mass.upper) {
            crossings.push(CrossingBounds {
                class,
                prior_upper,
                through_lower: through_lower.clone(),
            });
        }
        lower_prefix = through_lower;
        upper_prefix += &mass.upper;
    }
    Err(UnresolvedDraw {
        key: key.clone(),
        crossings,
    })
}

/// The class reading's width, decided by the holding rule at tolerance zero through [`release`].
fn decide(
    classes: usize,
    reading: Result<CertifiedDraw, UnresolvedDraw>,
) -> Result<ReleaseReturn, DrawRefusal> {
    let law = |refusal: WidthRefusal| DrawRefusal::Law(refusal.to_string());
    let (diameter, attaining) = match &reading {
        Ok(_) => (Rat::zero(), WidthWitness::Point),
        Err(unresolved) => (
            Rat::one(),
            WidthWitness::Coordinate {
                coordinate: unresolved.crossings.first().map_or(0, |c| c.class),
            },
        ),
    };
    let width = ReceiverWidth::declared(
        "the key's inverse-CDF class",
        "the normalized faces inside the interval enclosure",
        DiameterNorm::Supremum,
        diameter,
        attaining,
        classes,
    )
    .map_err(law)?;
    let options = LawfulOptions::assemble(&width, Rat::zero(), None, false).map_err(law)?;
    let rule = DecisionRule::new(
        CERTIFIED_DRAW_RULE,
        WithinTolerance::Release,
        BeyondTolerance::Hold,
    );
    match (release(&rule, &options).map_err(law)?, reading) {
        (ReleaseReturn::Released { .. }, Ok(certified)) => Ok(ReleaseReturn::Drawn(certified)),
        (ReleaseReturn::Hold, Err(unresolved)) => Ok(ReleaseReturn::Unresolved(unresolved)),
        (decided, _) => Err(DrawRefusal::Law(format!(
            "the holding rule at tolerance zero returned {decided:?} against the draw's own width"
        ))),
    }
}

// -------------------------------------------------------------------------------------------
// the decision law
// -------------------------------------------------------------------------------------------

/// **The arms of the one decision law** (module header). `Released`, `Widen` and `Drawn` are
/// checked against what they name; `Ask` must be the offered probe; `Hold`, `Unresolved` and
/// `NoContinuationBridges` emit nothing and are the caller's.
///
/// Lean counterpart: `Foundation/ReceiverRelease.ReleaseReturn` (`Drawn` and `Unresolved` are its
/// `released` and `hold` at tolerance zero on the key's class reading).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReleaseReturn {
    /// The threshold commit: the width is inside the declared tolerance.
    Released {
        /// The exact width.
        width: Rat,
        /// The tolerance it fell inside.
        tolerance: Rat,
    },
    /// The certified draw: the key's class, with its certified cell.
    Drawn(CertifiedDraw),
    /// Retain the plural fibre and emit nothing at this receiver.
    Hold,
    /// A key the enclosure leaves plural: nothing emitted, the draw mass kept unresolved.
    Unresolved(UnresolvedDraw),
    /// Declare a wider tolerance, named.
    Widen {
        /// The proposed tolerance.
        tolerance: Rat,
    },
    /// Name the observation that would narrow the fibre.
    Ask {
        /// The offered probe.
        probe: ObservationProbe,
    },
    /// No admitted continuation bridges the gap.
    NoContinuationBridges {
        /// Why not, named.
        reason: String,
    },
}

impl ReleaseReturn {
    /// The class this return emits: the drawn class of a certified draw, and nothing otherwise.
    pub fn drawn_class(&self) -> Option<usize> {
        match self {
            Self::Drawn(certified) => Some(certified.class),
            _ => None,
        }
    }
}

/// **What the owner computed and what is therefore lawfully available** to the caller's decision.
/// The library computes the options; it does not choose among them.
///
/// [implemented-exact] Every field is private and the only constructor is [`Self::assemble`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawfulOptions {
    width: Rat,
    tolerance: Rat,
    inside_tolerance: bool,
    ask: Option<ObservationProbe>,
    bridges: bool,
}

impl LawfulOptions {
    /// Assemble the options from a width and the declared apparatus. The caller declares the
    /// tolerance; nothing here has a default. The result is a `Result` so that an incoherent
    /// assembly stays refusable as content.
    pub fn assemble(
        reading: &ReceiverWidth,
        tolerance: Rat,
        ask: Option<ObservationProbe>,
        bridges: bool,
    ) -> Result<Self, WidthRefusal> {
        let inside_tolerance = reading.releasable_at(&tolerance);
        Ok(Self {
            width: reading.diameter().clone(),
            tolerance,
            inside_tolerance,
            ask,
            bridges,
        })
    }

    /// The exact width.
    pub fn width(&self) -> &Rat {
        &self.width
    }

    /// The receiver's declared tolerance.
    pub fn tolerance(&self) -> &Rat {
        &self.tolerance
    }

    /// Whether the width is inside it. [`release`] never trusts this flag; it recomputes.
    pub fn inside_tolerance(&self) -> bool {
        self.inside_tolerance
    }

    /// The offered probe, when there is one to ask for.
    pub fn ask(&self) -> Option<&ObservationProbe> {
        self.ask.as_ref()
    }

    /// Whether any admitted continuation bridges the gap at all.
    pub fn bridges(&self) -> bool {
        self.bridges
    }
}

/// A caller's **declared** decision law. There is no default implementation and no blanket
/// implementation: the decision is supplied.
pub trait DecisionLaw {
    /// The law's declared name, for the refusal.
    fn name(&self) -> &str;
    /// The decision.
    fn decide(&self, options: &LawfulOptions) -> ReleaseReturn;
}

/// [definition] **What a declared rule returns inside its tolerance.**
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum WithinTolerance {
    /// Release the face at its width.
    Release,
    /// Retain the plural fibre and emit nothing.
    Hold,
}

/// [definition] **What a declared rule returns outside its tolerance**: never a release of that
/// face.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum BeyondTolerance {
    /// Retain the plural fibre and emit nothing.
    Hold,
    /// Declare the named wider tolerance (refused by [`release`] when the width is still outside).
    Widen(Rat),
    /// Ask the probe the options offer, holding when none is offered.
    Ask,
    /// Report that no admitted continuation bridges the gap, with the declared reason; held when
    /// the options say one does.
    NoContinuation(String),
}

/// [definition] **The data form of a declared decision law** (rebuild step 4 addition 8): a
/// declared name and the return it takes inside and beyond the tolerance, as data, so a backend
/// that cannot run a caller's code takes the decision as a value. It implements [`DecisionLaw`];
/// it is not a default, and its every return is checked by [`release`] like any other law's (Lean
/// `Foundation/ReceiverRelease.ReleaseLaw.sound`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct DecisionRule {
    name: String,
    within: WithinTolerance,
    beyond: BeyondTolerance,
}

impl DecisionRule {
    /// A declared rule.
    pub fn new(name: impl Into<String>, within: WithinTolerance, beyond: BeyondTolerance) -> Self {
        Self {
            name: name.into(),
            within,
            beyond,
        }
    }

    /// The return inside the tolerance.
    pub fn within(&self) -> &WithinTolerance {
        &self.within
    }

    /// The return beyond it.
    pub fn beyond(&self) -> &BeyondTolerance {
        &self.beyond
    }
}

impl DecisionLaw for DecisionRule {
    fn name(&self) -> &str {
        &self.name
    }

    /// The rule's return, read from the options' own exact width and tolerance (the flag is not
    /// trusted); an offer the options do not carry falls back to holding.
    fn decide(&self, options: &LawfulOptions) -> ReleaseReturn {
        if options.width() <= options.tolerance() {
            return match self.within {
                WithinTolerance::Release => ReleaseReturn::Released {
                    width: options.width().clone(),
                    tolerance: options.tolerance().clone(),
                },
                WithinTolerance::Hold => ReleaseReturn::Hold,
            };
        }
        match &self.beyond {
            BeyondTolerance::Hold => ReleaseReturn::Hold,
            BeyondTolerance::Widen(tolerance) => ReleaseReturn::Widen {
                tolerance: tolerance.clone(),
            },
            BeyondTolerance::Ask => match options.ask() {
                Some(probe) => ReleaseReturn::Ask {
                    probe: probe.clone(),
                },
                None => ReleaseReturn::Hold,
            },
            BeyondTolerance::NoContinuation(reason) if !options.bridges() => {
                ReleaseReturn::NoContinuationBridges {
                    reason: reason.clone(),
                }
            }
            BeyondTolerance::NoContinuation(_) => ReleaseReturn::Hold,
        }
    }
}

/// **Take the declared law's decision, and check what the library owns.**
///
/// A law returning [`ReleaseReturn::Released`] with the width outside its own declared tolerance is
/// refused by name; a law proposing a widening that does not contain the width, or asking for a
/// probe the options did not offer, is refused by name; and a law returning a draw is refused,
/// because a width decision carries no key ([`draw`] is the draw's own entry). Nothing else is
/// constrained: this module supplies no default and no global gate.
///
/// Lean counterpart: `ReleaseLaw.sound`, `ReleaseLaw.widenSound`.
pub fn release(
    law: &dyn DecisionLaw,
    options: &LawfulOptions,
) -> Result<ReleaseReturn, WidthRefusal> {
    let decision = law.decide(options);
    match &decision {
        ReleaseReturn::Released { width, tolerance } => {
            // The comparison is **recomputed** from the options' own exact width and tolerance
            // rather than trusted from the `inside_tolerance` flag, so a forged flag does not buy
            // a release.
            if options.width > options.tolerance || width > tolerance {
                return Err(WidthRefusal::ReleasedOutsideTolerance(Box::new(
                    ReleasedClaim {
                        law: law.name().to_owned(),
                        width: width.clone(),
                        tolerance: tolerance.clone(),
                    },
                )));
            }
        }
        ReleaseReturn::Ask { probe } => match &options.ask {
            Some(offered) if offered == probe => {}
            _ => {
                return Err(WidthRefusal::ProbeNotOffered {
                    law: law.name().to_owned(),
                    probe: probe.observation.clone(),
                });
            }
        },
        ReleaseReturn::Widen { tolerance } => {
            if options.width > *tolerance {
                return Err(WidthRefusal::WidenTooNarrow(Box::new(WidenClaim {
                    law: law.name().to_owned(),
                    width: options.width.clone(),
                    tolerance: tolerance.clone(),
                })));
            }
        }
        ReleaseReturn::Drawn(_) | ReleaseReturn::Unresolved(_) => {
            return Err(WidthRefusal::DrawNotOffered {
                law: law.name().to_owned(),
            });
        }
        ReleaseReturn::Hold | ReleaseReturn::NoContinuationBridges { .. } => {}
    }
    Ok(decision)
}

#[cfg(test)]
mod tests;
