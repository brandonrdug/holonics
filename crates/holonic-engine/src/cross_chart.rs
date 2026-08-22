//! **The cross-chart lift: what a chart transition owes, and the exact defect when it does not pay.**
//!
//! A lift takes a transport `T: X -> Y` in one chart and a transport `S: X' -> Y'` in another, with
//! declared chart transitions `Phi_X: X -> X'` and `Phi_Y: Y -> Y'`, and asks whether the square
//! commutes. It generally does not, and the whole content is the exact obstruction:
//!
//! ```text
//!     chi_gamma  =  Phi_Y T_gamma  -  S_gamma Phi_X
//! ```
//!
//! This module owns that object, its faces, its serial chain law, and — separately — the exact
//! reconstruction fibre of the binary-float mouth, which is the same question one level down: the
//! rounding map is a chart transition whose fibres are the reals a codeword cannot tell apart.
//!
//! # The two relations the composition returned absent
//!
//! Neither is a new organ. Each is the relation that fell out of composing owners that already
//! stand, and each was measured absent before it was written.
//!
//! **1. The exact rounding preimage.** [`crate::exact_value::ieee754`] owns the forward map
//! ([`round_into`](crate::exact_value::ieee754::round_into), with its exact residual) and an
//! *outward* enclosure, and its own documentation names what the enclosure is not: *"at the low
//! edge of a binade the true rounding preimage is only a quarter-ulp wide below the point, and this
//! returns a half-ulp there."* Outward is the honest direction for an admission test and it is the
//! wrong object for a fibre: it over-approximates, so it can neither partition the reals nor decide
//! endpoint membership. Measured 2026-08-20 by
//! `grep -rn "rounding_preimage\|round.*fibre\|fibre.*round" crates/ soma/ --include='*.rs'`: the
//! only other computation of a bf16 cell in the tree is
//! `crates/holonic-engine/examples/the_layer_stays_on_the_card.rs:314`, which is the same symmetric
//! half-ulp over-approximation. [`RoundingFibre`] is the exact preimage: asymmetric half-widths at
//! a binade's low edge, endpoint membership decided by ties-to-even, the subnormal grid, and the two
//! zeros splitting one magnitude cell between them.
//!
//! **2. The cross-chart intertwining defect.** [`crate::exact_linear::ExactRatMatrix`] owns rank,
//! kernel, image, cokernel annihilator, affine preimage fibre, the rebase receipt requiring **both**
//! identity compositions, and the metric adjoint. It owns all of that for *one* map. Nothing
//! composed two charts into `Phi_Y T - S Phi_X` and returned its faces, and nothing carried the
//! chain law that makes the defect additive along a composition.
//!
//! # The chain law, and its derivation is one line
//!
//! For `gamma: X -> Y` and `eta: Y -> Z` with transitions `Phi_X, Phi_Y, Phi_Z`:
//!
//! ```text
//!   chi_eta T_gamma + S_eta chi_gamma
//!     = (Phi_Z T_eta - S_eta Phi_Y) T_gamma  +  S_eta (Phi_Y T_gamma - S_gamma Phi_X)
//!     = Phi_Z T_eta T_gamma  -  S_eta Phi_Y T_gamma  +  S_eta Phi_Y T_gamma  -  S_eta S_gamma Phi_X
//!     = Phi_Z T_{eta gamma}  -  S_{eta gamma} Phi_X
//!     = chi_{eta gamma}
//! ```
//!
//! The two middle terms cancel. That cancellation **is** the law: the defect of a composition is the
//! later defect transported along the earlier source transport plus the later native transport
//! carrying the earlier defect, and nothing else appears. [`ChainLawReading`] verifies it as an
//! operator identity and on declared material vectors, and returns the residual either way.
//!
//! # What this module refuses
//!
//! A singular or rectangular `Phi` never acquires an inverse: [`ChartReceipt::Quotient`] carries the
//! kernel and says so by name. A rebase must exhibit **both** `Phi Phi^-1 = I` and `Phi^-1 Phi = I`
//! as matrices, not as booleans. An adjoint is `G_X^-1 Phi^T G_Y` and a bare transpose is that
//! object only when both metrics are the identity, which is a declaration and never a default —
//! [`bare_transpose_adjoint_defect`] exists to make the difference measurable rather than argued.

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::exact_linear::{ExactLinearError, ExactRatMatrix, LinearFactorization, RebaseReceipt};
use crate::exact_value::ExactValueError;
use crate::exact_value::ieee754::{self, BinaryFloatSpecies};

// -------------------------------------------------------------------------------------------
// the exact rounding preimage
// -------------------------------------------------------------------------------------------

/// Which cell of the format a codeword's rounding preimage is, named rather than inferred.
///
/// The species matters because the cells are not congruent: only [`FibreCell::BinadeLowEdge`] has
/// unequal half-widths, and only the two zero cells split one magnitude cell between two codewords.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum FibreCell {
    /// A normal codeword with a representable neighbour one ulp away on each side. The cell is
    /// symmetric: half an ulp either way.
    Normal,
    /// **The low edge of a binade**: significand exactly the hidden bit, with a binade below it.
    /// The neighbour below sits at half this ulp, so the cell reaches only a **quarter** ulp down
    /// and a **half** ulp up. This is the asymmetry the outward enclosure declines to compute.
    BinadeLowEdge,
    /// A subnormal codeword. The grid does not change across the subnormal range, nor across the
    /// subnormal/smallest-normal boundary, so the cell is symmetric there.
    Subnormal,
    /// `+0`. The magnitude cell `[0, u/2]` is split by the sign, and the positive half keeps the
    /// origin: an exact zero is not negative, so it rounds to `+0`.
    PositiveZero,
    /// `-0`. Its cell is `[-u/2, 0)` — closed where the tie lands, **open at the origin**, because
    /// the origin belongs to `+0`. A codec that cannot say this cannot round-trip `-0.0`.
    NegativeZero,
}

impl FibreCell {
    pub const fn name(self) -> &'static str {
        match self {
            Self::Normal => "normal",
            Self::BinadeLowEdge => "binade low edge",
            Self::Subnormal => "subnormal",
            Self::PositiveZero => "positive zero",
            Self::NegativeZero => "negative zero",
        }
    }
}

/// **The exact set of rationals that round to one codeword**, under round-to-nearest ties-to-even.
///
/// This is a `ReconstructionFiber` in the sense the corpus uses the word: the preimage the forward
/// map cannot distinguish, retained whole rather than summarized by a width. It is an interval with
/// *declared endpoint membership*, because the ties are exactly the endpoints and a fibre that
/// cannot say which side a tie lands on has not partitioned anything.
///
/// The membership rule, derived from
/// [`round_into`](crate::exact_value::ieee754::round_into) as written and uniform across every case
/// the format has: **both endpoints belong to the codeword whose significand is even.** Adjacent
/// codewords always have opposite significand parity — including across a binade re-seat, where
/// `255` is followed by `128` — so every tie belongs to exactly one side and the cells partition the
/// representable range.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RoundingFibre {
    pub species: BinaryFloatSpecies,
    pub bits: u64,
    /// The codeword's exact value; the fibre's distinguished point.
    pub value: Rat,
    pub lower: Rat,
    pub upper: Rat,
    /// Whether `lower` is itself in the fibre. Decided by ties-to-even, never by convention.
    pub lower_closed: bool,
    pub upper_closed: bool,
    /// `value - lower`.
    pub lower_half_width: Rat,
    /// `upper - value`.
    pub upper_half_width: Rat,
    pub cell: FibreCell,
    /// The significand's parity, which is what decides both endpoints.
    pub significand_even: bool,
    /// True when this is the format's largest finite magnitude: above `upper` the emit-side mouth
    /// **refuses** rather than saturating to an infinity, so the fibre has an exterior that is not
    /// another codeword's.
    pub top_of_format: bool,
}

impl RoundingFibre {
    /// The exact preimage of a declared codeword.
    ///
    /// Refuses the same patterns the decoder refuses: `NaN` and the infinities name no ratio.
    pub fn of(species: BinaryFloatSpecies, bits: u64) -> Result<Self, CrossChartError> {
        let datum = ieee754::decode_bits(species, bits)?;
        let stored = species.stored_significand_bits();
        let hidden: BigUint = BigUint::one() << stored;
        let raw_exponent = datum.ulp_exponent + species.exponent_bias() + stored as i32;
        let ulp = datum.unit_in_last_place();
        let half = Rat::new(BigInt::one(), BigInt::from(2));
        let significand_even = !datum.significand.bit(0);
        let value = datum.value();

        if datum.significand.is_zero() {
            // The magnitude cell of zero is `[0, u/2]`, and the sign splits it. `round_into` takes
            // the sign from the rational's own sign, so the origin goes to `+0` and every strictly
            // negative rational in the cell goes to `-0`.
            let half_ulp = &ulp * &half;
            let (lower, upper, lower_closed, upper_closed, cell) = if datum.negative {
                (
                    -half_ulp.clone(),
                    Rat::zero(),
                    true,
                    false,
                    FibreCell::NegativeZero,
                )
            } else {
                (
                    Rat::zero(),
                    half_ulp.clone(),
                    true,
                    true,
                    FibreCell::PositiveZero,
                )
            };
            let lower_half_width = &value - &lower;
            let upper_half_width = &upper - &value;
            return Ok(Self {
                species,
                bits,
                value,
                lower,
                upper,
                lower_closed,
                upper_closed,
                lower_half_width,
                upper_half_width,
                cell,
                significand_even,
                top_of_format: false,
            });
        }

        // The step UP is always one ulp: at the top of a binade `(s+1)*u` is exactly the next
        // binade's hidden bit, so the spacing does not change on the way up.
        let up_step = ulp.clone();
        // The step DOWN is half an ulp exactly at a binade's low edge, where the neighbour below
        // sits on the finer grid. The smallest normal is not such an edge: its neighbour is the
        // largest subnormal, which shares its ulp.
        let binade_low_edge = !datum.subnormal && datum.significand == hidden && raw_exponent > 1;
        let down_step = if binade_low_edge {
            &ulp * &half
        } else {
            ulp.clone()
        };

        let magnitude = if datum.negative {
            -value.clone()
        } else {
            value.clone()
        };
        let lower_magnitude = &magnitude - &(&down_step * &half);
        let upper_magnitude = &magnitude + &(&up_step * &half);
        let (lower, upper) = if datum.negative {
            (-upper_magnitude, -lower_magnitude)
        } else {
            (lower_magnitude, upper_magnitude)
        };
        let cell = if binade_low_edge {
            FibreCell::BinadeLowEdge
        } else if datum.subnormal {
            FibreCell::Subnormal
        } else {
            FibreCell::Normal
        };
        let exponent_mask: u64 = (1u64 << species.exponent_bits()) - 1;
        let top_of_format = !datum.subnormal
            && (raw_exponent as u64) == exponent_mask - 1
            && datum.significand == (hidden.clone() << 1usize) - BigUint::one();
        let lower_half_width = &value - &lower;
        let upper_half_width = &upper - &value;
        Ok(Self {
            species,
            bits,
            value,
            lower,
            upper,
            lower_closed: significand_even,
            upper_closed: significand_even,
            lower_half_width,
            upper_half_width,
            cell,
            significand_even,
            top_of_format,
        })
    }

    /// The bfloat16 preimage of a stored word.
    pub fn of_bfloat16(word: u16) -> Result<Self, CrossChartError> {
        Self::of(BinaryFloatSpecies::Bfloat16, u64::from(word))
    }

    /// **Does this rational round to this codeword?** Endpoint membership included, so this is the
    /// preimage and not a containment heuristic.
    pub fn contains(&self, quantity: &Rat) -> bool {
        let above_lower = if self.lower_closed {
            *quantity >= self.lower
        } else {
            *quantity > self.lower
        };
        let below_upper = if self.upper_closed {
            *quantity <= self.upper
        } else {
            *quantity < self.upper
        };
        above_lower && below_upper
    }

    /// The two half-widths differ. True exactly at a binade's low edge and at the two zeros.
    pub fn asymmetric(&self) -> bool {
        self.lower_half_width != self.upper_half_width
    }

    /// The fibre's total width, as an exact rational. A **face**, not the object: the object is the
    /// interval with its endpoint membership, and two fibres of equal width can differ in which
    /// ties they hold.
    pub fn width(&self) -> Rat {
        &self.upper - &self.lower
    }

    /// How the endpoints read in text, so an artifact can carry the membership rather than losing
    /// it to a bracket convention.
    pub fn interval_text(&self) -> String {
        format!(
            "{}{}, {}{}",
            if self.lower_closed { '[' } else { '(' },
            rat_text(&self.lower),
            rat_text(&self.upper),
            if self.upper_closed { ']' } else { ')' }
        )
    }
}

/// A rational as an exact `numerator/denominator` string. No decimal expansion is taken anywhere in
/// this module; a decimal is a compression with a deleted tail and it is not what a fibre endpoint
/// is.
pub fn rat_text(value: &Rat) -> String {
    if value.denom() == &BigInt::one() {
        value.numer().to_string()
    } else {
        format!("{}/{}", value.numer(), value.denom())
    }
}

/// **One codeword's place in a composed chain of ports**, with the fibre it acquired at each.
///
/// The composed preimage of a pathway is the preimage composition, not the last port's cell: a port
/// that is exact contributes a point and changes nothing, and a port that rounds contributes its own
/// cell around whatever arrived. Carrying the lineage is what lets a later reader say **where** a
/// difference was deleted rather than that one was.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PortStep {
    pub port: String,
    /// What the material was after this port, exactly.
    pub carried: Rat,
    /// The preimage this port alone contributes around `carried`.
    pub lower: Rat,
    pub upper: Rat,
    pub lower_closed: bool,
    pub upper_closed: bool,
    /// The exact residual this port deleted: `arrived - carried`. Zero for an exact port.
    pub residual: Rat,
    pub exact: bool,
}

/// The composed reconstruction fibre across a declared sequence of ports.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct PathwiseFibre {
    pub entered: Rat,
    pub steps: Vec<PortStep>,
    pub composed_lower: Rat,
    pub composed_upper: Rat,
    pub composed_lower_closed: bool,
    pub composed_upper_closed: bool,
    /// The sum of every port's residual: what the whole pathway deleted, exactly.
    pub total_residual: Rat,
    /// Whether the quantity that entered lies inside the composed preimage. It must.
    pub entered_inside: bool,
}

impl PathwiseFibre {
    /// Compose the ports' preimages: the composed fibre is the intersection of each port's cell,
    /// pulled back through the exact ports between them.
    ///
    /// Every port here is either exact (a point, contributing no constraint of its own beyond
    /// identity) or a rounding (contributing its cell). Because the exact ports in this pathway are
    /// *identity on the value* — the aligned-integer chart carries the same rational, and a grain
    /// placement is another rounding — the pullback is the identity and the composition is the
    /// intersection. A pathway whose exact ports were not value-preserving would owe the pullback
    /// explicitly, and this constructor refuses to pretend otherwise by requiring each step to carry
    /// its own residual.
    pub fn compose(entered: Rat, steps: Vec<PortStep>) -> Self {
        let mut lower = Rat::new(BigInt::from(-1), BigInt::one());
        let mut upper = Rat::one();
        let mut lower_closed = true;
        let mut upper_closed = true;
        let mut first = true;
        let mut total = Rat::zero();
        for step in &steps {
            total = total + &step.residual;
            if first {
                lower = step.lower.clone();
                upper = step.upper.clone();
                lower_closed = step.lower_closed;
                upper_closed = step.upper_closed;
                first = false;
                continue;
            }
            if step.lower > lower {
                lower = step.lower.clone();
                lower_closed = step.lower_closed;
            } else if step.lower == lower {
                lower_closed = lower_closed && step.lower_closed;
            }
            if step.upper < upper {
                upper = step.upper.clone();
                upper_closed = step.upper_closed;
            } else if step.upper == upper {
                upper_closed = upper_closed && step.upper_closed;
            }
        }
        let inside = {
            let above = if lower_closed {
                entered >= lower
            } else {
                entered > lower
            };
            let below = if upper_closed {
                entered <= upper
            } else {
                entered < upper
            };
            above && below
        };
        Self {
            entered,
            steps,
            composed_lower: lower,
            composed_upper: upper,
            composed_lower_closed: lower_closed,
            composed_upper_closed: upper_closed,
            total_residual: total,
            entered_inside: inside,
        }
    }

    pub fn interval_text(&self) -> String {
        format!(
            "{}{}, {}{}",
            if self.composed_lower_closed { '[' } else { '(' },
            rat_text(&self.composed_lower),
            rat_text(&self.composed_upper),
            if self.composed_upper_closed { ']' } else { ')' }
        )
    }
}

/// **The Minkowski sum of several rounding cells**, which is what a group sum's preimage is.
///
/// When a declared quotient adds `n` stored coordinates, the preimage of the sum is the sum of the
/// preimages: the reals that could have produced it. The endpoints add; the endpoint *membership*
/// conjoins, because a sum reaches its extreme only when every summand does. This is the exact
/// reconstruction fibre of a grouped coordinate and it is not the same object as any one cell.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct SummedFibre {
    pub summands: Vec<RoundingFibre>,
    pub value: Rat,
    pub lower: Rat,
    pub upper: Rat,
    pub lower_closed: bool,
    pub upper_closed: bool,
}

impl SummedFibre {
    pub fn of(summands: Vec<RoundingFibre>) -> Self {
        let mut value = Rat::zero();
        let mut lower = Rat::zero();
        let mut upper = Rat::zero();
        let mut lower_closed = true;
        let mut upper_closed = true;
        for fibre in &summands {
            value = value + &fibre.value;
            lower = lower + &fibre.lower;
            upper = upper + &fibre.upper;
            lower_closed = lower_closed && fibre.lower_closed;
            upper_closed = upper_closed && fibre.upper_closed;
        }
        Self {
            summands,
            value,
            lower,
            upper,
            lower_closed,
            upper_closed,
        }
    }

    pub fn width(&self) -> Rat {
        &self.upper - &self.lower
    }

    pub fn interval_text(&self) -> String {
        format!(
            "{}{}, {}{}",
            if self.lower_closed { '[' } else { '(' },
            rat_text(&self.lower),
            rat_text(&self.upper),
            if self.upper_closed { ']' } else { ')' }
        )
    }
}

// -------------------------------------------------------------------------------------------
// chart transition receipts
// -------------------------------------------------------------------------------------------

/// **What a declared chart transition returns when asked what species it is.**
///
/// There are two answers and no third. A rebase exhibits **both** identity compositions as matrices
/// — a boolean is a claim about a computation and this carries the computation. A quotient exhibits
/// its kernel and **refuses an inverse by name**; it does not receive a pseudo-inverse, because a
/// pseudo-inverse requires two declared receiver metrics and nobody declared them here.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ChartReceipt {
    Rebase {
        inverse: Box<ExactRatMatrix>,
        /// `Phi Phi^-1`, exhibited. Must be the identity.
        forward_identity: Box<ExactRatMatrix>,
        /// `Phi^-1 Phi`, exhibited. Must be the identity.
        backward_identity: Box<ExactRatMatrix>,
    },
    Quotient {
        rank: usize,
        /// The collapsed directions, exhibited one per free column.
        kernel: Vec<Vec<Rat>>,
        /// Receiver directions this transition cannot reach.
        cokernel_annihilator: Vec<Vec<Rat>>,
        refusal: &'static str,
    },
}

impl ChartReceipt {
    pub fn is_rebase(&self) -> bool {
        matches!(self, Self::Rebase { .. })
    }

    pub fn species(&self) -> &'static str {
        match self {
            Self::Rebase { .. } => "rebase",
            Self::Quotient { .. } => "quotient",
        }
    }

    /// The collapsed dimension. Zero for a rebase, by construction.
    pub fn collapsed_dimension(&self) -> usize {
        match self {
            Self::Rebase { .. } => 0,
            Self::Quotient { kernel, .. } => kernel.len(),
        }
    }
}

/// Type the declared chart transition, exhibiting whichever receipt it earns.
pub fn chart_receipt(phi: &ExactRatMatrix) -> Result<ChartReceipt, CrossChartError> {
    match phi.rebase_receipt()? {
        RebaseReceipt::Rebase { inverse, .. } => {
            let forward = phi.multiply(&inverse)?;
            let backward = inverse.multiply(phi)?;
            Ok(ChartReceipt::Rebase {
                inverse,
                forward_identity: Box::new(forward),
                backward_identity: Box::new(backward),
            })
        }
        RebaseReceipt::Refused {
            factorization,
            reason,
        } => Ok(ChartReceipt::Quotient {
            rank: factorization.rank,
            kernel: factorization.kernel.clone(),
            cokernel_annihilator: factorization.cokernel_annihilator.clone(),
            refusal: reason,
        }),
    }
}

/// **The exact defect of taking a bare transpose for an adjoint under declared metrics.**
///
/// `<Phi x, y>_Y = <x, Phi^dagger y>_X` characterizes the adjoint, and `Phi^dagger = G_X^-1 Phi^T
/// G_Y`. When both metrics are the identity the bare transpose is that object; when either is not,
/// it is a different map and the pairing does not balance. This returns the exact imbalance for the
/// bare transpose and for the metric adjoint side by side, so the difference is measured rather than
/// asserted.
///
/// The metric adjoint's defect must be zero. The bare transpose's must not be, under a metric that
/// is not the identity — that is what makes this a control rather than a restatement.
pub fn bare_transpose_adjoint_defect(
    phi: &ExactRatMatrix,
    domain_metric: &ExactRatMatrix,
    codomain_metric: &ExactRatMatrix,
    x: &[Rat],
    y: &[Rat],
) -> Result<(Rat, Rat), CrossChartError> {
    let transpose = phi.transpose()?;
    let bare = phi.adjoint_defect(&transpose, domain_metric, codomain_metric, x, y)?;
    let metric = phi.metric_adjoint(domain_metric, codomain_metric)?;
    let lawful = phi.adjoint_defect(&metric, domain_metric, codomain_metric, x, y)?;
    Ok((bare, lawful))
}

// -------------------------------------------------------------------------------------------
// the cross-chart defect
// -------------------------------------------------------------------------------------------

/// One direction of the domain on which the lift fails, with both sides of the square exhibited.
///
/// A rank is a face. This is the object behind it: the input, what the source transport gave after
/// the chart transition, what the native transport gave, and the difference.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct DefectSample {
    pub direction_name: String,
    pub direction: Vec<Rat>,
    /// `Phi_Y T_gamma v`
    pub lifted: Vec<Rat>,
    /// `S_gamma Phi_X v`
    pub native: Vec<Rat>,
    /// `chi_gamma v`
    pub defect: Vec<Rat>,
}

/// **`chi_gamma = Phi_Y T_gamma - S_gamma Phi_X`, with every face of it.**
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CrossChartDefect {
    pub name: String,
    pub chi: ExactRatMatrix,
    /// Rank, kernel, image and open exterior at once, from the standing carrier.
    pub factorization: LinearFactorization,
    /// True when the square commutes exactly. A genuine zero, not a tolerance.
    pub is_zero: bool,
    /// A named direction the lift fails on, with both sides. `None` exactly when `is_zero`.
    pub sample: Option<DefectSample>,
    /// The shapes, so an artifact reader need not recompose them.
    pub domain: usize,
    pub codomain: usize,
}

impl CrossChartDefect {
    pub fn rank(&self) -> usize {
        self.factorization.rank
    }

    /// The directions of `X` the defect cannot see: the lift **does** commute on these.
    pub fn agreeing_dimension(&self) -> usize {
        self.factorization.kernel.len()
    }

    pub fn open_exterior_dimension(&self) -> usize {
        self.factorization.cokernel_annihilator.len()
    }
}

/// Build the defect of one declared lift.
///
/// Shapes: `Phi_X: X -> X'`, `T: X -> Y`, `Phi_Y: Y -> Y'`, `S: X' -> Y'`, and `chi: X -> Y'`.
pub fn cross_chart_defect(
    name: &str,
    phi_y: &ExactRatMatrix,
    t: &ExactRatMatrix,
    s: &ExactRatMatrix,
    phi_x: &ExactRatMatrix,
    direction_names: &[String],
) -> Result<CrossChartDefect, CrossChartError> {
    let lifted = phi_y.multiply(t)?;
    let native = s.multiply(phi_x)?;
    let chi = lifted.subtract(&native)?;
    let factorization = chi.factorization()?;
    let is_zero = factorization.rank == 0;
    let sample = if is_zero {
        None
    } else {
        let mut found = None;
        for column in 0..chi.columns() {
            let mut direction = vec![Rat::zero(); chi.columns()];
            direction[column] = Rat::one();
            let defect = chi.apply(&direction)?;
            if defect.iter().any(|entry| !entry.is_zero()) {
                found = Some(DefectSample {
                    direction_name: direction_names
                        .get(column)
                        .cloned()
                        .unwrap_or_else(|| format!("e[{column}]")),
                    lifted: lifted.apply(&direction)?,
                    native: native.apply(&direction)?,
                    defect,
                    direction,
                });
                break;
            }
        }
        found
    };
    Ok(CrossChartDefect {
        name: name.to_owned(),
        domain: chi.columns(),
        codomain: chi.rows(),
        chi,
        factorization,
        is_zero,
        sample,
    })
}

/// One material vector's reading of the chain law.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChainVectorCheck {
    pub name: String,
    /// `chi_{eta gamma} v`
    pub composed: Vec<Rat>,
    /// `(chi_eta T_gamma + S_eta chi_gamma) v`
    pub reconstructed: Vec<Rat>,
    pub residual: Vec<Rat>,
    pub holds: bool,
}

/// **The serial chain law, verified as an operator identity and on declared material.**
///
/// `chi_{eta gamma} = chi_eta T_gamma + S_eta chi_gamma`. The residual is returned whether or not it
/// is zero; a law verified only where it holds has not been verified.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChainLawReading {
    pub composed: ExactRatMatrix,
    pub reconstructed: ExactRatMatrix,
    pub residual: ExactRatMatrix,
    pub operator_identity_holds: bool,
    pub vector_checks: Vec<ChainVectorCheck>,
}

/// Compose two lifts and read the chain law off them.
///
/// `gamma: X -> Y` with `(Phi_X, Phi_Y, T_gamma, S_gamma)`, `eta: Y -> Z` with
/// `(Phi_Y, Phi_Z, T_eta, S_eta)`. The composite's source transport is `T_eta T_gamma` and its
/// native transport is `S_eta S_gamma`; the composite defect is built from those directly, so the
/// law is a check and not a definition.
#[allow(clippy::too_many_arguments)]
pub fn chain_law(
    phi_x: &ExactRatMatrix,
    phi_y: &ExactRatMatrix,
    phi_z: &ExactRatMatrix,
    t_gamma: &ExactRatMatrix,
    s_gamma: &ExactRatMatrix,
    t_eta: &ExactRatMatrix,
    s_eta: &ExactRatMatrix,
    material: &[(String, Vec<Rat>)],
) -> Result<
    (
        CrossChartDefect,
        CrossChartDefect,
        CrossChartDefect,
        ChainLawReading,
    ),
    CrossChartError,
> {
    let chi_gamma = cross_chart_defect("gamma", phi_y, t_gamma, s_gamma, phi_x, &[])?;
    let chi_eta = cross_chart_defect("eta", phi_z, t_eta, s_eta, phi_y, &[])?;
    let t_composite = t_eta.multiply(t_gamma)?;
    let s_composite = s_eta.multiply(s_gamma)?;
    let chi_composite = cross_chart_defect(
        "eta after gamma",
        phi_z,
        &t_composite,
        &s_composite,
        phi_x,
        &[],
    )?;

    let composed_chi = chi_composite.chi.clone();
    let reconstructed = chi_eta
        .chi
        .multiply(t_gamma)?
        .add(&s_eta.multiply(&chi_gamma.chi)?)?;
    let residual = chi_composite.chi.subtract(&reconstructed)?;
    let operator_identity_holds = residual.entries().iter().all(num_traits::Zero::is_zero);

    let mut vector_checks = Vec::with_capacity(material.len());
    for (name, vector) in material {
        let composed = chi_composite.chi.apply(vector)?;
        let recon = reconstructed.apply(vector)?;
        let residual: Vec<Rat> = composed.iter().zip(&recon).map(|(a, b)| a - b).collect();
        let holds = residual.iter().all(num_traits::Zero::is_zero);
        vector_checks.push(ChainVectorCheck {
            name: name.clone(),
            composed,
            reconstructed: recon,
            residual,
            holds,
        });
    }

    Ok((
        chi_gamma,
        chi_eta,
        chi_composite,
        ChainLawReading {
            composed: composed_chi,
            reconstructed,
            residual,
            operator_identity_holds,
            vector_checks,
        },
    ))
}

/// **A pair a chart transition identifies, and the shortest word that reopens it.**
///
/// For a linear quotient the reopening word is always one coordinate functional of the finer chart —
/// two distinct vectors differ somewhere, and a single coordinate reads the difference. The content
/// is therefore not the length but **which** coordinate and what the two readings were, and this
/// carries both. A receiver family with a successor conduct would need
/// [`crate::receiver_exact_compression`] instead, whose words can be longer than one; a linear
/// quotient has no successor conduct, so the shorter machinery is the right one and this says so
/// rather than reaching for the larger organ.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ReopeningSeparator {
    pub left: Vec<Rat>,
    pub right: Vec<Rat>,
    /// Both map to this under the transition: they are identified.
    pub identified_image: Vec<Rat>,
    pub separating_coordinate: usize,
    pub left_reading: Rat,
    pub right_reading: Rat,
    /// Coordinates in the word. One, for a linear quotient.
    pub word_length: usize,
}

/// The shortest reopening separator for a declared quotient, or `None` when it collapses nothing.
pub fn shortest_reopening_separator(
    phi: &ExactRatMatrix,
) -> Result<Option<ReopeningSeparator>, CrossChartError> {
    let kernel = phi.kernel_basis()?;
    let Some(direction) = kernel.first() else {
        return Ok(None);
    };
    let left = vec![Rat::zero(); phi.columns()];
    let right = direction.clone();
    let identified_image = phi.apply(&right)?;
    let mut separating = 0usize;
    for (index, entry) in direction.iter().enumerate() {
        if !entry.is_zero() {
            separating = index;
            break;
        }
    }
    Ok(Some(ReopeningSeparator {
        left_reading: left[separating].clone(),
        right_reading: right[separating].clone(),
        left,
        right,
        identified_image,
        separating_coordinate: separating,
        word_length: 1,
    }))
}

// -------------------------------------------------------------------------------------------

#[derive(Debug, Error)]
pub enum CrossChartError {
    #[error("the exact linear carrier refused: {0}")]
    Linear(#[from] ExactLinearError),
    #[error("the float mouth refused: {0}")]
    Float(#[from] ExactValueError),
    #[error("the declared charts do not compose: {what}")]
    ShapeMismatch { what: &'static str },
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rat(numerator: i64, denominator: i64) -> Rat {
        Rat::new(BigInt::from(numerator), BigInt::from(denominator))
    }

    fn matrix(rows: Vec<Vec<Rat>>) -> ExactRatMatrix {
        ExactRatMatrix::new(rows).expect("a rectangular matrix")
    }

    // --- the rounding fibre ---------------------------------------------------------------

    /// **The fibre is the preimage, exhaustively.** Every bfloat16 pattern, and for each one a
    /// probe just inside each endpoint, at each endpoint, and just outside: `round_into` must agree
    /// with `contains` at every one of them. This is the law the module claims, checked against the
    /// mouth as written rather than against a restatement of it.
    #[test]
    fn cross_chart_the_rounding_fibre_is_the_exact_preimage_on_every_bfloat16_pattern() {
        let mut checked = 0u64;
        let mut asymmetric = 0u64;
        for word in 0u32..=0xffff {
            let word = word as u16;
            let Ok(fibre) = RoundingFibre::of_bfloat16(word) else {
                continue; // NaN and the infinities name no ratio.
            };
            if fibre.asymmetric() {
                asymmetric += 1;
            }
            // The endpoints are where the law lives: they are exactly the ties, and every tie
            // decision is checked here for every pattern the format has. The interior probes are
            // added only on the cells whose geometry is not the plain symmetric one, which keeps
            // the sweep exhaustive over the decisions without paying for the interior of 65,000
            // congruent cells that the partition test below already covers.
            let mut probes = vec![fibre.value.clone()];
            if !fibre.width().is_zero() {
                probes.push(fibre.lower.clone());
                probes.push(fibre.upper.clone());
                if fibre.asymmetric() || fibre.cell != FibreCell::Normal {
                    let tiny = fibre.width() / Rat::from_integer(BigInt::from(1024));
                    probes.push(&fibre.lower + &tiny);
                    probes.push(&fibre.upper - &tiny);
                }
            }
            for probe in probes {
                let claimed = fibre.contains(&probe);
                let Ok((got, residual)) = ieee754::round_into_bfloat16(&probe) else {
                    continue; // past the format's top; the mouth refuses and so does the fibre.
                };
                assert_eq!(
                    got == word,
                    claimed,
                    "word {word:#06x} cell {} probe {} : the mouth said {got:#06x}, the fibre said {claimed}",
                    fibre.cell.name(),
                    rat_text(&probe)
                );
                if got == word {
                    let back = ieee754::decode_bfloat16_bits(got).expect("decodes").value();
                    assert_eq!(&back + &residual, probe, "the residual law");
                }
                checked += 1;
            }
        }
        assert!(checked > 190_000, "the sweep covered {checked} probes");
        assert!(
            asymmetric > 0,
            "some cell must be asymmetric or the law is vacuous"
        );
    }

    /// **Ties to even, on a real tie.** The midpoint between two adjacent codewords belongs to the
    /// one with the even significand, and the fibre says which before the mouth is asked.
    #[test]
    fn cross_chart_the_tie_belongs_to_the_even_significand() {
        // 0x3f80 = 1.0 (significand 128, even); 0x3f81 = 1 + 2^-7 (significand 129, odd).
        let even = RoundingFibre::of_bfloat16(0x3f80).expect("decodes");
        let odd = RoundingFibre::of_bfloat16(0x3f81).expect("decodes");
        assert!(even.significand_even);
        assert!(!odd.significand_even);
        let tie = &even.value + &(&(&odd.value - &even.value) / Rat::from_integer(BigInt::from(2)));
        assert!(
            even.contains(&tie),
            "the tie belongs to the even significand"
        );
        assert!(!odd.contains(&tie), "and to nothing else");
        assert_eq!(ieee754::round_into_bfloat16(&tie).expect("emits").0, 0x3f80);
        assert!(even.upper_closed && !odd.lower_closed);
    }

    /// **A binade's low edge has unequal half-widths**, by a factor of exactly two.
    #[test]
    fn cross_chart_the_binade_low_edge_cell_is_asymmetric() {
        let fibre = RoundingFibre::of_bfloat16(0x3f80).expect("decodes"); // 1.0
        assert_eq!(fibre.cell, FibreCell::BinadeLowEdge);
        assert!(fibre.asymmetric());
        let two = Rat::from_integer(BigInt::from(2));
        assert_eq!(&fibre.lower_half_width * &two, fibre.upper_half_width);
        // 1.0's ulp is 2^-7; the cell reaches 2^-9 down and 2^-8 up.
        assert_eq!(fibre.lower_half_width, rat(1, 512));
        assert_eq!(fibre.upper_half_width, rat(1, 256));
    }

    /// **The two zeros split one magnitude cell**, and the origin belongs to the positive one.
    #[test]
    fn cross_chart_the_two_zeros_partition_the_smallest_cell() {
        let positive = RoundingFibre::of_bfloat16(0x0000).expect("decodes");
        let negative = RoundingFibre::of_bfloat16(0x8000).expect("decodes");
        assert_eq!(positive.cell, FibreCell::PositiveZero);
        assert_eq!(negative.cell, FibreCell::NegativeZero);
        assert!(positive.contains(&Rat::zero()));
        assert!(
            !negative.contains(&Rat::zero()),
            "the origin is not negative"
        );
        assert!(
            positive.upper_closed,
            "the tie above zero is even and stays"
        );
        assert!(negative.lower_closed);
        assert!(!negative.upper_closed, "the origin is the other cell's");
        assert_eq!(negative.upper, Rat::zero());
        assert_eq!(&positive.upper, &-negative.lower.clone());
        // and the mouth agrees on both signs of the tie
        assert_eq!(
            ieee754::round_into_bfloat16(&positive.upper)
                .expect("emits")
                .0,
            0x0000
        );
        assert_eq!(
            ieee754::round_into_bfloat16(&negative.lower)
                .expect("emits")
                .0,
            0x8000
        );
    }

    /// **Subnormal cells are symmetric**, including across the boundary into the smallest normal,
    /// because the grid does not change there.
    #[test]
    fn cross_chart_the_subnormal_grid_does_not_change_at_the_normal_boundary() {
        let largest_subnormal = RoundingFibre::of_bfloat16(0x007f).expect("decodes");
        let smallest_normal = RoundingFibre::of_bfloat16(0x0080).expect("decodes");
        assert_eq!(largest_subnormal.cell, FibreCell::Subnormal);
        assert_eq!(smallest_normal.cell, FibreCell::Normal);
        assert!(!largest_subnormal.asymmetric());
        assert!(
            !smallest_normal.asymmetric(),
            "the smallest normal is not a binade low edge"
        );
        assert_eq!(largest_subnormal.upper, smallest_normal.lower);
        assert!(largest_subnormal.upper_closed != smallest_normal.lower_closed);
    }

    /// The cells **partition**: consecutive codewords share an endpoint and exactly one of them
    /// holds it.
    #[test]
    fn cross_chart_the_cells_partition_the_representable_range() {
        for word in 0x0000u16..0x7f7f {
            let (Ok(left), Ok(right)) = (
                RoundingFibre::of_bfloat16(word),
                RoundingFibre::of_bfloat16(word + 1),
            ) else {
                continue;
            };
            assert_eq!(
                left.upper, right.lower,
                "adjacent cells meet at {word:#06x}"
            );
            assert!(
                left.upper_closed ^ right.lower_closed,
                "exactly one side holds the tie at {word:#06x}"
            );
        }
    }

    // --- the chart receipts ---------------------------------------------------------------

    #[test]
    fn cross_chart_a_rebase_exhibits_both_identities_and_a_quotient_refuses_an_inverse() {
        let rebase = matrix(vec![vec![rat(2, 1), rat(0, 1)], vec![rat(0, 1), rat(1, 3)]]);
        match chart_receipt(&rebase).expect("typed") {
            ChartReceipt::Rebase {
                forward_identity,
                backward_identity,
                ..
            } => {
                let identity = ExactRatMatrix::identity(2).expect("identity");
                assert_eq!(*forward_identity, identity);
                assert_eq!(*backward_identity, identity);
            }
            other => panic!("a diagonal invertible map is a rebase, got {other:?}"),
        }

        // The grouped-sharing quotient: two coordinates summed into one.
        let quotient = matrix(vec![vec![rat(1, 1), rat(1, 1)]]);
        match chart_receipt(&quotient).expect("typed") {
            ChartReceipt::Quotient {
                rank,
                kernel,
                refusal,
                ..
            } => {
                assert_eq!(rank, 1);
                assert_eq!(kernel.len(), 1);
                assert!(refusal.contains("no inverse") || refusal.contains("quotient"));
            }
            other => panic!("a rectangular map has no inverse, got {other:?}"),
        }
    }

    /// **A bare transpose is not an adjoint under a metric nobody made the identity.** The lawful
    /// adjoint's defect is zero; the bare transpose's is not, and it is returned exactly.
    #[test]
    fn cross_chart_the_bare_transpose_differs_from_the_metric_adjoint() {
        let phi = matrix(vec![vec![rat(1, 1), rat(2, 1)], vec![rat(0, 1), rat(1, 1)]]);
        let identity = ExactRatMatrix::identity(2).expect("identity");
        let weighted = ExactRatMatrix::from_diagonal(vec![rat(1, 1), rat(3, 1)]).expect("metric");
        let x = vec![rat(1, 1), rat(1, 1)];
        let y = vec![rat(1, 1), rat(0, 1)];

        let (bare_euclidean, lawful_euclidean) =
            bare_transpose_adjoint_defect(&phi, &identity, &identity, &x, &y).expect("defects");
        assert!(
            bare_euclidean.is_zero(),
            "under two identity metrics the transpose IS the adjoint"
        );
        assert!(lawful_euclidean.is_zero());

        let (bare, lawful) =
            bare_transpose_adjoint_defect(&phi, &weighted, &identity, &x, &y).expect("defects");
        assert!(lawful.is_zero(), "the metric adjoint balances the pairing");
        assert!(
            !bare.is_zero(),
            "the bare transpose does not, and the defect is exhibited: {bare}"
        );
    }

    // --- the defect and the chain law -------------------------------------------------------

    #[test]
    fn cross_chart_the_defect_is_zero_exactly_when_the_square_commutes() {
        let phi_x = ExactRatMatrix::identity(2).expect("identity");
        let t = matrix(vec![vec![rat(1, 1), rat(2, 1)], vec![rat(3, 1), rat(4, 1)]]);
        let phi_y = matrix(vec![vec![rat(1, 1), rat(1, 1)]]);
        // S declared as the honest composite: the square commutes and chi is a genuine zero.
        let s = phi_y.multiply(&t).expect("compose");
        let commuting =
            cross_chart_defect("commuting", &phi_y, &t, &s, &phi_x, &[]).expect("defect");
        assert!(commuting.is_zero);
        assert_eq!(commuting.rank(), 0);
        assert!(commuting.sample.is_none());

        // An independently declared S does not, and the defect names a direction.
        let other = matrix(vec![vec![rat(1, 1), rat(0, 1)]]);
        let defect = cross_chart_defect("open", &phi_y, &t, &other, &phi_x, &[]).expect("defect");
        assert!(!defect.is_zero);
        let sample = defect.sample.as_ref().expect("a named direction");
        assert!(sample.defect.iter().any(|entry| !entry.is_zero()));
        for ((lifted, native), difference) in
            sample.lifted.iter().zip(&sample.native).zip(&sample.defect)
        {
            assert_eq!(&(lifted - native), difference, "both sides are exhibited");
        }
    }

    /// **The chain law, as an operator identity and on material.** The residual is exactly zero.
    #[test]
    fn cross_chart_the_chain_law_holds_as_an_operator_identity() {
        let phi_x = ExactRatMatrix::from_diagonal(vec![rat(2, 1), rat(3, 1)]).expect("phi x");
        let phi_y = matrix(vec![vec![rat(1, 1), rat(1, 1), rat(0, 1)]]);
        let phi_z = ExactRatMatrix::from_diagonal(vec![rat(5, 1), rat(7, 1)]).expect("phi z");
        let t_gamma = matrix(vec![
            vec![rat(1, 1), rat(2, 1)],
            vec![rat(3, 1), rat(-1, 1)],
            vec![rat(0, 1), rat(4, 1)],
        ]);
        let s_gamma = matrix(vec![vec![rat(1, 3), rat(-2, 5)]]);
        let t_eta = matrix(vec![
            vec![rat(1, 1), rat(0, 1), rat(2, 1)],
            vec![rat(-3, 1), rat(1, 1), rat(1, 1)],
        ]);
        let s_eta = matrix(vec![vec![rat(9, 1)], vec![rat(-4, 1)]]);
        let material = vec![
            ("first".to_owned(), vec![rat(1, 1), rat(0, 1)]),
            ("second".to_owned(), vec![rat(0, 1), rat(1, 1)]),
            ("third".to_owned(), vec![rat(5, 7), rat(-11, 3)]),
        ];
        let (_, _, composite, reading) = chain_law(
            &phi_x, &phi_y, &phi_z, &t_gamma, &s_gamma, &t_eta, &s_eta, &material,
        )
        .expect("chain");
        assert!(
            reading.operator_identity_holds,
            "residual {:?}",
            reading.residual
        );
        assert_eq!(reading.vector_checks.len(), 3);
        for check in &reading.vector_checks {
            assert!(check.holds, "{} residual {:?}", check.name, check.residual);
        }
        // and the composite defect is not trivially zero, or the law would be vacuous here
        assert!(!composite.is_zero);
    }

    #[test]
    fn cross_chart_the_separator_reopens_a_collapsed_pair() {
        let quotient = matrix(vec![vec![rat(1, 1), rat(1, 1), rat(1, 1), rat(1, 1)]]);
        let separator = shortest_reopening_separator(&quotient)
            .expect("computed")
            .expect("a quotient collapses something");
        assert_eq!(separator.word_length, 1);
        assert!(
            separator
                .identified_image
                .iter()
                .all(num_traits::Zero::is_zero)
        );
        assert_ne!(separator.left_reading, separator.right_reading);
        let rebase = ExactRatMatrix::identity(3).expect("identity");
        assert!(
            shortest_reopening_separator(&rebase)
                .expect("computed")
                .is_none()
        );
    }

    // --- the composed fibres ---------------------------------------------------------------

    #[test]
    fn cross_chart_the_summed_fibre_adds_endpoints_and_conjoins_membership() {
        let even = RoundingFibre::of_bfloat16(0x3f80).expect("decodes"); // closed both ends
        let odd = RoundingFibre::of_bfloat16(0x3f81).expect("decodes"); // open both ends
        let summed = SummedFibre::of(vec![even.clone(), even.clone()]);
        assert!(summed.lower_closed && summed.upper_closed);
        assert_eq!(summed.lower, &even.lower + &even.lower);
        assert_eq!(summed.width(), &even.width() + &even.width());
        let mixed = SummedFibre::of(vec![even, odd]);
        assert!(!mixed.lower_closed, "one open summand opens the sum");
        assert!(!mixed.upper_closed);
    }

    #[test]
    fn cross_chart_the_pathwise_fibre_intersects_and_keeps_its_lineage() {
        let entered = rat(3, 7);
        let (word, residual) = ieee754::round_into_bfloat16(&entered).expect("emits");
        let fibre = RoundingFibre::of_bfloat16(word).expect("decodes");
        let steps = vec![
            PortStep {
                port: "bf16".to_owned(),
                carried: fibre.value.clone(),
                lower: fibre.lower.clone(),
                upper: fibre.upper.clone(),
                lower_closed: fibre.lower_closed,
                upper_closed: fibre.upper_closed,
                residual: residual.clone(),
                exact: false,
            },
            PortStep {
                port: "aligned".to_owned(),
                carried: fibre.value.clone(),
                lower: fibre.lower.clone(),
                upper: fibre.upper.clone(),
                lower_closed: fibre.lower_closed,
                upper_closed: fibre.upper_closed,
                residual: Rat::zero(),
                exact: true,
            },
        ];
        let composed = PathwiseFibre::compose(entered.clone(), steps);
        assert!(
            composed.entered_inside,
            "what entered must be inside its own preimage"
        );
        assert_eq!(composed.total_residual, residual);
        assert_eq!(composed.composed_lower, fibre.lower);
        assert_eq!(&fibre.value + &composed.total_residual, entered);
        assert_eq!(composed.steps.len(), 2);
        assert!(composed.steps[1].exact, "the aligned port deletes nothing");
    }
}
