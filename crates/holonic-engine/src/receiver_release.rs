//! **Receiver width and release: uncertainty as a structure, not a scalar.**
//!
//! [definition] This module is the executable owner of item **R6** of
//! `docs/plans/THE_RECEIVER_ATLAS_SEPARATES_WHAT_ONE_FACE_CANNOT.md`. Its Lean counterpart is
//! `formal/elementary-holonics/ElementaryHolonics/Foundation/ReceiverRelease.lean`
//! (namespace `Soma.Holonics.Foundation.ReceiverRelease`), and the correspondence is the
//! deliverable:
//!
//! | Lean | Rust |
//! |---|---|
//! | `width` | [`width`] and [`ReceiverWidth`] |
//! | `width_nonneg` | [`ReceiverWidth::diameter`] is a maximum of absolute separations |
//! | `abs_sub_le_width` | [`ReceiverWidth::attaining`], the pair that attains it |
//! | `width_le_of_bounds` | [`ExactZonotope::supremum_diameter`], the enclosure route |
//! | `width_mono` | `the_width_is_monotone_under_fibre_inclusion` |
//! | `width_eq_zero_iff` | [`ReceiverWidth::is_zero`] |
//! | `releasable_at_every_tolerance_iff_width_zero` | `width_zero_releases_at_every_tolerance` |
//! | `NonExpansive`, `width_nonExpansive_factor` | [`FactorMap`], [`FactoredReading::verify_non_expansive`] and `a_non_expansive_coarser_receiver_has_no_larger_width` |
//! | `expansive_factor_increases_width` | `an_expansive_factor_map_widens_the_reading` |
//! | `ReleaseReturn` | [`ReleaseReturn`] |
//! | `ReleaseLaw`, `ReleaseLaw.sound`, `ReleaseLaw.widenSound` | [`DecisionLaw`] and [`release`], which refuses a release outside tolerance by name |
//! | `every_lawful_return_other_than_hold_ask_or_no_continuation_is_inside_its_tolerance` | [`release`]'s `Released`, `Widen` and `ReleaseCoarser` arms, and [`LawfulOptions::assemble`]'s tolerance check |
//! | `coarser_receiver_factors`, `releaseCoarser` | [`CoarseningTower`], [`release_coarser`] and [`CoarserRelease`], which carries the tolerance it was searched under |
//! | `Releasable` | [`ReceiverWidth::releasable_at`] |
//! | `no_default_among_the_lawful_returns` | `two_lawful_laws_return_different_arms` |
//! | `future_stable_event_with_unstable_timing` | `an_event_is_future_stable_while_its_timing_is_not` |
//! | `timingInsufficiency` | `the_coarse_event_reading_does_not_determine_the_timing` |
//!
//! Item **T5** of `docs/plans/THE_TUBE_CARRIES_RELEASE_THROUGH_NECKS_FOLDS_AND_JUNCTIONS.md` adds
//! the horizon's second coordinate. The same Lean owner carries it, and the tube-side consumer is
//! `crates/holonic-engine/src/continuing_tube.rs`.
//!
//! | Lean | Rust |
//! |---|---|
//! | `Horizon`, `Horizon.longitudinalOnly`, `Horizon.Within` | [`Horizon`], [`Horizon::longitudinal_only`], [`Horizon::contains`] |
//! | `horizonWithin_is_not_total` | `the_horizon_has_two_coordinates_that_are_not_one_scale`; [`Horizon`] derives no `Ord` |
//! | `ChainDistanceAtMost`, `chainDistance_symm`, `chainDistance_trans` | `continuing_tube::index_distance` and `continuing_tube::IndexReading` |
//! | `Comparable`, `chainDistance_orderDual` | `continuing_tube::IndexDirection`, which names the direction the same distance is walked in |
//! | `TwoAxisReach`, `twoAxisWidth` | `continuing_tube::{HorizonReach, two_axis_width}` |
//! | `twoAxisWidth_mono`, `twoAxisWidth_mono_longitudinal`, `twoAxisWidth_mono_index` | `the_two_axis_width_is_monotone_in_each_coordinate` |
//! | `twoAxisWidth_at_index_zero_is_the_longitudinal_width`, `longitudinal_case_is_the_existing_width_law` | `the_longitudinal_only_case_is_the_existing_width` |
//! | `coarseReach`, `coarse_width_eq_zero`, `fineFibre` | `continuing_tube::{IndexDirection, Plurality}` |
//! | `looking_toward_the_coarse_is_determined_and_toward_the_fine_is_plural` | `the_reach_is_a_face_toward_the_coarse_and_a_fibre_toward_the_fine` |
//! | `width` over already-read faces | [`width_over_readings`], which [`width_enumerated`] now is |
//!
//! # The object
//!
//! [definition] For a **compatible family** — the preimage/observation fibre of
//! [`crate::receiver_atlas::LocalChart::preimage_fibre`], carried here either enumerated
//! ([`CompatibleFamily::Finite`]) or enclosed ([`CompatibleFamily::Enclosed`]) — an exact `h`-step
//! map `Φ_h` and a receiver reading `R`, the **width** is
//!
//! ```text
//! w_R(h) = diam { R(Φ_h(x, u)) : x compatible, u admitted }
//! ```
//!
//! and a face is **released** when that width falls inside the receiver's *declared* tolerance.
//!
//! # Why an enclosure is exact here
//!
//! [implemented-exact] The first real dynamics is [`crate::causal_chord::Linearization`]'s
//! `x_{t+1} = A x_t + B u_t` over `Q`. The image of a box under an exact linear map is **not** a
//! box, but it *is* an exact zonotope: `A·(c + G e) = A c + (A G) e`. [`ExactZonotope`] carries
//! that centre and those generators exactly, [`horizon_image`] pushes a box of compatible states
//! and a box of admitted inputs through `h` steps, and
//! [`ExactZonotope::supremum_diameter`] is the sup-norm diameter `2·max_i Σ_j |G_ij|` — exact,
//! and linear in the generator count.
//!
//! [established-bounded] **A finding, stated as a refusal rather than hidden.** The *squared
//! Euclidean* diameter of a zonotope is attained at a vertex of the generator cube, so computing
//! it exactly would enumerate `2^k` sign patterns. This module therefore declares
//! [`DiameterNorm::Supremum`] as the exact norm on an enclosure and refuses
//! [`DiameterNorm::SquaredEuclidean`] on one by name
//! ([`WidthRefusal::NormNotExactOnEnclosure`]) rather than enumerating a declared-size family.
//! On an enumerated family both norms are exact and both are computed.
//!
//! # Release is receiver-relative, and this module builds no global gate
//!
//! [project-postulate] AGENTS.md: *"A plural fibre does not impose a universal certainty gate on
//! generation."* The Lean theorem `release_is_receiver_relative_not_a_global_gate` is that clause
//! proved, and this module is built to match it: [`release`] takes the caller's [`DecisionLaw`]
//! and enforces exactly **one** thing — that a law returning [`ReleaseReturn::Released`] has the
//! width inside the tolerance it declared. It supplies no default among `Hold`, `Widen`, `Ask`,
//! `ReleaseCoarser` and `NoContinuationBridges`, and it exposes no predicate on a fibre that any
//! generator is obliged to consult.
//!
//! # No floats
//!
//! [implemented-exact] Every centre, generator, half-width, separation, diameter and tolerance is
//! an exact `Rat` or `BigInt`. No `f32`/`f64` appears anywhere in this module.

use std::collections::BTreeMap;
use std::fmt::{self, Debug};

use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::causal_chord::Linearization;
use crate::exact_linear::{ExactLinearError, ExactRatMatrix};

/// Serialized schema name for a returned width.
pub const RECEIVER_WIDTH_SCHEMA: &str = "holonics.receiver-width.v1";

/// The ceiling on the number of uncertainty generators an enclosure may carry.
///
/// [definition] Every generator is one column of exact rationals of the declared dimension, and
/// [`horizon_image`] multiplies the admitted-input generator count by the declared horizon. The
/// ceiling is checked with checked arithmetic **before** any allocation, so a hostile horizon
/// declaration is a typed refusal and never a memory request.
pub const GENERATOR_CEILING: usize = 4096;

/// The ceiling on a declared horizon.
///
/// [definition] `horizon_image` runs one exact matrix multiplication per step, so the *step count*
/// is itself work sized by a caller declaration. Bounding the generator product is not enough: an
/// admitted-input box with no width contributes no generator at all, so a hostile horizon would
/// pass the generator ceiling and still loop. This ceiling is checked first.
pub const HORIZON_CEILING: usize = 4096;

/// The ceiling on the number of members an enumerated compatible family may declare.
///
/// [definition] A width over an enumerated family reads every unordered pair, so the work is
/// `n(n−1)/2`. The ceiling bounds `n`, and the pair count is formed with checked arithmetic.
pub const FAMILY_CEILING: usize = 4096;

/// The ceiling on the carrier extent a declared linearization may present to [`horizon_image`].
///
/// [definition] [`HORIZON_CEILING`] bounds the *number* of exact matrix multiplications, but each
/// one is `extent³` exact rational products, and the extent comes from a caller-declared matrix.
/// A horizon inside its ceiling therefore still admits unbounded work unless the extent is bounded
/// too. This ceiling is checked first, before any matrix is formed.
pub const EXTENT_CEILING: usize = 256;

/// The ceiling on the **product** `horizon · extent³` — the exact rational multiplications
/// [`horizon_image`] will actually perform.
///
/// [definition] The two axis ceilings above bound each declaration separately; this bounds the
/// work, which is what a hostile declaration actually buys. The product is formed with checked
/// arithmetic, so a declaration whose product overflows `usize` is refused rather than wrapping.
pub const MULTIPLY_WORK_CEILING: usize = 1 << 24;

/// The ceiling on the number of steps a declared coarsening tower may carry to one search.
///
/// [definition] [`release_coarser`] checks the factoring of every step over every unordered pair
/// of the fibre, so the work is `steps · n(n−1)/2` with `n` bounded by [`FAMILY_CEILING`]. This
/// ceiling bounds the step count before the first step runs.
pub const TOWER_STEP_CEILING: usize = 256;

/// The ceiling on the number of candidate observations one [`narrowing_observation`] call may
/// declare.
///
/// [definition] Every candidate partitions the fibre and re-reads the target width inside each
/// level set, so the work is linear in the candidate count and quadratic in the fibre. This
/// ceiling bounds the candidate count before the first candidate is read.
pub const CANDIDATE_CEILING: usize = 1024;

// -------------------------------------------------------------------------------------------
// R6 (a) — the exact enclosure
// -------------------------------------------------------------------------------------------

/// Where one uncertainty generator came from. A [`ProbeDirection`] names this, so `Ask` asks for a
/// *named* observation and not for "more data".
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(tag = "source", rename_all = "kebab-case")]
pub enum GeneratorSource {
    /// A coordinate of the compatible-state fibre.
    CompatibleState {
        /// Which state coordinate is unresolved.
        coordinate: usize,
    },
    /// A port of the admitted input at one step of the horizon.
    AdmittedInput {
        /// Which step of the horizon.
        step: usize,
        /// Which input port.
        port: usize,
    },
}

impl fmt::Display for GeneratorSource {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::CompatibleState { coordinate } => write!(f, "compatible-state@{coordinate}"),
            Self::AdmittedInput { step, port } => write!(f, "admitted-input@step{step}/port{port}"),
        }
    }
}

/// One generator of an exact zonotope: a column of exact rationals with the source it came from.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Generator {
    /// Where the unresolved direction came from.
    pub source: GeneratorSource,
    /// The column itself, of the zonotope's dimension.
    pub column: Vec<Rat>,
}

/// **An exact zonotope** `{ c + G e : e ∈ [−1, 1]^k }` over `Q`.
///
/// This is the exact enclosure of a compatible family. A box is the special case where `G` is
/// diagonal, and the image of a zonotope under an exact linear map is again a zonotope — which is
/// why an `h`-step exact linear map keeps the enclosure exact rather than widening it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "ExactZonotopeWire")]
pub struct ExactZonotope {
    dimension: usize,
    center: Vec<Rat>,
    generators: Vec<Generator>,
}

/// The wire an [`ExactZonotope`] deserializes from. It carries no invariant, and
/// `TryFrom` routes every decoded value back through [`ExactZonotope::declared`], so a serialized
/// enclosure cannot enter the module with a generator of the wrong length or a generator count
/// past the ceiling.
#[derive(Deserialize)]
struct ExactZonotopeWire {
    center: Vec<Rat>,
    generators: Vec<Generator>,
}

impl TryFrom<ExactZonotopeWire> for ExactZonotope {
    type Error = WidthRefusal;

    fn try_from(wire: ExactZonotopeWire) -> Result<Self, Self::Error> {
        Self::declared(wire.center, wire.generators)
    }
}

impl ExactZonotope {
    /// The box hull of a declared centre and declared nonnegative half-widths, one generator per
    /// coordinate whose half-width is nonzero.
    ///
    /// A negative half-width is refused by name: an enclosure with a negative extent is not an
    /// enclosure.
    pub fn box_hull(center: Vec<Rat>, half_widths: &[Rat]) -> Result<Self, WidthRefusal> {
        if center.len() != half_widths.len() {
            return Err(WidthRefusal::DimensionMismatch {
                declared: center.len(),
                found: half_widths.len(),
            });
        }
        let dimension = center.len();
        if dimension == 0 {
            return Err(WidthRefusal::EmptyDimension);
        }
        let live = half_widths.iter().filter(|w| !w.is_zero()).count();
        if live > GENERATOR_CEILING {
            return Err(WidthRefusal::GeneratorCeiling {
                requested: live,
                ceiling: GENERATOR_CEILING,
            });
        }
        let mut generators = Vec::with_capacity(live);
        for (coordinate, half_width) in half_widths.iter().enumerate() {
            if half_width.is_negative() {
                return Err(WidthRefusal::NegativeHalfWidth { coordinate });
            }
            if half_width.is_zero() {
                continue;
            }
            let mut column = vec![Rat::zero(); dimension];
            column[coordinate] = half_width.clone();
            generators.push(Generator {
                source: GeneratorSource::CompatibleState { coordinate },
                column,
            });
        }
        Ok(Self {
            dimension,
            center,
            generators,
        })
    }

    /// A zonotope from a declared centre and declared generators, each checked against the
    /// dimension and the ceiling.
    pub fn declared(center: Vec<Rat>, generators: Vec<Generator>) -> Result<Self, WidthRefusal> {
        let dimension = center.len();
        if dimension == 0 {
            return Err(WidthRefusal::EmptyDimension);
        }
        if generators.len() > GENERATOR_CEILING {
            return Err(WidthRefusal::GeneratorCeiling {
                requested: generators.len(),
                ceiling: GENERATOR_CEILING,
            });
        }
        for generator in &generators {
            if generator.column.len() != dimension {
                return Err(WidthRefusal::DimensionMismatch {
                    declared: dimension,
                    found: generator.column.len(),
                });
            }
        }
        Ok(Self {
            dimension,
            center,
            generators,
        })
    }

    /// The exact dimension of the space this enclosure lives in.
    pub fn dimension(&self) -> usize {
        self.dimension
    }

    /// The exact centre.
    pub fn center(&self) -> &[Rat] {
        &self.center
    }

    /// The exact generators, in declaration order.
    pub fn generators(&self) -> &[Generator] {
        &self.generators
    }

    /// The image under an exact linear map. Exact: `M·(c + G e) = M c + (M G) e`.
    pub fn mapped(&self, map: &ExactRatMatrix) -> Result<Self, WidthRefusal> {
        if map.columns() != self.dimension {
            return Err(WidthRefusal::DimensionMismatch {
                declared: self.dimension,
                found: map.columns(),
            });
        }
        let center = map.apply(&self.center)?;
        let mut generators = Vec::with_capacity(self.generators.len());
        for generator in &self.generators {
            generators.push(Generator {
                source: generator.source,
                column: map.apply(&generator.column)?,
            });
        }
        Ok(Self {
            dimension: map.rows(),
            center,
            generators,
        })
    }

    /// The Minkowski sum of two enclosures of the same dimension: centres add, generators join.
    pub fn summed(&self, other: &Self) -> Result<Self, WidthRefusal> {
        if self.dimension != other.dimension {
            return Err(WidthRefusal::DimensionMismatch {
                declared: self.dimension,
                found: other.dimension,
            });
        }
        let total = self
            .generators
            .len()
            .checked_add(other.generators.len())
            .ok_or(WidthRefusal::GeneratorCountOverflows {
                states: self.generators.len(),
                inputs: other.generators.len(),
                horizon: 1,
            })?;
        if total > GENERATOR_CEILING {
            return Err(WidthRefusal::GeneratorCeiling {
                requested: total,
                ceiling: GENERATOR_CEILING,
            });
        }
        let center = self
            .center
            .iter()
            .zip(&other.center)
            .map(|(a, b)| a + b)
            .collect();
        let mut generators = Vec::with_capacity(total);
        generators.extend(self.generators.iter().cloned());
        generators.extend(other.generators.iter().cloned());
        Ok(Self {
            dimension: self.dimension,
            center,
            generators,
        })
    }

    /// The exact half-extent of the enclosure along one coordinate: `Σ_j |G_ij|`.
    pub fn coordinate_half_extent(&self, coordinate: usize) -> Result<Rat, WidthRefusal> {
        if coordinate >= self.dimension {
            return Err(WidthRefusal::DimensionMismatch {
                declared: self.dimension,
                found: coordinate,
            });
        }
        Ok(self
            .generators
            .iter()
            .fold(Rat::zero(), |sum, generator| {
                sum + generator.column[coordinate].abs()
            }))
    }

    /// **The exact sup-norm diameter** `2·max_i Σ_j |G_ij|`, with the coordinate attaining it.
    ///
    /// Lean counterpart: `width_le_of_bounds` — the enclosure route to a width, which pins the
    /// diameter without enumerating the family.
    pub fn supremum_diameter(&self) -> Result<(Rat, usize), WidthRefusal> {
        let mut best = Rat::zero();
        let mut at = 0usize;
        for coordinate in 0..self.dimension {
            let extent = self.coordinate_half_extent(coordinate)?;
            if extent > best {
                best = extent;
                at = coordinate;
            }
        }
        Ok((best * Rat::from_integer(BigInt::from(2)), at))
    }

    /// The same enclosure with one generator dropped: what observing that direction exactly would
    /// leave. Used by [`narrowing_probe`].
    pub fn without_generator(&self, index: usize) -> Result<Self, WidthRefusal> {
        if index >= self.generators.len() {
            return Err(WidthRefusal::GeneratorAbsent {
                index,
                carried: self.generators.len(),
            });
        }
        let mut generators = self.generators.clone();
        generators.remove(index);
        Ok(Self {
            dimension: self.dimension,
            center: self.center.clone(),
            generators,
        })
    }
}

// -------------------------------------------------------------------------------------------
// R6 (b) — the exact h-step map
// -------------------------------------------------------------------------------------------

/// **The exact `h`-step image of a compatible enclosure under a declared linearization.**
///
/// `Φ_h(x, u_0 … u_{h−1}) = A^h x + Σ_{k<h} A^{h−1−k} B u_k`, with a *fresh* admitted input drawn
/// at every step. The returned enclosure is exact: every centre and every generator is an exact
/// rational matrix–vector product, and nothing is widened.
///
/// # Declared-size guard
///
/// [implemented-exact] The generator count of the return is
/// `states.generators + horizon · inputs.generators`. That product and that sum are formed with
/// checked arithmetic and compared against [`GENERATOR_CEILING`] **before** the first allocation,
/// so a hostile `horizon` is refused by name and never sizes a `Vec`.
pub fn horizon_image(
    linearization: &Linearization,
    states: &ExactZonotope,
    inputs: &ExactZonotope,
    horizon: usize,
) -> Result<ExactZonotope, WidthRefusal> {
    let extent = linearization.extent();
    if extent > EXTENT_CEILING {
        return Err(WidthRefusal::ExtentCeiling {
            requested: extent,
            ceiling: EXTENT_CEILING,
        });
    }
    if states.dimension() != extent {
        return Err(WidthRefusal::DimensionMismatch {
            declared: extent,
            found: states.dimension(),
        });
    }
    if inputs.dimension() != linearization.source_count() {
        return Err(WidthRefusal::DimensionMismatch {
            declared: linearization.source_count(),
            found: inputs.dimension(),
        });
    }
    if horizon > HORIZON_CEILING {
        return Err(WidthRefusal::HorizonCeiling {
            requested: horizon,
            ceiling: HORIZON_CEILING,
        });
    }
    let input_total = horizon
        .checked_mul(inputs.generators().len())
        .ok_or(WidthRefusal::GeneratorCountOverflows {
            states: states.generators().len(),
            inputs: inputs.generators().len(),
            horizon,
        })?;
    let total = states
        .generators()
        .len()
        .checked_add(input_total)
        .ok_or(WidthRefusal::GeneratorCountOverflows {
            states: states.generators().len(),
            inputs: inputs.generators().len(),
            horizon,
        })?;
    if total > GENERATOR_CEILING {
        return Err(WidthRefusal::GeneratorCeiling {
            requested: total,
            ceiling: GENERATOR_CEILING,
        });
    }
    // The work itself: one `extent × extent` exact multiplication per step, each `extent³`
    // rational products. Formed with checked arithmetic and compared before the loop runs.
    let multiply_work = extent
        .checked_mul(extent)
        .and_then(|square| square.checked_mul(extent))
        .and_then(|cube| cube.checked_mul(horizon.max(1)))
        .ok_or(WidthRefusal::MultiplyWorkCeiling {
            extent,
            horizon,
            ceiling: MULTIPLY_WORK_CEILING,
        })?;
    if multiply_work > MULTIPLY_WORK_CEILING {
        return Err(WidthRefusal::MultiplyWorkCeiling {
            extent,
            horizon,
            ceiling: MULTIPLY_WORK_CEILING,
        });
    }

    // `A^h` and the `h` transported excitation maps, built by repeated exact multiplication.
    let mut power = ExactRatMatrix::identity(extent)?;
    let mut transported: Vec<ExactRatMatrix> = Vec::with_capacity(horizon);
    for _ in 0..horizon {
        transported.push(power.multiply(&linearization.excitation)?);
        power = linearization.state.multiply(&power)?;
    }

    let mut image = states.mapped(&power)?;
    // Step `k` of the horizon contributes `A^{h−1−k} B u_k`; `transported[j]` is `A^j B`, so the
    // step whose transport exponent is `j` is `k = h − 1 − j`.
    for (exponent, map) in transported.iter().enumerate() {
        let step = horizon - 1 - exponent;
        let block = inputs.mapped(map)?;
        let relabelled = ExactZonotope {
            dimension: block.dimension,
            center: block.center,
            generators: block
                .generators
                .into_iter()
                .enumerate()
                .map(|(port, generator)| Generator {
                    source: GeneratorSource::AdmittedInput { step, port },
                    column: generator.column,
                })
                .collect(),
        };
        image = image.summed(&relabelled)?;
    }
    Ok(image)
}

/// **One exact trajectory**: the `h`-step advance of a single compatible state under a declared
/// input word. The word's length is the horizon; a shorter word is refused by name.
pub fn advance(
    linearization: &Linearization,
    state: &[Rat],
    inputs: &[Vec<Rat>],
) -> Result<Vec<Rat>, WidthRefusal> {
    if state.len() != linearization.extent() {
        return Err(WidthRefusal::DimensionMismatch {
            declared: linearization.extent(),
            found: state.len(),
        });
    }
    let mut current = state.to_vec();
    for step in inputs {
        if step.len() != linearization.source_count() {
            return Err(WidthRefusal::DimensionMismatch {
                declared: linearization.source_count(),
                found: step.len(),
            });
        }
        let free = linearization.state.apply(&current)?;
        let driven = linearization.excitation.apply(step)?;
        current = free.iter().zip(&driven).map(|(a, b)| a + b).collect();
    }
    Ok(current)
}

// -------------------------------------------------------------------------------------------
// R6 (c) — the reading and its exact faces
// -------------------------------------------------------------------------------------------

/// An exact face returned by a receiver reading. Three arms, each exact; no float appears.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "face", rename_all = "kebab-case")]
pub enum ExactFace {
    /// A yes/no reading, separated by `1` when the two disagree.
    Flag(bool),
    /// An exact integer reading — a step count, a Betti number, a multiplicity.
    Count(BigInt),
    /// An exact rational vector reading.
    Vector(Vec<Rat>),
}

impl ExactFace {
    /// The name of this arm, for the incomparability refusal.
    pub fn arm(&self) -> &'static str {
        match self {
            Self::Flag(_) => "flag",
            Self::Count(_) => "count",
            Self::Vector(_) => "vector",
        }
    }

    /// **The exact separation of two faces in a declared norm.** Two faces of different arms are
    /// refused by name rather than coerced; two vectors of different lengths likewise.
    pub fn separation(&self, other: &Self, norm: DiameterNorm) -> Result<Rat, WidthRefusal> {
        match (self, other) {
            (Self::Flag(left), Self::Flag(right)) => Ok(if left == right {
                Rat::zero()
            } else {
                Rat::from_integer(BigInt::from(1))
            }),
            (Self::Count(left), Self::Count(right)) => {
                let difference = Rat::from_integer((left - right).abs());
                Ok(match norm {
                    DiameterNorm::Supremum => difference,
                    DiameterNorm::SquaredEuclidean => &difference * &difference,
                })
            }
            (Self::Vector(left), Self::Vector(right)) => {
                if left.len() != right.len() {
                    return Err(WidthRefusal::VectorFacesDiffer {
                        left: left.len(),
                        right: right.len(),
                    });
                }
                Ok(match norm {
                    DiameterNorm::Supremum => left
                        .iter()
                        .zip(right)
                        .map(|(a, b)| (a - b).abs())
                        .fold(Rat::zero(), |best, value| if value > best { value } else { best }),
                    DiameterNorm::SquaredEuclidean => {
                        left.iter().zip(right).fold(Rat::zero(), |sum, (a, b)| {
                            let difference = a - b;
                            sum + &difference * &difference
                        })
                    }
                })
            }
            _ => Err(WidthRefusal::FacesIncomparable {
                left: self.arm(),
                right: other.arm(),
            }),
        }
    }
}

/// The declared exact norm the diameter is taken in.
///
/// [established-bounded] `SquaredEuclidean` is exact on an **enumerated** family and is refused on
/// an enclosure: the Euclidean diameter of a zonotope is attained at a vertex of the generator
/// cube, so an exact computation would enumerate `2^k` sign patterns. The refusal is
/// [`WidthRefusal::NormNotExactOnEnclosure`] and names the norm.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum DiameterNorm {
    /// The sup-norm. Exact on both an enumerated family and an enclosure.
    Supremum,
    /// The squared Euclidean norm. Exact on an enumerated family only.
    SquaredEuclidean,
}

impl DiameterNorm {
    /// The name, for a refusal message.
    pub fn name(self) -> &'static str {
        match self {
            Self::Supremum => "supremum",
            Self::SquaredEuclidean => "squared-euclidean",
        }
    }
}

/// A declared exact reading of one compatible state. Implementors are the receivers of the plan;
/// the reading is `R ∘ Φ_h` already composed, exactly as the Lean owner says.
pub trait Reading {
    /// The receiver's declared name. It appears in every refusal and in every returned width.
    fn name(&self) -> &str;

    /// The exact face this receiver reads off one compatible state.
    fn read(&self, state: &[Rat]) -> Result<ExactFace, WidthRefusal>;
}

/// An exact **linear** reading `R x`, the one reading that is exact on an enclosure as well as on
/// an enumerated family.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LinearReading {
    /// The receiver's declared name.
    pub receiver: String,
    /// The exact matrix `R`.
    pub matrix: ExactRatMatrix,
}

impl Reading for LinearReading {
    fn name(&self) -> &str {
        &self.receiver
    }

    fn read(&self, state: &[Rat]) -> Result<ExactFace, WidthRefusal> {
        Ok(ExactFace::Vector(self.matrix.apply(state)?))
    }
}

/// How a compatible family is carried. Private: the only way to build a [`CompatibleFamily`] is
/// through [`CompatibleFamily::enumerated`] or [`CompatibleFamily::enclosed`], so the declared-size
/// ceiling and the common-dimension check cannot be bypassed by a struct literal.
#[derive(Clone, Debug, PartialEq, Eq)]
enum FamilyCarrier {
    /// The fibre enumerated: finitely many compatible states, each already advanced to the
    /// horizon or read by a reading that advances them.
    Finite(Vec<Vec<Rat>>),
    /// The fibre enclosed: an exact zonotope hull of the compatible states at the horizon.
    Enclosed(ExactZonotope),
}

/// The compatible family a width is taken over: the preimage/observation fibre, enumerated or
/// enclosed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CompatibleFamily {
    lineage: String,
    carrier: FamilyCarrier,
}

impl CompatibleFamily {
    /// What this fibre is the fibre of.
    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// The enclosing hull, when the family is enclosed.
    pub fn hull(&self) -> Option<&ExactZonotope> {
        match &self.carrier {
            FamilyCarrier::Enclosed(hull) => Some(hull),
            FamilyCarrier::Finite(_) => None,
        }
    }

    /// An enumerated family, with its declared size checked against [`FAMILY_CEILING`] and its
    /// members checked against one another for a common dimension.
    pub fn enumerated(
        lineage: impl Into<String>,
        members: Vec<Vec<Rat>>,
    ) -> Result<Self, WidthRefusal> {
        if members.is_empty() {
            return Err(WidthRefusal::EmptyFamily);
        }
        if members.len() > FAMILY_CEILING {
            return Err(WidthRefusal::FamilyCeiling {
                declared: members.len(),
                ceiling: FAMILY_CEILING,
            });
        }
        // The pair count is the work this family asks for; form it with checked arithmetic.
        let count = members.len();
        count
            .checked_mul(count.saturating_sub(1))
            .ok_or(WidthRefusal::PairCountOverflows { members: count })?;
        let dimension = members[0].len();
        if dimension == 0 {
            return Err(WidthRefusal::EmptyDimension);
        }
        for member in &members {
            if member.len() != dimension {
                return Err(WidthRefusal::DimensionMismatch {
                    declared: dimension,
                    found: member.len(),
                });
            }
        }
        Ok(Self {
            lineage: lineage.into(),
            carrier: FamilyCarrier::Finite(members),
        })
    }

    /// An enclosed family.
    pub fn enclosed(lineage: impl Into<String>, hull: ExactZonotope) -> Self {
        Self {
            lineage: lineage.into(),
            carrier: FamilyCarrier::Enclosed(hull),
        }
    }

    /// The enumerated members, when the family is enumerated.
    pub fn members(&self) -> Option<&[Vec<Rat>]> {
        match &self.carrier {
            FamilyCarrier::Finite(members) => Some(members),
            FamilyCarrier::Enclosed(_) => None,
        }
    }

    /// Whether every member of this family is a member of the other. Used by the monotonicity
    /// law; only defined between two enumerated families.
    pub fn is_subfamily_of(&self, other: &Self) -> Option<bool> {
        match (self.members(), other.members()) {
            (Some(mine), Some(theirs)) => {
                Some(mine.iter().all(|member| theirs.contains(member)))
            }
            _ => None,
        }
    }
}

/// **The width of a receiver reading over a compatible family.**
///
/// Lean counterpart: `Foundation/ReceiverRelease.lean::width`.
///
/// [implemented-exact] Every field is private. The only constructors are [`width_enumerated`] and
/// [`width_enclosed`], and the only wire route is the validating [`TryFrom`] below, reached
/// through `#[serde(try_from = ...)]`: a remounted reading whose schema, diameter sign or
/// attaining witness is incoherent with its own `read` count is refused rather than carried, so
/// a forged width cannot be handed to [`LawfulOptions::assemble`].
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(try_from = "ReceiverWidthWire")]
pub struct ReceiverWidth {
    schema: String,
    receiver: String,
    lineage: String,
    norm: DiameterNorm,
    diameter: Rat,
    attaining: WidthWitness,
    read: usize,
}

/// The wire form of a [`ReceiverWidth`]. Deserializing a `ReceiverWidth` goes through this and
/// the structural re-check in `TryFrom`; there is no unchecked route.
#[derive(Clone, Debug, Deserialize)]
struct ReceiverWidthWire {
    schema: String,
    receiver: String,
    lineage: String,
    norm: DiameterNorm,
    diameter: Rat,
    attaining: WidthWitness,
    read: usize,
}

impl TryFrom<ReceiverWidthWire> for ReceiverWidth {
    type Error = WidthRefusal;

    fn try_from(wire: ReceiverWidthWire) -> Result<Self, Self::Error> {
        if wire.schema != RECEIVER_WIDTH_SCHEMA {
            return Err(WidthRefusal::WidthSchemaMismatch {
                declared: wire.schema,
                expected: RECEIVER_WIDTH_SCHEMA,
            });
        }
        if wire.diameter.is_negative() {
            return Err(WidthRefusal::NegativeWidth {
                declared: wire.diameter.to_string(),
            });
        }
        match &wire.attaining {
            WidthWitness::Pair { left, right } => {
                if left >= right || *right >= wire.read {
                    return Err(WidthRefusal::WitnessOutsideReading {
                        read: wire.read,
                        witness: format!("{:?}", wire.attaining),
                    });
                }
            }
            WidthWitness::Coordinate { .. } => {}
            WidthWitness::Point => {
                if !wire.diameter.is_zero() {
                    return Err(WidthRefusal::WitnessOutsideReading {
                        read: wire.read,
                        witness: "point witness with a nonzero diameter".to_owned(),
                    });
                }
            }
        }
        Ok(Self {
            schema: wire.schema,
            receiver: wire.receiver,
            lineage: wire.lineage,
            norm: wire.norm,
            diameter: wire.diameter,
            attaining: wire.attaining,
            read: wire.read,
        })
    }
}

impl ReceiverWidth {
    /// The serialized schema.
    pub fn schema(&self) -> &str {
        &self.schema
    }

    /// The receiver whose reading this is.
    pub fn receiver(&self) -> &str {
        &self.receiver
    }

    /// What the fibre is the fibre of.
    pub fn lineage(&self) -> &str {
        &self.lineage
    }

    /// The declared norm.
    pub fn norm(&self) -> DiameterNorm {
        self.norm
    }

    /// The exact diameter.
    pub fn diameter(&self) -> &Rat {
        &self.diameter
    }

    /// How the diameter was reached: the pair that attains it, or the coordinate of the enclosure.
    pub fn attaining(&self) -> &WidthWitness {
        &self.attaining
    }

    /// How many members were read, or how many generators the enclosure carried.
    pub fn read(&self) -> usize {
        self.read
    }

    /// **Width zero is exactly constancy on the fibre**, and exactly releasability at every
    /// tolerance.
    ///
    /// Lean counterpart: `width_eq_zero_iff` and
    /// `releasable_at_every_tolerance_iff_width_zero`.
    pub fn is_zero(&self) -> bool {
        self.diameter.is_zero()
    }

    /// Whether this width falls inside a declared tolerance.
    ///
    /// Lean counterpart: `Releasable`.
    pub fn releasable_at(&self, tolerance: &Rat) -> bool {
        &self.diameter <= tolerance
    }
}

/// How a width was attained: the content of the diameter, not a summary of it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "witness", rename_all = "kebab-case")]
pub enum WidthWitness {
    /// The two enumerated members whose readings are furthest apart.
    Pair {
        /// Index of the first member.
        left: usize,
        /// Index of the second member.
        right: usize,
    },
    /// The coordinate of the image enclosure whose extent is widest.
    Coordinate {
        /// Which coordinate.
        coordinate: usize,
    },
    /// The family is a single member, or the enclosure carries no generator: the width is zero and
    /// nothing attains it but the point itself.
    Point,
}

/// **The width of a declared reading over an enumerated compatible family.**
///
/// Every unordered pair is read; the work is `n(n−1)/2` with `n` bounded by [`FAMILY_CEILING`] at
/// the family's construction.
pub fn width_enumerated(
    reading: &dyn Reading,
    family: &CompatibleFamily,
    norm: DiameterNorm,
) -> Result<ReceiverWidth, WidthRefusal> {
    let Some(members) = family.members() else {
        return Err(WidthRefusal::DeclaredReadingNeedsEnumeratedFamily {
            receiver: reading.name().to_owned(),
        });
    };
    let faces = members
        .iter()
        .map(|member| reading.read(member))
        .collect::<Result<Vec<_>, _>>()?;
    width_over_readings(reading.name(), family.lineage(), &faces, norm)
}

/// **The width of an exact linear reading over an enclosed compatible family.**
///
/// Exact and linear in the generator count: the image of the hull is an exact zonotope and its
/// sup-norm diameter is `2·max_i Σ_j |G_ij|`. The squared-Euclidean norm is refused on an
/// enclosure by name.
pub fn width_enclosed(
    reading: &LinearReading,
    family: &CompatibleFamily,
    norm: DiameterNorm,
) -> Result<ReceiverWidth, WidthRefusal> {
    let Some(hull) = family.hull() else {
        return Err(WidthRefusal::EnclosedReadingNeedsEnclosure {
            receiver: reading.receiver.clone(),
        });
    };
    if norm != DiameterNorm::Supremum {
        return Err(WidthRefusal::NormNotExactOnEnclosure { norm: norm.name() });
    }
    let image = hull.mapped(&reading.matrix)?;
    let (diameter, coordinate) = image.supremum_diameter()?;
    let attaining = if image.generators().is_empty() {
        WidthWitness::Point
    } else {
        WidthWitness::Coordinate { coordinate }
    };
    Ok(ReceiverWidth {
        schema: RECEIVER_WIDTH_SCHEMA.to_owned(),
        receiver: reading.receiver.clone(),
        lineage: family.lineage().to_owned(),
        norm,
        diameter,
        attaining,
        read: image.generators().len(),
    })
}

/// The width, dispatched on how the family is carried. A declared non-linear reading over an
/// enclosure is refused by name rather than sampled.
pub fn width(
    reading: &dyn Reading,
    family: &CompatibleFamily,
    norm: DiameterNorm,
) -> Result<ReceiverWidth, WidthRefusal> {
    if family.members().is_some() {
        width_enumerated(reading, family, norm)
    } else {
        Err(WidthRefusal::DeclaredReadingNeedsEnumeratedFamily {
            receiver: reading.name().to_owned(),
        })
    }
}

// -------------------------------------------------------------------------------------------
// T5 (a) — the horizon has two coordinates
// -------------------------------------------------------------------------------------------

/// The ceiling on the index coordinate of a declared two-axis [`Horizon`].
///
/// [definition] The index coordinate counts steps through a tower's charts. Every step toward a
/// finer chart replaces a face by its **fibre**, so the population a reach carries is multiplied
/// rather than kept, and the coordinate is therefore work a caller declares. It is checked by
/// [`Horizon::declare`] before any reach is walked; the tube-side reach adds its own work ceiling
/// over the product of this coordinate with the chart and face populations.
pub const INDEX_HORIZON_CEILING: usize = 1024;

/// **A horizon with two coordinates: `h` longitudinal steps and `k` steps in the tower's index.**
///
/// [definition] `w_R(h)` — the width this module already owned — measures distance into the
/// horizon along one axis only. The second coordinate is distance in the **index**, in either
/// direction: `k` steps toward the finer charts or `k` steps toward the coarser ones. Brandon's
/// statement, September 18: *zooming from orbit down to an organism is as far into the horizon as
/// looking out to the stars*, and that is the same notion of distance in both directions.
///
/// [proved-derived; formal-checked] Lean counterpart:
/// `Foundation/ReceiverRelease.lean::Horizon`, with `Horizon.Within` the product order,
/// `horizonWithin_refl`/`horizonWithin_trans` its two laws and `horizonWithin_is_not_total` the
/// statement that **the two coordinates are not one scale**: `(2, 0)` and `(0, 2)` are
/// incomparable horizons, so "how far into the horizon" is a pair and not a number, and no
/// lexicographic order is imposed on it here. That is why this type derives no `Ord`.
///
/// [implemented-exact] Both fields are private and the only constructors are [`Self::declare`] and
/// [`Self::longitudinal_only`], which check both ceilings. The `Deserialize` route goes through
/// `#[serde(try_from = ...)]` and re-runs those checks, so a remounted horizon cannot carry a
/// declaration the library would have refused.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(try_from = "HorizonWire")]
pub struct Horizon {
    longitudinal: usize,
    index: usize,
}

/// The wire form of a [`Horizon`]. Deserializing one goes through this and the ceiling checks in
/// `TryFrom`; there is no unchecked route.
#[derive(Clone, Copy, Debug, Deserialize)]
struct HorizonWire {
    longitudinal: usize,
    index: usize,
}

impl TryFrom<HorizonWire> for Horizon {
    type Error = WidthRefusal;

    fn try_from(wire: HorizonWire) -> Result<Self, Self::Error> {
        Self::declare(wire.longitudinal, wire.index)
    }
}

impl Horizon {
    /// Declare a two-axis horizon, checking both coordinates against their ceilings before
    /// anything is sized by them.
    pub fn declare(longitudinal: usize, index: usize) -> Result<Self, WidthRefusal> {
        if longitudinal > HORIZON_CEILING {
            return Err(WidthRefusal::HorizonCeiling {
                requested: longitudinal,
                ceiling: HORIZON_CEILING,
            });
        }
        if index > INDEX_HORIZON_CEILING {
            return Err(WidthRefusal::IndexHorizonCeiling {
                requested: index,
                ceiling: INDEX_HORIZON_CEILING,
            });
        }
        Ok(Self {
            longitudinal,
            index,
        })
    }

    /// The horizon this module's existing width reads at: `h` longitudinal steps and `k = 0`.
    ///
    /// Lean counterpart: `Horizon.longitudinalOnly` and
    /// `twoAxisWidth_at_index_zero_is_the_longitudinal_width`, which is why every theorem already
    /// proved of `width` is the `k = 0` case of the two-axis width and is not restated.
    pub fn longitudinal_only(longitudinal: usize) -> Result<Self, WidthRefusal> {
        Self::declare(longitudinal, 0)
    }

    /// The longitudinal coordinate: steps of `Φ` along the tube.
    pub const fn longitudinal(&self) -> usize {
        self.longitudinal
    }

    /// The index coordinate: steps through the tower's charts, in either direction.
    pub const fn index(&self) -> usize {
        self.index
    }

    /// Whether this is the longitudinal-only horizon the one-axis width reads at.
    pub const fn is_longitudinal_only(&self) -> bool {
        self.index == 0
    }

    /// Whether `inner` lies inside this horizon, in the **product** order: no further along either
    /// axis. This is the order the monotonicity law is stated in, and it is partial.
    ///
    /// Lean counterpart: `Horizon.Within`.
    pub const fn contains(&self, inner: &Self) -> bool {
        inner.longitudinal <= self.longitudinal && inner.index <= self.index
    }

    /// Whether two horizons are comparable at all. `(2, 0)` and `(0, 2)` are not.
    ///
    /// Lean counterpart: `horizonWithin_is_not_total`.
    pub const fn comparable(&self, other: &Self) -> bool {
        self.contains(other) || other.contains(self)
    }
}

/// **The width of an already-read family of exact faces.**
///
/// [definition] This is [`width_enumerated`]'s second half on its own: the diameter of a set of
/// exact faces in a declared norm, with the pair that attains it. It exists because a width is
/// taken over readings that did not come from a `Vec<Rat>` compatible family — the faces of a
/// tube's two-axis horizon are the first consumer — and the diameter law must not be written a
/// second time for them.
///
/// Lean counterpart: `Foundation/ReceiverRelease.lean::width`, with `abs_sub_le_width` the pair
/// that attains it and `width_nonneg` the sign. The declared face count is checked against
/// [`FAMILY_CEILING`] and its pair count formed with checked arithmetic before any pair is read.
pub fn width_over_readings(
    receiver: &str,
    lineage: &str,
    faces: &[ExactFace],
    norm: DiameterNorm,
) -> Result<ReceiverWidth, WidthRefusal> {
    if faces.is_empty() {
        return Err(WidthRefusal::EmptyFamily);
    }
    if faces.len() > FAMILY_CEILING {
        return Err(WidthRefusal::FamilyCeiling {
            declared: faces.len(),
            ceiling: FAMILY_CEILING,
        });
    }
    let count = faces.len();
    count
        .checked_mul(count.saturating_sub(1))
        .ok_or(WidthRefusal::PairCountOverflows { members: count })?;
    let mut diameter = Rat::zero();
    let mut attaining = WidthWitness::Point;
    for left in 0..faces.len() {
        for right in (left + 1)..faces.len() {
            let separation = faces[left].separation(&faces[right], norm)?;
            if separation > diameter {
                diameter = separation;
                attaining = WidthWitness::Pair { left, right };
            }
        }
    }
    Ok(ReceiverWidth {
        schema: RECEIVER_WIDTH_SCHEMA.to_owned(),
        receiver: receiver.to_owned(),
        lineage: lineage.to_owned(),
        norm,
        diameter,
        attaining,
        read: faces.len(),
    })
}

// -------------------------------------------------------------------------------------------
// R6 (d) — `Ask`: the probe that narrows the fibre most, computed
// -------------------------------------------------------------------------------------------

/// The named direction whose exact observation would narrow the width most.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ProbeDirection {
    /// Where the unresolved direction came from.
    pub source: GeneratorSource,
    /// Which generator of the image enclosure it is.
    pub generator: usize,
    /// The exact width that observing it would leave.
    pub width_after: Rat,
    /// The exact reduction it buys.
    pub reduction: Rat,
}

/// The named declared observation whose reading would narrow the width most.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ObservationProbe {
    /// The observation's declared name.
    pub observation: String,
    /// The exact width the worst remaining level set would still carry.
    pub width_after: Rat,
    /// The exact reduction it buys.
    pub reduction: Rat,
}

/// Either kind of answer to `Ask`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "ask", rename_all = "kebab-case")]
pub enum AskProbe {
    /// An unresolved direction of the enclosure.
    Direction(ProbeDirection),
    /// A declared observation over the enumerated fibre.
    Observation(ObservationProbe),
}

impl AskProbe {
    /// The exact width the probe would leave.
    pub fn width_after(&self) -> &Rat {
        match self {
            Self::Direction(probe) => &probe.width_after,
            Self::Observation(probe) => &probe.width_after,
        }
    }

    /// The probe's name, for the law's refusal.
    pub fn name(&self) -> String {
        match self {
            Self::Direction(probe) => probe.source.to_string(),
            Self::Observation(probe) => probe.observation.clone(),
        }
    }
}

/// **The probe direction maximally reducing the width, computed rather than guessed.**
///
/// Observing one generator of the image enclosure exactly removes that generator; the sup-norm
/// diameter of what remains is exact, so the generator to ask for is the one whose removal leaves
/// the smallest diameter. The work is the generator count squared times the dimension, and the
/// generator count is bounded by [`GENERATOR_CEILING`] at the enclosure's construction.
///
/// Returns `None` when the enclosure carries no generator: there is nothing left to ask.
pub fn narrowing_probe(
    reading: &LinearReading,
    hull: &ExactZonotope,
) -> Result<Option<ProbeDirection>, WidthRefusal> {
    let image = hull.mapped(&reading.matrix)?;
    if image.generators().is_empty() {
        return Ok(None);
    }
    let (before, _) = image.supremum_diameter()?;
    let mut best: Option<ProbeDirection> = None;
    for index in 0..image.generators().len() {
        let narrowed = image.without_generator(index)?;
        let (after, _) = narrowed.supremum_diameter()?;
        let candidate = ProbeDirection {
            source: image.generators()[index].source,
            generator: index,
            width_after: after.clone(),
            reduction: &before - &after,
        };
        let better = match &best {
            None => true,
            Some(current) => candidate.width_after < current.width_after,
        };
        if better {
            best = Some(candidate);
        }
    }
    Ok(best)
}

/// **The declared observation maximally reducing the width over an enumerated fibre.**
///
/// Each candidate observation partitions the fibre into the level sets of its own reading; the
/// width that survives is the largest width the target reading still carries inside one level set.
/// The observation to ask for is the candidate minimizing that survivor. Nothing is sampled and no
/// candidate is invented: the candidate family is the caller's declaration.
pub fn narrowing_observation(
    reading: &dyn Reading,
    family: &CompatibleFamily,
    candidates: &[&dyn Reading],
    norm: DiameterNorm,
) -> Result<Option<ObservationProbe>, WidthRefusal> {
    let Some(members) = family.members() else {
        return Err(WidthRefusal::DeclaredReadingNeedsEnumeratedFamily {
            receiver: reading.name().to_owned(),
        });
    };
    if candidates.len() > CANDIDATE_CEILING {
        return Err(WidthRefusal::CandidateCeiling {
            requested: candidates.len(),
            ceiling: CANDIDATE_CEILING,
        });
    }
    let before = width_enumerated(reading, family, norm)?.diameter;
    let mut best: Option<ObservationProbe> = None;
    for candidate in candidates {
        // The level sets of the candidate's own reading, keyed by its serialized exact face so
        // that no ordering on the face type is assumed.
        let mut levels: BTreeMap<String, Vec<Vec<Rat>>> = BTreeMap::new();
        for member in members {
            let face = candidate.read(member)?;
            levels
                .entry(format!("{face:?}"))
                .or_default()
                .push(member.clone());
        }
        let mut survivor = Rat::zero();
        for level in levels.values() {
            let sub = CompatibleFamily::enumerated(
                format!("{}|{}", family.lineage(), candidate.name()),
                level.clone(),
            )?;
            let inner = width_enumerated(reading, &sub, norm)?.diameter;
            if inner > survivor {
                survivor = inner;
            }
        }
        let probe = ObservationProbe {
            observation: candidate.name().to_owned(),
            width_after: survivor.clone(),
            reduction: &before - &survivor,
        };
        let better = match &best {
            None => true,
            Some(current) => probe.width_after < current.width_after,
        };
        if better {
            best = Some(probe);
        }
    }
    Ok(best)
}

// -------------------------------------------------------------------------------------------
// R6 (e) — `ReleaseCoarser`: the refinement order, and the factoring it checks
// -------------------------------------------------------------------------------------------

/// One step of a declared coarsening tower: a receiver, and the claim that it factors through the
/// step before it. The claim is **checked** over the fibre, never assumed.
pub struct CoarseningStep {
    /// The coarser receiver.
    pub reading: Box<dyn Reading>,
}

impl Debug for CoarseningStep {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("CoarseningStep")
            .field("reading", &self.reading.name())
            .finish()
    }
}

/// **A declared coarsening tower**, finest first. This is the atlas refinement order of
/// [`crate::receiver_atlas::AtlasRefinement`] presented as a chain of readings, which is what
/// `ReleaseCoarser` needs: the coarser invariant to release is the first one up the tower whose
/// width falls inside tolerance.
#[derive(Debug)]
pub struct CoarseningTower {
    /// What this tower coarsens.
    pub lineage: String,
    /// The steps, finest first. Step `0` is the finest *coarsening* of the target reading.
    pub steps: Vec<CoarseningStep>,
}

/// What the coarser search returned.
///
/// [implemented-exact] **The tolerance is part of the object.** A `CoarserRelease` is the claim
/// *"this coarser receiver's width is inside `tolerance`"*, and the tolerance it was searched
/// under is carried with it so that the claim cannot be re-used against a different, narrower
/// tolerance. Every field is private and the only constructor is [`release_coarser`]: there is no
/// literal, no `Default` and no `Deserialize` that mints one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoarserRelease {
    receiver: String,
    width: Rat,
    step: usize,
    tolerance: Rat,
}

impl CoarserRelease {
    /// The coarser receiver's name.
    pub fn receiver(&self) -> &str {
        &self.receiver
    }

    /// Its exact width.
    pub fn width(&self) -> &Rat {
        &self.width
    }

    /// How many steps up the tower it sits.
    pub fn step(&self) -> usize {
        self.step
    }

    /// **The tolerance this release was searched under.** [`LawfulOptions::assemble`] refuses a
    /// release whose searched tolerance is not the tolerance being assembled.
    pub fn searched_tolerance(&self) -> &Rat {
        &self.tolerance
    }
}

/// **The coarser invariant whose width is inside tolerance, found through the refinement order.**
///
/// At every step the factoring is *checked* over the fibre: two members the finer reading
/// identifies must be identified by the coarser one, or the step is refused by name with the two
/// members that refute it. A tower whose steps do not actually coarsen is not a tower, and saying
/// so is the point.
///
/// Returns `None` when no step of the declared tower is inside tolerance — which is exactly when
/// `ReleaseCoarser` is not among the lawful returns.
pub fn release_coarser(
    fine: &dyn Reading,
    tower: &CoarseningTower,
    family: &CompatibleFamily,
    tolerance: &Rat,
    norm: DiameterNorm,
) -> Result<Option<CoarserRelease>, WidthRefusal> {
    let Some(members) = family.members() else {
        return Err(WidthRefusal::DeclaredReadingNeedsEnumeratedFamily {
            receiver: fine.name().to_owned(),
        });
    };
    if tower.steps.len() > TOWER_STEP_CEILING {
        return Err(WidthRefusal::TowerStepCeiling {
            requested: tower.steps.len(),
            ceiling: TOWER_STEP_CEILING,
        });
    }
    let mut previous: &dyn Reading = fine;
    for (step, entry) in tower.steps.iter().enumerate() {
        let coarse = entry.reading.as_ref();
        for left in 0..members.len() {
            for right in (left + 1)..members.len() {
                if previous.read(&members[left])? != previous.read(&members[right])? {
                    continue;
                }
                if coarse.read(&members[left])? != coarse.read(&members[right])? {
                    return Err(WidthRefusal::CoarserDoesNotFactor {
                        coarse: coarse.name().to_owned(),
                        fine: previous.name().to_owned(),
                        left,
                        right,
                    });
                }
            }
        }
        let reading = width_enumerated(coarse, family, norm)?;
        if reading.releasable_at(tolerance) {
            return Ok(Some(CoarserRelease {
                receiver: coarse.name().to_owned(),
                width: reading.diameter,
                step,
                tolerance: tolerance.clone(),
            }));
        }
        previous = coarse;
    }
    Ok(None)
}

/// A declared factor map on an exact rational reading. A *coarser* receiver is this map composed
/// with a finer one; whether it is also *narrower* depends on whether the map is non-expansive,
/// which [`FactoredReading::verify_non_expansive`] checks rather than assumes.
///
/// Lean counterpart: `NonExpansive`, `width_nonExpansive_factor` and
/// `expansive_factor_increases_width`.
pub trait FactorMap {
    /// The factor map's declared name.
    fn name(&self) -> &str;
    /// The map itself.
    fn apply(&self, value: &Rat) -> Rat;
}

/// **A coarser receiver**: a declared factor map composed with a finer reading. It factors through
/// the finer reading by construction — `coarser_receiver_factors` in the Lean owner — so it is a
/// lawful `ReleaseCoarser` target.
pub struct FactoredReading<'a> {
    /// The coarser receiver's declared name.
    pub receiver: String,
    /// The finer reading it factors through.
    pub fine: &'a dyn Reading,
    /// The declared factor map.
    pub factor: &'a dyn FactorMap,
}

impl Debug for FactoredReading<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FactoredReading")
            .field("receiver", &self.receiver)
            .field("fine", &self.fine.name())
            .field("factor", &self.factor.name())
            .finish()
    }
}

impl Reading for FactoredReading<'_> {
    fn name(&self) -> &str {
        &self.receiver
    }

    fn read(&self, state: &[Rat]) -> Result<ExactFace, WidthRefusal> {
        match self.fine.read(state)? {
            ExactFace::Vector(values) => Ok(ExactFace::Vector(
                values.iter().map(|value| self.factor.apply(value)).collect(),
            )),
            other => Err(WidthRefusal::FactorNeedsVectorFace {
                factor: self.factor.name().to_owned(),
                arm: other.arm(),
            }),
        }
    }
}

impl FactoredReading<'_> {
    /// **Check non-expansiveness on the fibre actually read**, rather than asserting it.
    ///
    /// For every pair of members and every coordinate of the finer reading, the factored
    /// separation must not exceed the finer one. A factor map that fails is returned by name with
    /// the pair and the coordinate that refute it — which is exactly the counterexample the Lean
    /// owner's `expansive_factor_increases_width` exhibits.
    pub fn verify_non_expansive(&self, family: &CompatibleFamily) -> Result<(), WidthRefusal> {
        let Some(members) = family.members() else {
            return Err(WidthRefusal::DeclaredReadingNeedsEnumeratedFamily {
                receiver: self.receiver.clone(),
            });
        };
        let fine = members
            .iter()
            .map(|member| self.fine.read(member))
            .collect::<Result<Vec<_>, _>>()?;
        for left in 0..fine.len() {
            for right in (left + 1)..fine.len() {
                let (ExactFace::Vector(a), ExactFace::Vector(b)) = (&fine[left], &fine[right])
                else {
                    return Err(WidthRefusal::FactorNeedsVectorFace {
                        factor: self.factor.name().to_owned(),
                        arm: fine[left].arm(),
                    });
                };
                if a.len() != b.len() {
                    return Err(WidthRefusal::VectorFacesDiffer {
                        left: a.len(),
                        right: b.len(),
                    });
                }
                for (coordinate, (x, y)) in a.iter().zip(b).enumerate() {
                    let before = (x - y).abs();
                    let after = (self.factor.apply(x) - self.factor.apply(y)).abs();
                    if after > before {
                        return Err(WidthRefusal::FactorIsExpansive {
                            factor: self.factor.name().to_owned(),
                            left,
                            right,
                            coordinate,
                        });
                    }
                }
            }
        }
        Ok(())
    }
}

// -------------------------------------------------------------------------------------------
// R6 (f) — the release law, declared by the caller
// -------------------------------------------------------------------------------------------

/// **The six lawful returns.** Only [`ReleaseReturn::Released`] is constrained by this module, and
/// only by the tolerance the caller itself declared.
///
/// Lean counterpart: `Foundation/ReceiverRelease.lean::ReleaseReturn`.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
#[serde(tag = "release", rename_all = "kebab-case")]
pub enum ReleaseReturn {
    /// The width is inside the declared tolerance.
    Released {
        /// The exact width.
        width: Rat,
        /// The tolerance it fell inside.
        tolerance: Rat,
    },
    /// Retain the plural fibre and emit nothing at this receiver.
    Hold,
    /// Declare a wider tolerance, named.
    Widen {
        /// The proposed tolerance.
        tolerance: Rat,
    },
    /// Name the input or observation that would narrow the fibre most.
    Ask {
        /// The computed probe.
        probe: AskProbe,
    },
    /// Release only the coarser invariant whose width is inside tolerance.
    ReleaseCoarser {
        /// The coarser receiver.
        receiver: String,
        /// Its exact width.
        width: Rat,
    },
    /// No admitted continuation bridges the gap.
    NoContinuationBridges {
        /// Why not, named.
        reason: String,
    },
}

/// **What the library computed and what is therefore lawfully available** to the caller's decision.
/// The library computes the options; it does not choose among them.
///
/// [implemented-exact] Every field is private and the only constructor is [`Self::assemble`],
/// which refuses an incoherent assembly rather than carrying it. In particular a
/// [`CoarserRelease`] searched under one tolerance cannot be assembled against another — the
/// two-call route *"search the coarser invariant at tolerance 10, assemble at tolerance 1/2,
/// release"* is refused at the assembly, not merely at the release.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LawfulOptions {
    width: Rat,
    tolerance: Rat,
    inside_tolerance: bool,
    ask: Option<AskProbe>,
    coarser: Option<CoarserRelease>,
    bridges: bool,
}

impl LawfulOptions {
    /// Assemble the options from a width and the declared apparatus. The caller declares the
    /// tolerance; nothing here has a default.
    ///
    /// # What is refused
    ///
    /// A `coarser` release searched under a tolerance other than `tolerance` is refused by name
    /// ([`WidthRefusal::CoarserSearchedAtAnotherTolerance`]). [`release_coarser`] answers the
    /// question *"is any step of this tower inside **this** tolerance"*, and its answer is only
    /// an answer to that question; re-presenting it under a narrower tolerance would release a
    /// face outside the tolerance actually declared.
    pub fn assemble(
        reading: &ReceiverWidth,
        tolerance: Rat,
        ask: Option<AskProbe>,
        coarser: Option<CoarserRelease>,
        bridges: bool,
    ) -> Result<Self, WidthRefusal> {
        if let Some(offered) = &coarser
            && offered.tolerance != tolerance
        {
            return Err(WidthRefusal::CoarserSearchedAtAnotherTolerance(Box::new(
                CoarserToleranceClaim {
                    receiver: offered.receiver.clone(),
                    searched: offered.tolerance.clone(),
                    declared: tolerance,
                },
            )));
        }
        let inside_tolerance = reading.releasable_at(&tolerance);
        Ok(Self {
            width: reading.diameter.clone(),
            tolerance,
            inside_tolerance,
            ask,
            coarser,
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

    /// The computed probe, when there is one to ask for.
    pub fn ask(&self) -> Option<&AskProbe> {
        self.ask.as_ref()
    }

    /// The coarser invariant inside tolerance, when the declared tower carries one.
    pub fn coarser(&self) -> Option<&CoarserRelease> {
        self.coarser.as_ref()
    }

    /// Whether any admitted continuation bridges the gap at all.
    pub fn bridges(&self) -> bool {
        self.bridges
    }
}

/// A caller's **declared** decision law. There is no default implementation and no blanket
/// implementation: the decision is supplied, exactly as a metric is supplied to a chart in
/// [`crate::receiver_atlas::Capability`].
pub trait DecisionLaw {
    /// The law's declared name, for the refusal.
    fn name(&self) -> &str;
    /// The decision.
    fn decide(&self, options: &LawfulOptions) -> ReleaseReturn;
}

/// **Take the declared law's decision, and check the one thing the library owns.**
///
/// A law returning [`ReleaseReturn::Released`] with the width outside its own declared tolerance is
/// refused by name; a law asking for a probe the options did not offer, or releasing a coarser
/// receiver the tower did not return, is refused by name. Nothing else is constrained: `Hold`,
/// `Widen`, `Ask`, `ReleaseCoarser` and `NoContinuationBridges` are the caller's to choose among,
/// and this module supplies no default and no global gate.
///
/// Lean counterpart: `ReleaseLaw.sound`.
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
                    probe: probe.name(),
                });
            }
        },
        ReleaseReturn::ReleaseCoarser { receiver, width } => match &options.coarser {
            Some(offered) if &offered.receiver == receiver && &offered.width == width => {
                // The coarser arm releases a face, so it carries the same obligation the
                // `Released` arm does: the released width is inside the tolerance these options
                // were assembled against. Matching `(receiver, width)` against the offer is not
                // that check — the offer was searched under its own tolerance, which
                // `LawfulOptions::assemble` has already required to be this one, and the
                // inequality is recomputed here rather than inherited.
                //
                // Lean counterpart: the `releaseCoarser` constructor of
                // `Foundation/ReceiverRelease.lean::ReleaseReturn` carries
                // `coarserWidth ≤ tolerance` as an argument, and
                // `every_lawful_return_other_than_hold_ask_or_no_continuation_is_inside_its_tolerance`
                // collects the three arms that name a tolerance.
                if width > &options.tolerance {
                    return Err(WidthRefusal::CoarserReleasedOutsideTolerance(Box::new(
                        CoarserClaim {
                            law: law.name().to_owned(),
                            receiver: receiver.clone(),
                            width: width.clone(),
                            tolerance: options.tolerance.clone(),
                        },
                    )));
                }
            }
            _ => {
                return Err(WidthRefusal::CoarserNotOffered {
                    law: law.name().to_owned(),
                    receiver: receiver.clone(),
                });
            }
        },
        ReleaseReturn::Hold
        | ReleaseReturn::Widen { .. }
        | ReleaseReturn::NoContinuationBridges { .. } => {}
    }
    Ok(decision)
}

// -------------------------------------------------------------------------------------------
// R6 (g) — refusals
// -------------------------------------------------------------------------------------------

/// The release a declared law claimed, with the tolerance it declared it against. Carried behind a
/// box inside [`WidthRefusal::ReleasedOutsideTolerance`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReleasedClaim {
    /// The law that claimed it.
    pub law: String,
    /// The exact width it released.
    pub width: Rat,
    /// The exact tolerance it declared.
    pub tolerance: Rat,
}

/// A coarser release offered against a tolerance other than the one it was searched under.
/// Carried behind a box inside [`WidthRefusal::CoarserSearchedAtAnotherTolerance`], so the
/// refusal stays small.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoarserToleranceClaim {
    /// The coarser receiver named by the release.
    pub receiver: String,
    /// The tolerance [`release_coarser`] searched under.
    pub searched: Rat,
    /// The tolerance the options declare.
    pub declared: Rat,
}

/// The coarser release a declared law claimed, with the tolerance the options were assembled
/// against. Carried behind a box inside [`WidthRefusal::CoarserReleasedOutsideTolerance`].
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CoarserClaim {
    /// The law that claimed it.
    pub law: String,
    /// The coarser receiver it claimed to release.
    pub receiver: String,
    /// The exact width it released.
    pub width: Rat,
    /// The exact tolerance the options declared.
    pub tolerance: Rat,
}

/// Why a width or a release was refused. Every failure is returned as content.
#[derive(Debug, Error)]
pub enum WidthRefusal {
    /// A coarser release searched under one tolerance was assembled against another.
    #[error(
        "the coarser receiver {} was searched inside tolerance {} and cannot be offered against \
         the declared tolerance {}",
        .0.receiver, .0.searched, .0.declared
    )]
    CoarserSearchedAtAnotherTolerance(Box<CoarserToleranceClaim>),
    /// A remounted width declares a schema this module does not own.
    #[error("a receiver width declaring schema {declared} is not a {expected}")]
    WidthSchemaMismatch {
        /// What the wire declared.
        declared: String,
        /// What this module owns.
        expected: &'static str,
    },
    /// A remounted width declares a negative diameter. A diameter is a maximum of absolute
    /// separations and is never negative (`width_nonneg`).
    #[error("a receiver width of {declared} is negative; a diameter is a maximum of absolute separations")]
    NegativeWidth {
        /// The declared diameter, as prose.
        declared: String,
    },
    /// A remounted width's attaining witness does not index the reading it claims.
    #[error("an attaining witness {witness} does not index a reading of {read} members")]
    WitnessOutsideReading {
        /// How many members the width claims to have read.
        read: usize,
        /// The witness, as prose.
        witness: String,
    },
    /// A declared law released a coarser receiver outside the declared tolerance.
    #[error(
        "the law {} released the coarser receiver {} at width {} outside the declared tolerance {}",
        .0.law, .0.receiver, .0.width, .0.tolerance
    )]
    CoarserReleasedOutsideTolerance(Box<CoarserClaim>),
    /// A compatible family with no member has no diameter.
    #[error("a compatible family with no member has no width")]
    EmptyFamily,
    /// A zero-dimensional carrier has no reading.
    #[error("a zero-dimensional carrier carries no receiver reading")]
    EmptyDimension,
    /// Two declared extents do not agree.
    #[error("a carrier of dimension {declared} does not pair with one of dimension {found}")]
    DimensionMismatch {
        /// What was declared.
        declared: usize,
        /// What was found.
        found: usize,
    },
    /// A declared enclosure asks for more generators than the ceiling admits.
    #[error(
        "an enclosure of {requested} uncertainty generators exceeds the declared ceiling {ceiling}; \
         nothing was allocated"
    )]
    GeneratorCeiling {
        /// How many were asked for.
        requested: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// The generator count of an `h`-step image does not fit a machine integer.
    #[error(
        "{states} state generators and {inputs} input generators over horizon {horizon} overflow \
         the machine integer counting them; nothing was allocated"
    )]
    GeneratorCountOverflows {
        /// State generators.
        states: usize,
        /// Input generators.
        inputs: usize,
        /// The declared horizon.
        horizon: usize,
    },
    /// A declared carrier extent is wider than the ceiling admits.
    #[error(
        "a carrier of extent {requested} exceeds the declared ceiling {ceiling}; nothing was \
         allocated and no product was formed"
    )]
    ExtentCeiling {
        /// The declared extent.
        requested: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// The exact multiplications a declared horizon and extent ask for exceed the work ceiling.
    #[error(
        "a horizon of {horizon} steps at extent {extent} asks for more than the declared ceiling \
         of {ceiling} exact products; no step was taken"
    )]
    MultiplyWorkCeiling {
        /// The declared extent.
        extent: usize,
        /// The declared horizon.
        horizon: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// A declared coarsening tower carries more steps than the ceiling admits.
    #[error(
        "a coarsening tower of {requested} steps exceeds the declared ceiling {ceiling}; no step \
         was checked"
    )]
    TowerStepCeiling {
        /// The declared step count.
        requested: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// More candidate observations were declared than the ceiling admits.
    #[error(
        "a probe over {requested} candidate observations exceeds the declared ceiling {ceiling}; \
         no candidate was read"
    )]
    CandidateCeiling {
        /// The declared candidate count.
        requested: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// A declared horizon is longer than the ceiling admits.
    #[error(
        "a horizon of {requested} steps exceeds the declared ceiling {ceiling}; nothing was \
         allocated and no step was taken"
    )]
    HorizonCeiling {
        /// How many steps were asked for.
        requested: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// A declared two-axis horizon reaches further through the index than the ceiling admits.
    #[error(
        "an index horizon of {requested} chart steps exceeds the declared ceiling {ceiling}; \
         no chart was walked and no fibre was opened"
    )]
    IndexHorizonCeiling {
        /// How many index steps were asked for.
        requested: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// A declared enumerated family is wider than the ceiling admits.
    #[error(
        "an enumerated family of {declared} members exceeds the declared ceiling {ceiling}; \
         nothing was allocated"
    )]
    FamilyCeiling {
        /// How many were declared.
        declared: usize,
        /// The ceiling.
        ceiling: usize,
    },
    /// The pair count of a declared family does not fit a machine integer.
    #[error("the unordered pairs of {members} members overflow the machine integer counting them")]
    PairCountOverflows {
        /// How many members were declared.
        members: usize,
    },
    /// A generator index outside the enclosure.
    #[error("generator {index} lies outside an enclosure carrying {carried}")]
    GeneratorAbsent {
        /// The index asked for.
        index: usize,
        /// How many the enclosure carries.
        carried: usize,
    },
    /// A declared half-width was negative.
    #[error("coordinate {coordinate} was declared a negative half-width, which is not an extent")]
    NegativeHalfWidth {
        /// Which coordinate.
        coordinate: usize,
    },
    /// Two faces of different arms have no separation.
    #[error("a {left} face and a {right} face are incomparable and no separation is invented")]
    FacesIncomparable {
        /// The first arm.
        left: &'static str,
        /// The second arm.
        right: &'static str,
    },
    /// Two vector faces of different lengths have no separation.
    #[error("a vector face of length {left} and one of length {right} are incomparable")]
    VectorFacesDiffer {
        /// The first length.
        left: usize,
        /// The second length.
        right: usize,
    },
    /// A declared reading was asked for a width over an enclosure it cannot read.
    #[error(
        "the declared reading {receiver:?} is not linear, so its width needs an enumerated \
         compatible family; an enclosure is refused rather than sampled"
    )]
    DeclaredReadingNeedsEnumeratedFamily {
        /// The receiver that refused.
        receiver: String,
    },
    /// An enclosure reading was asked for a width over an enumerated family.
    #[error("the enclosure reading {receiver:?} was given an enumerated family instead of a hull")]
    EnclosedReadingNeedsEnclosure {
        /// The receiver that refused.
        receiver: String,
    },
    /// A norm that is not exact on an enclosure.
    #[error(
        "the {norm} diameter of a zonotope is attained at a vertex of its generator cube, so it is \
         not computed exactly on an enclosure; declare the supremum norm or enumerate the family"
    )]
    NormNotExactOnEnclosure {
        /// The norm that was declared.
        norm: &'static str,
    },
    /// A declared law released outside its own declared tolerance. The claim is boxed because two
    /// exact rationals and a name are the largest payload this refusal carries, and an unboxed
    /// variant would widen every `Result` in the module.
    #[error(
        "the decision law {:?} released a width of {} outside its own declared tolerance of {}",
        .0.law, .0.width, .0.tolerance
    )]
    ReleasedOutsideTolerance(Box<ReleasedClaim>),
    /// A declared law asked for a probe the library did not compute.
    #[error("the decision law {law:?} asked for the probe {probe:?}, which was not among the computed options")]
    ProbeNotOffered {
        /// The law.
        law: String,
        /// The probe it named.
        probe: String,
    },
    /// A declared law released a coarser receiver the tower did not return.
    #[error(
        "the decision law {law:?} released the coarser receiver {receiver:?}, which the declared \
         tower did not return inside tolerance"
    )]
    CoarserNotOffered {
        /// The law.
        law: String,
        /// The receiver it named.
        receiver: String,
    },
    /// A declared coarsening step does not factor through the step before it.
    #[error(
        "the receiver {coarse:?} does not factor through {fine:?}: members {left} and {right} of \
         the fibre are identified by the finer reading and separated by the coarser one, so the \
         declared tower is not a coarsening"
    )]
    CoarserDoesNotFactor {
        /// The coarser receiver.
        coarse: String,
        /// The finer one.
        fine: String,
        /// The first member.
        left: usize,
        /// The second.
        right: usize,
    },
    /// A factor map was composed with a reading whose face it cannot act on.
    #[error("the factor map {factor:?} acts on a vector face and was given a {arm} face")]
    FactorNeedsVectorFace {
        /// The factor map.
        factor: String,
        /// The arm it was given.
        arm: &'static str,
    },
    /// A declared factor map increases a separation on the fibre actually read.
    #[error(
        "the factor map {factor:?} is expansive on this fibre: at coordinate {coordinate} it \
         separates members {left} and {right} further than the finer reading does, so the coarser \
         receiver is not narrower"
    )]
    FactorIsExpansive {
        /// The factor map.
        factor: String,
        /// The first member.
        left: usize,
        /// The second.
        right: usize,
        /// The coordinate that refutes it.
        coordinate: usize,
    },
    /// The exact linear algebra refused.
    #[error(transparent)]
    Linear(#[from] ExactLinearError),
}

impl PartialEq for WidthRefusal {
    fn eq(&self, other: &Self) -> bool {
        self.to_string() == other.to_string()
    }
}

#[cfg(test)]
#[path = "receiver_release/tests.rs"]
mod tests;
