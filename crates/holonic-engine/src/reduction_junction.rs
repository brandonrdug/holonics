//! **The shared-output reduction junction: `y = sum_a T_a y_a`, with its word, its widths, its one
//! rounding and its adjoint returns.**
//!
//! # What was attempted first, and exactly what it could not express
//!
//! | owner | what it carries | what it cannot say |
//! |---|---|---|
//! | [`crate::exact_linear::ExactRatMatrix::metric_adjoint`] | `G_X^-1 T^T G_Y` for **one** map, and [`crate::exact_linear::ExactRatMatrix::adjoint_defect`] exhibits its defect against a declared pair | **one map, not a family into one output.** There is no term for a population of partials writing one logical output, so there is nothing to reduce and nothing to return the adjoint *of*. |
//! | [`crate::exact_work::ExactWork`] | additions, multiplications, `peak_bits` — the widest single entry, and a `dependency_span` | **no per-node width and no aperture that refuses.** `peak_bits` is one maximum over a whole deed; it cannot say which node of which reduction word was widest, and it is a *measurement* that never refuses. An overflow aperture that turns a width into a refusal has no term anywhere. |
//! | [`crate::interchange::certify_footprints`] | that two members do not share an address | it *refuses* a shared output; it has no construction that makes one lawful. |
//! | [`crate::hardware_cover::CoverDecomposition`] | which chart carries which cell | no reduction, no order, no rounding. |
//! | [`crate::exact_value::ExactInterval`] | an exact enclosure as a set | one carrier, no junction and no directed boundary. |
//!
//! So the absent relation founded here is: **a fixed reduction word over a declared family of
//! partials into one owned output, carrying the intermediate width at every node against a declared
//! overflow aperture, exactly one directed rounding at a declared boundary with its residual
//! retained, and the adjoint return into every partial chart.** The absent *types* are
//! [`ReductionWord`] and [`NodeWidth`]; the absent *constitutive law* is one outward rounding at the
//! boundary and nowhere else; the absent *consequence* is `ybar_a = T_a^* ybar` for every `a`.
//!
//! # What is composed
//!
//! - [`crate::exact_linear::ExactRatMatrix`] for every `T_a`, its metric adjoint and its exact
//!   adjoint defect — this module builds no adjoint of its own and asserts no orthonormality;
//! - [`crate::section_partition::SectionRegion`] and
//!   [`crate::section_partition::uncovered_regions`] for the inner regions `K_a`, so the inner
//!   partition is certified by the same computation the output partition is;
//! - [`crate::exact_work::ExactWork`] for the reduction's own counted work.
//!
//! # Two things the receipt says about its own evidence
//!
//! **Value agreement between the word and its reversed control is forced by exactness**, because
//! addition over `Rat` is associative and commutative. It is therefore a control on the
//! *implementation* — that the walker reduces the declared leaves in the declared word and that no
//! rounding enters mid-tree — and it is evidence about nothing else. What is *not* forced is the
//! per-node width, which differs between the two words on cancelling material, and the aperture
//! refusal, which is a genuine falsifier.
//!
//! **The rounding policy is what makes the value control non-vacuous.** Under
//! [`RoundingPolicy::AtEveryNode`] the two words disagree in value on the same material; under
//! [`RoundingPolicy::OnceAtBoundary`] they agree. [`ReductionJunction::certify`] admits only the
//! second and returns [`ReductionDefect::RoundingNotAtBoundary`] for the first, so the control
//! reading is available and the law is not.

use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use relational_geometry::Rat;

use crate::exact_linear::{ExactLinearError, ExactRatMatrix};
use crate::exact_work::ExactWork;
use crate::section_partition::{uncovered_regions, JunctionOutput, SectionRegion, SectionShape};

// -------------------------------------------------------------------------------------------------
// the word
// -------------------------------------------------------------------------------------------------

/// A node of the fixed reduction word: a leaf naming one partial, or a join of two nodes.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReductionNode {
    Leaf(usize),
    Join(Box<ReductionNode>, Box<ReductionNode>),
}

impl ReductionNode {
    /// The leaves this node reduces, in the word's own order.
    pub fn leaves(&self) -> Vec<usize> {
        match self {
            ReductionNode::Leaf(leaf) => vec![*leaf],
            ReductionNode::Join(left, right) => {
                let mut leaves = left.leaves();
                leaves.extend(right.leaves());
                leaves
            }
        }
    }

    /// The number of joins below and including this node — the additions the word performs.
    pub fn joins(&self) -> usize {
        match self {
            ReductionNode::Leaf(_) => 0,
            ReductionNode::Join(left, right) => 1 + left.joins() + right.joins(),
        }
    }

    /// The longest chain of joins from this node to a leaf: the word's dependency span.
    pub fn span(&self) -> usize {
        match self {
            ReductionNode::Leaf(_) => 0,
            ReductionNode::Join(left, right) => 1 + left.span().max(right.span()),
        }
    }

    fn relabel(&self, map: &dyn Fn(usize) -> usize) -> Self {
        match self {
            ReductionNode::Leaf(leaf) => ReductionNode::Leaf(map(*leaf)),
            ReductionNode::Join(left, right) => ReductionNode::Join(
                Box::new(left.relabel(map)),
                Box::new(right.relabel(map)),
            ),
        }
    }
}

/// **The fixed reduction word**: a declared binary tree over the partials. Fixed, so the receipt
/// can be reproduced; declared, so the reversed control is a different word over the same material
/// rather than a different implementation.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReductionWord {
    pub root: ReductionNode,
}

impl ReductionWord {
    /// A left-leaning word: `((((0,1),2),3),4)`. Its prefix sums are the accumulation a serial
    /// reduction performs, which is what makes its widths differ from the reversed control's.
    pub fn left_leaning(leaves: usize) -> Option<Self> {
        if leaves == 0 {
            return None;
        }
        let mut root = ReductionNode::Leaf(0);
        for leaf in 1..leaves {
            root = ReductionNode::Join(Box::new(root), Box::new(ReductionNode::Leaf(leaf)));
        }
        Some(Self { root })
    }

    /// A balanced word over `leaves` partials.
    pub fn balanced(leaves: usize) -> Option<Self> {
        if leaves == 0 {
            return None;
        }
        Some(Self {
            root: balanced_node(0, leaves),
        })
    }

    /// **The reversed control**: the same tree shape with the leaves relabelled `i -> n-1-i`.
    ///
    /// The shape is held fixed and the assignment reversed, so the two words visit the same
    /// material in genuinely different accumulation orders. Mirroring the tree instead would
    /// reproduce the same node values and control nothing.
    pub fn reversed(&self, leaves: usize) -> Self {
        Self {
            root: self.root.relabel(&move |leaf| leaves.saturating_sub(1) - leaf),
        }
    }

    pub fn leaves(&self) -> Vec<usize> {
        self.root.leaves()
    }

    /// The word as text, so the receipt carries it rather than referring to it.
    pub fn written(&self) -> String {
        write_node(&self.root)
    }
}

fn balanced_node(from: usize, to: usize) -> ReductionNode {
    if to - from == 1 {
        return ReductionNode::Leaf(from);
    }
    let middle = from + (to - from) / 2;
    ReductionNode::Join(
        Box::new(balanced_node(from, middle)),
        Box::new(balanced_node(middle, to)),
    )
}

fn write_node(node: &ReductionNode) -> String {
    match node {
        ReductionNode::Leaf(leaf) => format!("{leaf}"),
        ReductionNode::Join(left, right) => {
            format!("({} + {})", write_node(left), write_node(right))
        }
    }
}

// -------------------------------------------------------------------------------------------------
// the partials, the rounding and the junction
// -------------------------------------------------------------------------------------------------

/// One partial of a shared-output junction: which inner region it contracts, what it carries in its
/// own chart, and the chart transition into the output's.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartialTerm {
    pub index: usize,
    /// `K_a` — the coordinate region of the inner axis this partial contracts.
    pub inner: SectionRegion,
    /// The partial's exact value in **its own** chart. Exact rationals; never a float.
    pub carried: Vec<Rat>,
    /// The lower and upper exact enclosure of `carried`, coordinate by coordinate. A partial that
    /// stands exactly carries an enclosure equal to itself.
    pub enclosure: Vec<(Rat, Rat)>,
    /// `T_a` — the chart transition from this partial's chart to the output's, `m` rows by `n_a`
    /// columns. The identity embedding is written down as an identity matrix and **declared**; it
    /// is never assumed.
    pub chart: ExactRatMatrix,
    /// `G_X` — the declared receiver metric on this partial's own chart. The Euclidean case is the
    /// identity and must be written down.
    pub domain_metric: ExactRatMatrix,
}

/// The one rounding a junction performs. Outward, so the boundary value encloses the exact one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum DirectedRounding {
    Outward,
}

/// Where rounding is permitted to happen. Only [`RoundingPolicy::OnceAtBoundary`] is lawful; the
/// other exists so the control can exhibit what it costs.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RoundingPolicy {
    OnceAtBoundary,
    AtEveryNode,
}

/// **A shared-output junction.** Several partials write one logical output; this owns the output
/// and states how they join.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReductionJunction {
    /// Who owns the output region. A partial does not.
    pub owner: String,
    /// The output's coordinate region in the section.
    pub output: SectionRegion,
    /// The dimension of the output chart the partials are carried into.
    pub output_dimension: usize,
    /// The inner axis `K` the partials partition. `1 x K`, so `uncovered_regions` reads it.
    pub inner_shape: SectionShape,
    pub partials: Vec<PartialTerm>,
    /// The fixed word. Its leaves must be exactly the partials, each once.
    pub word: ReductionWord,
    /// The greatest intermediate width, in bits, this junction is admitted at. A node above it
    /// refuses; nothing wraps.
    pub overflow_aperture: u64,
    /// The carrier's grain, `2^-carrier_exponent`, at which the partials stand exactly.
    pub carrier_exponent: u32,
    /// The declared boundary's grain, `2^-boundary_exponent`, at which the one rounding happens.
    pub boundary_exponent: u32,
    pub rounding: DirectedRounding,
    pub policy: RoundingPolicy,
    /// `G_Y` — the declared receiver metric on the output chart.
    pub codomain_metric: ExactRatMatrix,
    /// `ybar` — the covector returned to the output, which the adjoints carry into every partial
    /// chart.
    pub returned_covector: Vec<Rat>,
}

// -------------------------------------------------------------------------------------------------
// the receipt
// -------------------------------------------------------------------------------------------------

/// One node of one word, with the width it stood at.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NodeWidth {
    /// The leaves this node reduces, in the word's order.
    pub leaves: Vec<usize>,
    /// The node's exact value in the output chart.
    pub value: Vec<Rat>,
    /// The widest coordinate's exact width: the numerator's bits plus the denominator's, which is
    /// what an exact rational actually costs.
    pub width_bits: u64,
    /// Joins between this node and a leaf.
    pub depth: usize,
}

/// The reading of one word over the same partials.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct WordReading {
    pub word: String,
    pub leaves: Vec<usize>,
    pub nodes: Vec<NodeWidth>,
    /// The exact value at the root, before any rounding.
    pub value: Vec<Rat>,
    /// The widest node.
    pub peak_width_bits: u64,
    /// The longest chain of joins.
    pub dependency_span: usize,
    /// How many roundings this reading performed. The law admits exactly one, at the boundary.
    pub roundings: usize,
}

/// The adjoint return into one partial's chart.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct AdjointReturn {
    pub partial: usize,
    /// `T_a^* = G_X^-1 T_a^T G_Y`, from `exact_linear::metric_adjoint`.
    pub adjoint: ExactRatMatrix,
    /// `ybar_a = T_a^* ybar`.
    pub returned: Vec<Rat>,
    /// **The exact operator residual `G_X T_a^* - T_a^T G_Y`.** The characterization
    /// `<T x, y>_Y = <x, T^dagger y>_X` holds for every `x` and `y` exactly when this matrix is
    /// zero, so this is the whole claim, exhibited rather than sampled.
    pub residual: ExactRatMatrix,
    /// The widest absolute entry of [`AdjointReturn::residual`] — a face of it, order-free, and
    /// zero exactly when the residual is the zero operator. The residual stands beside it and is
    /// the object.
    pub defect: Rat,
    /// The same residual for a claimed **bare transpose**: `G_X T_a^T - T_a^T G_Y`.
    pub bare_transpose_residual: ExactRatMatrix,
    /// The widest absolute entry of [`AdjointReturn::bare_transpose_residual`]. Zero exactly when
    /// the bare transpose IS the adjoint, which for an invertible `G_X` means `T^T G_Y = G_X T^T`.
    ///
    /// **This is an operator fact and no longer a probe.** It was read at one authored pair
    /// `x = (1, 2, ..., n)` against the declared covector until 2026-08-19, and that reading went
    /// silently vacuous: for `T = I`, `G_X = I`, `G_Y = diag(1, 3)` and `ybar = (1, 0)` the probe
    /// returns zero under a metric that is not the identity, so the receipt could not be told from
    /// the Euclidean case. The authored probe is removed; nothing here samples.
    pub bare_transpose_defect: Rat,
}

/// **The reduction receipt.**
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ReductionReceipt {
    pub schema: String,
    pub owner: String,
    pub output: SectionRegion,
    pub output_dimension: usize,
    /// Per partial: its inner region, its exact carried value, its enclosure, its width.
    pub partials: Vec<PartialReceipt>,
    /// The inner regions certified as a partition of `K`, computed.
    pub inner_uncovered: Vec<SectionRegion>,
    pub inner_overlaps: Vec<(usize, usize, SectionRegion)>,
    /// The declared word.
    pub declared: WordReading,
    /// The reversed control over the same partials.
    pub reversed: WordReading,
    /// Whether the two words agree coordinate by coordinate before rounding.
    pub words_agree: bool,
    pub overflow_aperture: u64,
    pub carrier_exponent: u32,
    pub boundary_exponent: u32,
    pub rounding: DirectedRounding,
    /// The boundary value: an exact integer at `2^-boundary_exponent`, one per output coordinate.
    pub boundary_value: Vec<BigInt>,
    /// `exact - rounded`, exactly, one per output coordinate. Outward rounding makes it oppose the
    /// value's own hand or vanish.
    pub boundary_residual: Vec<Rat>,
    /// **How many `round_outward` invocations the certified path performed** — the unit is one
    /// invocation, and the count is the total: one per output coordinate at the declared boundary,
    /// plus any the policy took inside the tree, which the admitted policy takes none of. So a
    /// scalar output reads `1` and a two-coordinate output reads `2`, and the field moves with a
    /// declared input rather than standing as a constant.
    pub roundings: usize,
    pub adjoints: Vec<AdjointReturn>,
    /// Every defect the reading survived without refusing — empty on a certified junction, and
    /// carried so a caller reading only the value cannot lose the lineage.
    pub obstruction_lineage: Vec<String>,
    pub work: ExactWork,
}

/// One partial's half of the receipt.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartialReceipt {
    pub index: usize,
    pub inner: SectionRegion,
    pub inner_extent: u64,
    pub carried: Vec<Rat>,
    pub enclosure: Vec<(Rat, Rat)>,
    /// The width of the partial in its own chart.
    pub width_bits: u64,
    /// `T_a` as the receipt carries it; a caller never has to go back to the junction for it.
    pub chart: ExactRatMatrix,
    /// The width of `T_a y_a`, in the output chart.
    pub carried_width_bits: u64,
}

impl ReductionReceipt {
    /// The output value at the boundary, as an exact rational: `k * 2^-boundary_exponent`.
    pub fn boundary_rational(&self) -> Vec<Rat> {
        let scale = boundary_scale(self.boundary_exponent);
        self.boundary_value
            .iter()
            .map(|value| Rat::new(value.clone(), scale.clone()))
            .collect()
    }
}

// -------------------------------------------------------------------------------------------------
// the defects
// -------------------------------------------------------------------------------------------------

/// Why a junction is not a junction.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReductionDefect {
    /// The word's leaves are not exactly the partials, each once.
    WordDisagrees {
        declared_leaves: Vec<usize>,
        partials: usize,
    },
    /// A node stood wider than the declared overflow aperture. **It refuses; nothing wraps.**
    WidthExceedsAperture {
        word: String,
        leaves: Vec<usize>,
        width_bits: u64,
        aperture: u64,
    },
    /// `T_a` does not carry the partial's chart into the output's.
    ChartShape {
        partial: usize,
        rows: usize,
        columns: usize,
        output_dimension: usize,
        carried: usize,
    },
    /// A declared metric is not square, or does not match the chart it is declared on.
    MetricShape { partial: Option<usize> },
    /// The claimed adjoint failed its own characterization **as an operator**: the exact residual
    /// `G_X T* - T^T G_Y` is not the zero matrix. The residual is exhibited, not summarized.
    AdjointDefect {
        partial: usize,
        defect: Rat,
        residual: ExactRatMatrix,
    },
    /// A leaf of the word names no partial. **Never read as an exact zero**: a fabricated zero at
    /// the public reader is a silent wrap, and the value it produces cannot be told from a real one.
    UnknownLeaf { leaf: usize, partials: usize },
    /// A partial contracts an inner region the declared axis does not have. Checked the way a
    /// foreign cell write is; without it a foreign extent also suppresses the hole check.
    InnerOutsideAxis {
        partial: usize,
        region: SectionRegion,
        shape: SectionShape,
    },
    /// A carried value does not stand exactly at the declared carrier grain: its denominator is not
    /// a power of two dividing `2^carrier_exponent`. Without this, `carrier_exponent` is compared
    /// only with `boundary_exponent` and both are declared numbers with no material behind either.
    CarrierGrainRefused {
        partial: usize,
        coordinate: usize,
        value: Rat,
        carrier_exponent: u32,
    },
    /// The rounding policy is not one rounding at the boundary.
    RoundingNotAtBoundary { roundings: usize },
    /// The declared boundary is finer than the carrier the partials stand at, so the "rounding"
    /// would be an interpolation.
    BoundaryFinerThanCarrier { carrier: u32, boundary: u32 },
    /// The inner regions do not partition `K`.
    InnerUncovered { region: SectionRegion },
    /// Two inner regions meet.
    InnerOverlaps {
        partials: (usize, usize),
        region: SectionRegion,
    },
    /// The two words disagreed on the value. Under one boundary rounding this cannot happen; under
    /// any other policy it can, which is the whole content of the control.
    WordsDisagree {
        coordinate: usize,
        declared: Rat,
        reversed: Rat,
    },
    /// An exact linear owner refused.
    Linear(ExactLinearError),
}

impl std::fmt::Display for ReductionDefect {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            ReductionDefect::WordDisagrees {
                declared_leaves,
                partials,
            } => write!(
                formatter,
                "the word names leaves {declared_leaves:?} over {partials} partials"
            ),
            ReductionDefect::WidthExceedsAperture {
                word,
                leaves,
                width_bits,
                aperture,
            } => write!(
                formatter,
                "in {word}, the node over {leaves:?} stands at {width_bits} bits against an \
                 aperture of {aperture}"
            ),
            ReductionDefect::ChartShape {
                partial,
                rows,
                columns,
                output_dimension,
                carried,
            } => write!(
                formatter,
                "partial {partial} carries {carried} coordinates through a {rows} x {columns} \
                 chart into a {output_dimension}-dimensional output"
            ),
            ReductionDefect::MetricShape { partial } => match partial {
                Some(partial) => write!(formatter, "the metric declared on partial {partial} does not fit its chart"),
                None => write!(formatter, "the output metric does not fit the output chart"),
            },
            ReductionDefect::AdjointDefect {
                partial,
                defect,
                residual,
            } => write!(
                formatter,
                "the adjoint into partial {partial} leaves an operator residual with widest entry \
                 {defect}: {:?}",
                residual.to_rows()
            ),
            ReductionDefect::UnknownLeaf { leaf, partials } => write!(
                formatter,
                "the word names leaf {leaf} over {partials} partials; it holds no partial"
            ),
            ReductionDefect::InnerOutsideAxis {
                partial,
                region,
                shape,
            } => write!(
                formatter,
                "partial {partial} contracts {region}, which lies outside the {} x {} inner axis",
                shape.rows, shape.width
            ),
            ReductionDefect::CarrierGrainRefused {
                partial,
                coordinate,
                value,
                carrier_exponent,
            } => write!(
                formatter,
                "partial {partial} carries {value} at coordinate {coordinate}, which does not \
                 stand exactly at the declared carrier grain 2^-{carrier_exponent}"
            ),
            ReductionDefect::RoundingNotAtBoundary { roundings } => write!(
                formatter,
                "the reduction rounded {roundings} times; the law admits one, at the boundary"
            ),
            ReductionDefect::BoundaryFinerThanCarrier { carrier, boundary } => write!(
                formatter,
                "the boundary grain 2^-{boundary} is finer than the carrier's 2^-{carrier}"
            ),
            ReductionDefect::InnerUncovered { region } => {
                write!(formatter, "no partial contracts the inner region {region}")
            }
            ReductionDefect::InnerOverlaps { partials, region } => write!(
                formatter,
                "partials {} and {} both contract {region}",
                partials.0, partials.1
            ),
            ReductionDefect::WordsDisagree {
                coordinate,
                declared,
                reversed,
            } => write!(
                formatter,
                "coordinate {coordinate} reduced to {declared} under the word and {reversed} under \
                 its reversed control"
            ),
            ReductionDefect::Linear(error) => write!(formatter, "{error}"),
        }
    }
}

// -------------------------------------------------------------------------------------------------
// the certification
// -------------------------------------------------------------------------------------------------

fn boundary_scale(exponent: u32) -> BigInt {
    BigInt::from(1) << exponent
}

/// Whether an exact rational stands **exactly** at the grain `2^-exponent`: its denominator must
/// be a power of two, and no finer than the grain. `1/3` stands at no dyadic grain whatever.
fn stands_at_grain(value: &Rat, exponent: u32) -> bool {
    let denominator = value.denom();
    if denominator.is_negative() || denominator.is_zero() {
        return false;
    }
    let one = BigInt::from(1);
    // A power of two is exactly the positive integer with `d & (d - 1) == 0`.
    if (denominator.clone() & (denominator - &one)) != BigInt::from(0) {
        return false;
    }
    // `d = 2^k` has `k + 1` bits, so the grain admits it when `k <= exponent`.
    denominator.bits().saturating_sub(1) <= u64::from(exponent)
}

fn width_bits(value: &Rat) -> u64 {
    value.numer().bits() + value.denom().bits()
}

fn widest(values: &[Rat]) -> u64 {
    values.iter().map(width_bits).max().unwrap_or(0)
}

/// The widest absolute entry of an exact matrix. Zero exactly when the matrix is the zero operator,
/// and order-free — a face of the matrix, which stands beside it.
fn widest_entry(matrix: &ExactRatMatrix) -> Rat {
    matrix
        .entries()
        .iter()
        .map(|entry| if entry.numer().is_negative() { -entry } else { entry.clone() })
        .max()
        .unwrap_or_else(Rat::zero)
}

/// `floor(n / d)` for `d > 0`, without a float and without `num_integer`.
fn floor_div(numerator: &BigInt, denominator: &BigInt) -> BigInt {
    let quotient = numerator / denominator;
    let remainder = numerator % denominator;
    if remainder.is_negative() {
        quotient - 1
    } else {
        quotient
    }
}

fn ceil_div(numerator: &BigInt, denominator: &BigInt) -> BigInt {
    -floor_div(&(-numerator), denominator)
}

/// **Round one exact rational outward to the boundary grain.** Away from zero, so the boundary
/// value encloses the exact one, and the residual carries the difference exactly.
fn round_outward(value: &Rat, boundary_exponent: u32) -> (BigInt, Rat) {
    let scale = boundary_scale(boundary_exponent);
    let scaled = value * Rat::from(scale.clone());
    let rounded = if scaled.numer().is_negative() {
        floor_div(scaled.numer(), scaled.denom())
    } else {
        ceil_div(scaled.numer(), scaled.denom())
    };
    let at_boundary = Rat::new(rounded.clone(), scale);
    (rounded, value - at_boundary)
}

impl ReductionJunction {
    /// The face this junction presents to a [`crate::section_partition::SectionPartition`], so the
    /// partition owner never depends on this one.
    pub fn output_face(&self) -> JunctionOutput {
        JunctionOutput {
            owner: self.owner.clone(),
            output: self.output,
            partials: self.partials.len(),
        }
    }

    /// **Certify the junction.** Every failure is a named defect; nothing is asserted.
    pub fn certify(&self) -> Result<ReductionReceipt, Vec<ReductionDefect>> {
        let mut defects: Vec<ReductionDefect> = Vec::new();

        // ---- the word names the partials exactly once each ----------------------------------
        let mut leaves = self.word.leaves();
        let declared_leaves = leaves.clone();
        leaves.sort_unstable();
        let expected: Vec<usize> = (0..self.partials.len()).collect();
        if leaves != expected {
            defects.push(ReductionDefect::WordDisagrees {
                declared_leaves,
                partials: self.partials.len(),
            });
            return Err(defects);
        }

        // ---- the boundary is coarser than the carrier ----------------------------------------
        if self.boundary_exponent > self.carrier_exponent {
            defects.push(ReductionDefect::BoundaryFinerThanCarrier {
                carrier: self.carrier_exponent,
                boundary: self.boundary_exponent,
            });
        }

        // ---- the inner regions partition K ---------------------------------------------------
        //
        // Three checks, and the third exists because the first two can be defeated by the second:
        // a partial contracting coordinates the axis does not have used to be admitted, and its
        // foreign extent then covered the hole the sweep would have found. So every inner region is
        // checked to lie WITHIN the declared axis, and the sweep is taken over the regions **clipped
        // to the axis**, so a foreign extent can no longer suppress a hole.
        let inner: Vec<SectionRegion> = self.partials.iter().map(|partial| partial.inner).collect();
        let axis = self.inner_shape.whole();
        let mut clipped: Vec<SectionRegion> = Vec::with_capacity(inner.len());
        for (at, region) in inner.iter().enumerate() {
            if !region.within(&self.inner_shape) {
                defects.push(ReductionDefect::InnerOutsideAxis {
                    partial: self.partials[at].index,
                    region: *region,
                    shape: self.inner_shape,
                });
            }
            if let Some(met) = region.meet(&axis) {
                clipped.push(met);
            }
        }
        let mut inner_overlaps: Vec<(usize, usize, SectionRegion)> = Vec::new();
        for (a, left) in inner.iter().enumerate() {
            for (b, right) in inner.iter().enumerate().skip(a + 1) {
                if let Some(region) = left.meet(right) {
                    inner_overlaps.push((a, b, region));
                    defects.push(ReductionDefect::InnerOverlaps {
                        partials: (a, b),
                        region,
                    });
                }
            }
        }
        let inner_uncovered = uncovered_regions(&self.inner_shape, &clipped);
        for region in &inner_uncovered {
            defects.push(ReductionDefect::InnerUncovered { region: *region });
        }

        // ---- the charts and the metrics compose ----------------------------------------------
        if self.codomain_metric.rows() != self.output_dimension
            || !self.codomain_metric.is_square()
        {
            defects.push(ReductionDefect::MetricShape { partial: None });
        }
        for partial in &self.partials {
            if partial.chart.rows() != self.output_dimension
                || partial.chart.columns() != partial.carried.len()
            {
                defects.push(ReductionDefect::ChartShape {
                    partial: partial.index,
                    rows: partial.chart.rows(),
                    columns: partial.chart.columns(),
                    output_dimension: self.output_dimension,
                    carried: partial.carried.len(),
                });
            }
            if partial.domain_metric.rows() != partial.carried.len()
                || !partial.domain_metric.is_square()
            {
                defects.push(ReductionDefect::MetricShape {
                    partial: Some(partial.index),
                });
            }
        }
        if !defects.is_empty() {
            return Err(defects);
        }

        // ---- the leaves, in the output chart --------------------------------------------------
        let mut carried: Vec<Vec<Rat>> = Vec::with_capacity(self.partials.len());
        for partial in &self.partials {
            match partial.chart.apply(&partial.carried) {
                Ok(value) => carried.push(value),
                Err(error) => {
                    defects.push(ReductionDefect::Linear(error));
                    return Err(defects);
                }
            }
        }

        // ---- the declared word and its reversed control ---------------------------------------
        let declared = self.read_word(&self.word, &carried, self.policy, &mut defects);
        let reversed_word = self.word.reversed(self.partials.len());
        let reversed = self.read_word(&reversed_word, &carried, self.policy, &mut defects);
        let mut words_agree = true;
        for (at, (left, right)) in declared.value.iter().zip(&reversed.value).enumerate() {
            if left != right {
                words_agree = false;
                defects.push(ReductionDefect::WordsDisagree {
                    coordinate: at,
                    declared: left.clone(),
                    reversed: right.clone(),
                });
            }
        }

        // ---- the carried material stands at the DECLARED carrier grain ------------------------
        //
        // Taken here, after the word readings, so a junction that is wrong about both its carrier
        // and its aperture returns both defects rather than only the first. `carrier_exponent` was
        // compared with `boundary_exponent` and with nothing else, so both were declared numbers
        // with no material behind either — a partial carrying `1/3`, which is a dyadic at no
        // exponent whatever, was admitted at a declared carrier of `2^-4`.
        for partial in &self.partials {
            for (at, value) in partial.carried.iter().enumerate() {
                if !stands_at_grain(value, self.carrier_exponent) {
                    defects.push(ReductionDefect::CarrierGrainRefused {
                        partial: partial.index,
                        coordinate: at,
                        value: value.clone(),
                        carrier_exponent: self.carrier_exponent,
                    });
                }
            }
        }

        // ---- the roundings, COUNTED ------------------------------------------------------------
        //
        // The unit is **one `round_outward` invocation**, and the count is the total on the
        // certified path: one per output coordinate at the declared boundary, plus whatever the
        // policy took inside the tree, which under the admitted policy is none. It read the literal
        // `1` until 2026-08-19 — defensible as *one rounding per coordinate* and indefensible as a
        // field no declared input could move.
        let mut roundings = declared.roundings;
        let mut boundary_value: Vec<BigInt> = Vec::with_capacity(declared.value.len());
        let mut boundary_residual: Vec<Rat> = Vec::with_capacity(declared.value.len());
        for value in &declared.value {
            let (rounded, residual) = round_outward(value, self.boundary_exponent);
            roundings += 1;
            boundary_value.push(rounded);
            boundary_residual.push(residual);
        }

        // ---- exactly one rounding per coordinate, at the boundary ------------------------------
        if self.policy != RoundingPolicy::OnceAtBoundary {
            defects.push(ReductionDefect::RoundingNotAtBoundary { roundings });
        }

        // ---- the adjoint return into every partial chart ---------------------------------------
        let mut adjoints: Vec<AdjointReturn> = Vec::with_capacity(self.partials.len());
        for partial in &self.partials {
            match self.adjoint_of(partial) {
                Ok(adjoint) => {
                    if !adjoint.defect.is_zero() {
                        defects.push(ReductionDefect::AdjointDefect {
                            partial: partial.index,
                            defect: adjoint.defect.clone(),
                            residual: adjoint.residual.clone(),
                        });
                    }
                    adjoints.push(adjoint);
                }
                Err(error) => defects.push(ReductionDefect::Linear(error)),
            }
        }

        if !defects.is_empty() {
            return Err(defects);
        }

        // ---- the work, counted --------------------------------------------------------------
        let mut work = ExactWork::nothing();
        work.added(self.word.root.joins() as u64 * self.output_dimension as u64);
        work.multiplied(
            self.partials
                .iter()
                .map(|partial| (partial.chart.rows() * partial.chart.columns()) as u64)
                .sum(),
        );
        for value in &declared.value {
            work.wrote(value);
        }
        for node in &declared.nodes {
            for value in &node.value {
                work.wrote(value);
            }
        }
        work.resident(self.partials.len() as u64 * self.output_dimension as u64);
        for _ in 0..declared.dependency_span {
            work.stepped();
        }

        let partials: Vec<PartialReceipt> = self
            .partials
            .iter()
            .zip(&carried)
            .map(|(partial, in_output)| PartialReceipt {
                index: partial.index,
                inner: partial.inner,
                inner_extent: partial.inner.extent(),
                carried: partial.carried.clone(),
                enclosure: partial.enclosure.clone(),
                width_bits: widest(&partial.carried),
                chart: partial.chart.clone(),
                carried_width_bits: widest(in_output),
            })
            .collect();

        Ok(ReductionReceipt {
            schema: "holonic-engine.reduction-receipt.v1".to_owned(),
            owner: self.owner.clone(),
            output: self.output,
            output_dimension: self.output_dimension,
            partials,
            inner_uncovered,
            inner_overlaps,
            declared,
            reversed,
            words_agree,
            overflow_aperture: self.overflow_aperture,
            carrier_exponent: self.carrier_exponent,
            boundary_exponent: self.boundary_exponent,
            rounding: self.rounding,
            boundary_value,
            boundary_residual,
            roundings,
            adjoints,
            obstruction_lineage: Vec::new(),
            work,
        })
    }

    /// **Read one word over the partials, keeping every node's width.** Public so the control can
    /// read the same material under a policy the law refuses.
    pub fn read_word(
        &self,
        word: &ReductionWord,
        carried: &[Vec<Rat>],
        policy: RoundingPolicy,
        defects: &mut Vec<ReductionDefect>,
    ) -> WordReading {
        let mut nodes: Vec<NodeWidth> = Vec::new();
        let mut roundings = 0usize;
        let value = self.walk(&word.root, carried, policy, &mut nodes, &mut roundings, defects);
        let peak = nodes.iter().map(|node| node.width_bits).max().unwrap_or(0);
        for node in &nodes {
            if node.width_bits > self.overflow_aperture {
                defects.push(ReductionDefect::WidthExceedsAperture {
                    word: word.written(),
                    leaves: node.leaves.clone(),
                    width_bits: node.width_bits,
                    aperture: self.overflow_aperture,
                });
            }
        }
        WordReading {
            word: word.written(),
            leaves: word.leaves(),
            value,
            peak_width_bits: peak,
            dependency_span: word.root.span(),
            roundings,
            nodes,
        }
    }

    fn walk(
        &self,
        node: &ReductionNode,
        carried: &[Vec<Rat>],
        policy: RoundingPolicy,
        nodes: &mut Vec<NodeWidth>,
        roundings: &mut usize,
        defects: &mut Vec<ReductionDefect>,
    ) -> Vec<Rat> {
        match node {
            ReductionNode::Leaf(leaf) => {
                // A leaf naming no partial is a defect, never a fabricated zero. The zero below is
                // returned only so the walk can finish and report every further defect; a reading
                // whose defects are non-empty is not a value and `certify` refuses it.
                let value = match carried.get(*leaf) {
                    Some(value) => value.clone(),
                    None => {
                        defects.push(ReductionDefect::UnknownLeaf {
                            leaf: *leaf,
                            partials: carried.len(),
                        });
                        vec![Rat::zero(); self.output_dimension]
                    }
                };
                nodes.push(NodeWidth {
                    leaves: vec![*leaf],
                    width_bits: widest(&value),
                    depth: 0,
                    value: value.clone(),
                });
                value
            }
            ReductionNode::Join(left, right) => {
                let left_value = self.walk(left, carried, policy, nodes, roundings, defects);
                let right_value = self.walk(right, carried, policy, nodes, roundings, defects);
                let mut value: Vec<Rat> = left_value
                    .iter()
                    .zip(&right_value)
                    .map(|(a, b)| a + b)
                    .collect();
                if policy == RoundingPolicy::AtEveryNode {
                    // The control: rounding here rather than at the boundary. Every join costs one
                    // rounding, and the two words stop agreeing.
                    value = value
                        .iter()
                        .map(|coordinate| {
                            let (rounded, _) = round_outward(coordinate, self.boundary_exponent);
                            Rat::new(rounded, boundary_scale(self.boundary_exponent))
                        })
                        .collect();
                    *roundings += 1;
                }
                nodes.push(NodeWidth {
                    leaves: node.leaves(),
                    width_bits: widest(&value),
                    depth: node.span(),
                    value: value.clone(),
                });
                value
            }
        }
    }

    /// `T_a^* = G_X^-1 T_a^T G_Y` from `exact_linear`, its return `ybar_a`, and its **operator**
    /// residual — together with the residual a bare transpose would have left under the same
    /// declared metrics.
    ///
    /// The characterization is `<T x, y>_Y = <x, T^dagger y>_X` for **every** `x` and `y`, which in
    /// coordinates is `x^T T^T G_Y y = x^T G_X T^dagger y` for every `x, y`, hence the matrix
    /// identity `G_X T^dagger = T^T G_Y`. Its residual is what this returns. Reading it at one
    /// authored probe pair — which is what stood here — samples a bilinear form at a single point
    /// and can vanish while the operator identity fails; the operator residual cannot.
    fn adjoint_of(&self, partial: &PartialTerm) -> Result<AdjointReturn, ExactLinearError> {
        let adjoint = partial
            .chart
            .metric_adjoint(&partial.domain_metric, &self.codomain_metric)?;
        let returned = adjoint.apply(&self.returned_covector)?;
        let transpose = partial.chart.transpose()?;
        let carried = transpose.multiply(&self.codomain_metric)?;
        let residual = partial.domain_metric.multiply(&adjoint)?.subtract(&carried)?;
        let bare_transpose_residual = partial
            .domain_metric
            .multiply(&transpose)?
            .subtract(&carried)?;
        let defect = widest_entry(&residual);
        let bare_transpose_defect = widest_entry(&bare_transpose_residual);
        Ok(AdjointReturn {
            partial: partial.index,
            adjoint,
            returned,
            residual,
            defect,
            bare_transpose_residual,
            bare_transpose_defect,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    fn rat(numerator: i64, denominator: i64) -> Rat {
        Rat::new(BigInt::from(numerator), BigInt::from(denominator))
    }

    fn matrix(rows: &[&[(i64, i64)]]) -> ExactRatMatrix {
        ExactRatMatrix::new(
            rows.iter()
                .map(|row| row.iter().map(|(n, d)| rat(*n, *d)).collect())
                .collect(),
        )
        .expect("well-formed")
    }

    fn region(from: usize, to: usize) -> SectionRegion {
        SectionRegion::new(0, 1, from, to).expect("well-formed")
    }

    /// Five partials over a scalar output, at **dyadic** values that stand exactly at the declared
    /// carrier grain `2^-4`, chosen so the two words accumulate to different widths on the same
    /// material.
    ///
    /// It carried `1/3` until 2026-08-19, which stands at no dyadic grain whatever and was admitted
    /// only because the carrier was compared with the boundary and with nothing else.
    fn scalar_partials() -> Vec<PartialTerm> {
        let values = [rat(1, 1), rat(1, 1), rat(3, 4), rat(1, 8), rat(1, 8)];
        values
            .iter()
            .enumerate()
            .map(|(index, value)| PartialTerm {
                index,
                inner: region(index, index + 1),
                carried: vec![value.clone()],
                enclosure: vec![(value.clone(), value.clone())],
                chart: ExactRatMatrix::identity(1).expect("identity"),
                domain_metric: ExactRatMatrix::identity(1).expect("identity"),
            })
            .collect()
    }

    fn scalar_junction(aperture: u64, policy: RoundingPolicy) -> ReductionJunction {
        let partials = scalar_partials();
        ReductionJunction {
            owner: "control".to_owned(),
            output: SectionRegion::new(0, 1, 0, 1).expect("well-formed"),
            output_dimension: 1,
            inner_shape: SectionShape::of(1, partials.len(), 0),
            word: ReductionWord::left_leaning(partials.len()).expect("a word"),
            partials,
            overflow_aperture: aperture,
            carrier_exponent: 4,
            boundary_exponent: 2,
            rounding: DirectedRounding::Outward,
            policy,
            codomain_metric: ExactRatMatrix::identity(1).expect("identity"),
            returned_covector: vec![rat(1, 1)],
        }
    }

    // ---------------------------------------------------------------------------------------
    // CONTROL 5 — the word and its reversed control agree on the value and carry both widths
    // ---------------------------------------------------------------------------------------

    #[test]
    fn control_five_the_word_and_its_reversed_control_agree_and_carry_both_widths() {
        let junction = scalar_junction(64, RoundingPolicy::OnceAtBoundary);
        let receipt = junction.certify().expect("the junction certifies");
        assert!(receipt.words_agree);
        assert_eq!(receipt.declared.value, receipt.reversed.value);
        // 1 + 1 + 3/4 + 1/8 + 1/8 = 3.
        assert_eq!(receipt.declared.value, vec![rat(3, 1)]);
        // Every node of both words carries a width.
        assert_eq!(receipt.declared.nodes.len(), 9);
        assert_eq!(receipt.reversed.nodes.len(), 9);
        // And the widths DIFFER: the declared word accumulates 23/8, the reversed one never exceeds
        // 3. Value is forced by exactness; width is not, and it is the evidence.
        assert_eq!(receipt.declared.peak_width_bits, 9);
        assert_eq!(receipt.reversed.peak_width_bits, 5);
        assert_ne!(receipt.declared.peak_width_bits, receipt.reversed.peak_width_bits);
        // One rounding per output coordinate, at the boundary, and the count is taken rather than
        // written down: a scalar output performs one `round_outward`.
        assert_eq!(receipt.roundings, 1);
        assert_eq!(receipt.declared.roundings, 0);
        assert_eq!(receipt.boundary_value, vec![BigInt::from(12)]);
        assert_eq!(receipt.boundary_residual, vec![rat(0, 1)]);
    }

    /// **Perturbation A: the overflow aperture is set one bit below the widest node.** The reading
    /// refuses and names the node; nothing wraps and nothing is clipped.
    #[test]
    fn control_five_perturbed_a_narrow_aperture_refuses_rather_than_wrapping() {
        let junction = scalar_junction(8, RoundingPolicy::OnceAtBoundary);
        let defects = junction
            .certify()
            .expect_err("a node above the aperture refuses");
        let named = defects.iter().find_map(|defect| match defect {
            ReductionDefect::WidthExceedsAperture {
                leaves, width_bits, ..
            } => Some((leaves.clone(), *width_bits)),
            _ => None,
        });
        let (leaves, width) = named.expect("the aperture defect names its node");
        assert_eq!(width, 9);
        assert_eq!(leaves, vec![0, 1, 2, 3]);
    }

    /// **Perturbation B: rounding moves from the boundary to every node.** The law refuses the
    /// policy, and the same material read under it makes the two words disagree in value — which is
    /// what shows the value control is about the rounding rather than about arithmetic.
    #[test]
    fn control_five_perturbed_rounding_at_every_node_is_refused_and_breaks_the_agreement() {
        let junction = scalar_junction(64, RoundingPolicy::AtEveryNode);
        let defects = junction.certify().expect_err("the policy is refused");
        assert!(defects.iter().any(|defect| matches!(
            defect,
            ReductionDefect::RoundingNotAtBoundary { .. }
        )));
        // And the values genuinely part company under it.
        let carried: Vec<Vec<Rat>> = junction
            .partials
            .iter()
            .map(|partial| partial.carried.clone())
            .collect();
        let mut ignored = Vec::new();
        let declared = junction.read_word(
            &junction.word,
            &carried,
            RoundingPolicy::AtEveryNode,
            &mut ignored,
        );
        let reversed = junction.read_word(
            &junction.word.reversed(junction.partials.len()),
            &carried,
            RoundingPolicy::AtEveryNode,
            &mut ignored,
        );
        assert_ne!(declared.value, reversed.value);
        assert_eq!(declared.roundings, 4);
    }

    // ---------------------------------------------------------------------------------------
    // CONTROL 6 — the adjoint reaches every partial chart under a declared metric
    // ---------------------------------------------------------------------------------------

    /// A two-dimensional output with a genuinely non-identity declared codomain metric, and two
    /// partials with different charts.
    fn charted_junction() -> ReductionJunction {
        let first = PartialTerm {
            index: 0,
            inner: region(0, 2),
            carried: vec![rat(3, 1), rat(-1, 1)],
            enclosure: vec![(rat(3, 1), rat(3, 1)), (rat(-1, 1), rat(-1, 1))],
            chart: matrix(&[&[(1, 1), (0, 1)], &[(0, 1), (1, 1)]]),
            domain_metric: ExactRatMatrix::identity(2).expect("identity"),
        };
        let second = PartialTerm {
            index: 1,
            inner: region(2, 4),
            carried: vec![rat(1, 2), rat(2, 1)],
            enclosure: vec![(rat(1, 2), rat(1, 2)), (rat(2, 1), rat(2, 1))],
            // A declared rebase rather than an identity embedding.
            chart: matrix(&[&[(2, 1), (1, 3)], &[(0, 1), (5, 2)]]),
            domain_metric: matrix(&[&[(1, 1), (0, 1)], &[(0, 1), (7, 2)]]),
        };
        ReductionJunction {
            owner: "control".to_owned(),
            output: SectionRegion::new(0, 1, 0, 2).expect("well-formed"),
            output_dimension: 2,
            inner_shape: SectionShape::of(1, 4, 0),
            word: ReductionWord::balanced(2).expect("a word"),
            partials: vec![first, second],
            overflow_aperture: 128,
            carrier_exponent: 8,
            boundary_exponent: 3,
            rounding: DirectedRounding::Outward,
            policy: RoundingPolicy::OnceAtBoundary,
            // G_Y is NOT the identity, and it is declared.
            codomain_metric: matrix(&[&[(1, 1), (0, 1)], &[(0, 1), (3, 1)]]),
            returned_covector: vec![rat(1, 1), rat(-2, 1)],
        }
    }

    #[test]
    fn control_six_the_adjoint_reaches_every_partial_chart_with_zero_defect() {
        let junction = charted_junction();
        let receipt = junction.certify().expect("the junction certifies");
        assert_eq!(receipt.adjoints.len(), junction.partials.len());
        for adjoint in &receipt.adjoints {
            // exact_linear::adjoint_defect is exactly zero for G_X^-1 T^T G_Y.
            assert!(adjoint.defect.is_zero());
            assert_eq!(adjoint.returned.len(), junction.partials[adjoint.partial].carried.len());
        }
        // The second partial's chart is a rebase, so the adjoint carries the covector into a
        // genuinely different chart.
        assert_ne!(receipt.adjoints[0].returned, receipt.adjoints[1].returned);
    }

    /// **Perturbation: the bare transpose is claimed as the adjoint under a non-identity metric.**
    /// `exact_linear::adjoint_defect` exhibits a nonzero defect, and the receipt already carries it
    /// beside every adjoint, so the metric is visibly load-bearing.
    #[test]
    fn control_six_perturbed_a_bare_transpose_under_a_declared_metric_exhibits_a_defect() {
        let junction = charted_junction();
        let receipt = junction.certify().expect("the junction certifies");
        // At least one partial's bare transpose is refuted by the declared metrics.
        assert!(receipt
            .adjoints
            .iter()
            .any(|adjoint| !adjoint.bare_transpose_defect.is_zero()));
        // And the claim is checked the same way the law checks its own: through exact_linear.
        let partial = &junction.partials[1];
        let transpose = partial.chart.transpose().expect("transpose");
        let defect = partial
            .chart
            .adjoint_defect(
                &transpose,
                &partial.domain_metric,
                &junction.codomain_metric,
                &[rat(1, 1), rat(1, 1)],
                &junction.returned_covector,
            )
            .expect("defect");
        assert!(!defect.is_zero());
    }

    // ---------------------------------------------------------------------------------------
    // the inner partition, certified by the same computation as the output partition
    // ---------------------------------------------------------------------------------------

    #[test]
    fn an_inner_region_no_partial_contracts_refuses_by_name() {
        let mut junction = scalar_junction(64, RoundingPolicy::OnceAtBoundary);
        junction.inner_shape = SectionShape::of(1, 7, 0);
        let defects = junction.certify().expect_err("K is not covered");
        let named = defects.iter().find_map(|defect| match defect {
            ReductionDefect::InnerUncovered { region } => Some(*region),
            _ => None,
        });
        assert_eq!(named, Some(region(5, 7)));
    }

    #[test]
    fn the_outward_rounding_encloses_and_the_residual_opposes_the_hand() {
        // 5/8 at a boundary grain of 2^-2: outward gives 3/4, residual 5/8 - 3/4 = -1/8.
        let (rounded, residual) = round_outward(&rat(5, 8), 2);
        assert_eq!(rounded, BigInt::from(3));
        assert_eq!(residual, rat(-1, 8));
        let (rounded, residual) = round_outward(&rat(-5, 8), 2);
        assert_eq!(rounded, BigInt::from(-3));
        assert_eq!(residual, rat(1, 8));
    }

    #[test]
    fn the_reversed_control_is_the_same_shape_over_reversed_leaves() {
        let word = ReductionWord::left_leaning(4).expect("a word");
        assert_eq!(word.written(), "(((0 + 1) + 2) + 3)");
        assert_eq!(word.reversed(4).written(), "(((3 + 2) + 1) + 0)");
    }
}
