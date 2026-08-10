//! The Tschirnhaus organ: transport a polynomial of **any** degree to another chart, exhibit the
//! transport, and refuse — with the obstruction named — when the target chart cannot represent the
//! answer.
//!
//! `canon/TABLET_THE_CHART.md:280` states the construction this organ was first built for:
//!
//! > *"a Tschirnhaus organ. Take a degree-5 input, transport it to Bring form by an exact rational
//! > chart change, return the transported form and the transport, and refuse — with the obstruction
//! > named — when the target chart cannot represent the answer."*
//!
//! and §3.4 states why it matters: **the quintic is solvable; it is not solvable *in the radical
//! chart*.** Galois theory does not say "unsolvable". It says "not in this chart" and hands you the
//! obstruction. Everything below is built so that a refusal is a *return carrying evidence* and
//! never a bool, never a panic, and never a tolerance.
//!
//! ## The degree is a rung, not a category
//!
//! Until 2026-08-09 this organ carried `const QUINTIC_DEGREE: usize = 5` and refused anything else
//! at its first gate. `canon/THE_CONTAMINANT_PROTOCOL.md` §2.6 names the species and why lifting it
//! is not hygiene: **the restriction deletes the mechanism the organ exists to demonstrate.** The
//! radical chart's refusal at degree five is a statement only against the degrees where it does not
//! refuse — a quartic runs the whole family and the radical chart **returns**, because `S_n` is
//! solvable exactly for `n <= 4`. An organ that only ever saw degree five could not exhibit that
//! contrast and therefore could not state its own theorem.
//!
//! ## What a chart is here, and what a transport is
//!
//! A Tschirnhaus transform is an element `g` of `Q[x]/(f)`. It carries the root population
//! `{x_1..x_n}` of `f` to `{g(x_1)..g(x_n)}`, whose monic polynomial is
//!
//! ```text
//!   F(y) = prod_i (y - g(x_i))  =  Res_x( f(x), y - g(x) )
//! ```
//!
//! No root is ever computed. `F` is obtained from the power sums of `f` by the Newton identities:
//! `p_k = sum_i g(x_i)^k = sum_m [g^k]_m * s_m`, where `[g^k]_m` is the ordinary `m`-th coefficient
//! of the `k`-th power of `g` **as a polynomial**, and `s_m` are `f`'s own power sums. That identity
//! is why the whole organ needs no modular reduction and no linear algebra: raising a polynomial to
//! a power and pairing it against a fixed vector is the entire transport. It is also why the organ
//! is degree-general underneath — `s_0` is the degree and appears nowhere as a literal.
//!
//! The resultant is then computed **again, independently**, by fraction-free Bareiss elimination on
//! the Sylvester matrix over `Q[y]`, and the two must agree coefficient for coefficient. Two
//! independent implementations of the same object, per `CLAUDE.md` §8, with both work vectors
//! reported. A third, sharper check runs alongside: `F(g(x))` reduced modulo `f(x)` must be
//! **identically zero** — that is the transport verified by literal substitution, over `Q`.
//!
//! ## The chart family at general degree `n`, and where each one refuses
//!
//! ```text
//!   depressed   kill x^(n-1)                      a rational shift          ALWAYS returns over Q
//!   principal   kill x^(n-1), x^(n-2)             one auxiliary QUADRATIC   returns iff it has a
//!                                                                           rational root
//!   Bring       kill x^(n-1), x^(n-2), x^(n-3)    eliminate one parameter   returns iff the
//!                                                                           resultant has a
//!                                                                           rational root whose
//!                                                                           partner is also
//!                                                                           rational
//!   radical     write the roots                   the monodromy population  refuses when the
//!                                                                           observed sections
//!                                                                           refute solvability
//! ```
//!
//! **A chart killing `k` coefficients needs `n >= k + 1`, and this is derived rather than
//! declared.** The killed set is `x^(n-1) .. x^(n-k)`; if it reached `x^0` the constant term would
//! be zero, which forces a root at the origin, and killing every coefficient below the leading one
//! forces *all* roots to the origin. So the chart is not defined below its own rung and
//! [`ChartObstructionSpecies::ChartUndefinedAtDegree`] says so by name — a cubic has no Bring
//! chart, and that is a fact about degree three rather than a failure of the organ.
//!
//! **The Bring chart is not vacuous and the witness is worth stating.** `x^5 - 2x^3 + x - 1` has for
//! its roots the *squares* of the roots of `y^5 - y - 1`: if `y^5 = y + 1` and `x = y^2` then
//! `x^3 - x = y^6 - y^2 = y(y+1) - y^2 = y`. So the cubic transform `g = x^3 - x` carries it back to
//! Bring form exactly, over `Q`, with no radical anywhere — while its Galois group is still `S_5`
//! and the radical chart still refuses. That is `canon/TABLET_THE_CHART.md` §3.4's sentence as a
//! computation: **not unsolvable, unsolvable in that chart.**
//!
//! The depressed step is a shift and always succeeds. The principal step needs a root of a
//! quadratic in the transform parameter, so it is rational exactly when that quadratic's
//! discriminant is a square in `Q` — and when it is not, the organ returns the quadratic, the
//! discriminant, the Sturm certificate for each of its real roots, and the complete (empty)
//! rational-root population. **That is what "the target chart cannot represent the answer" is
//! supposed to look like.**
//!
//! ## The cost law the ladder carries, exhibited rather than commented
//!
//! For a Tschirnhaus transform of degree `k` killing the top `k` coefficients, `p_1 = 0` is linear
//! and solves for `c_0`, leaving `k-1` homogeneous conditions of degrees `2, 3, ..., k` on the
//! projective parameter space `P^(k-1)`. By Bezout they meet in
//!
//! ```text
//!   2 * 3 * ... * k  =  k!     points,   radicals of degree at most k
//! ```
//!
//! `k = 1` gives `1` — the depressed shift is unique and always rational. `k = 2` gives `2`, one
//! square root. `k = 3` gives `6 = 2 * 3`, which is exactly why the classical Bring reduction costs
//! a square root **and** a cube root. [`TschirnhausCost`] returns this as a figure, and the Bring
//! chart holds its own eliminant's degree against it — a bound that can fail, on material the organ
//! computes.
//!
//! ## The declared transform aperture, and the defect that writing it down exposed
//!
//! `CLAUDE.md` §8: *"An organ used past its declared aperture is a defect even when it appears to
//! return."* The vanishing conditions are **homogeneous** in the transform's coefficients — degrees
//! 1, 2 and 3 — so the parameter space is a projective space and not an affine one. The apertures:
//!
//! - **principal chart**: transforms of degree at most two up to scale, `[c_1 : c_2]` in `P^1` once
//!   `c_0` is eliminated by `p_1 = 0`. **Both** affine sub-charts are searched, `c_2 = 0` (linear)
//!   and `c_2 = 1` (quadratic), lowest transform degree first.
//! - **Bring chart**: transforms of degree at most three up to scale, `[c_1 : c_2 : c_3]` in `P^2`.
//!   All three affine sub-charts are searched: `c_3 = c_2 = 0` (linear), `c_3 = 0` (quadratic), and
//!   `c_3 = 1` (cubic, where `c_1` is eliminated by a resultant).
//!
//! **Searching one affine patch was this organ's first real defect and it was found by measuring,
//! not by reading.** Pinning `c_2 = 1` silently excludes the point at infinity, which is exactly the
//! linear transform — and for a source *already* in principal form the linear transform is the only
//! solution. `x^5 - x - 1` therefore came back as `AuxiliaryHasNoRoot` when the correct return is
//! the identity: the source is already principal, already Bring, and nothing needed solving. **A
//! chart that refuses because its own coordinate patch missed the answer has reported an obstruction
//! that does not exist**, which is the worst thing an obstruction organ can do. The aperture string
//! is now carried on every returned transport so a later reader sees it without reading this
//! comment.
//!
//! ## What this does not claim
//!
//! Nothing here bears on Abel–Ruffini, on the Hodge conjecture, or on any Millennium statement.
//! `CLAUDE.md` §3: a deed may be graded by movement on named substructure without claiming the
//! conjecture. The radical chart's verdict is a statement about a **declared receiver family** —
//! rational factorisation, binomial recognition, and Frobenius cycle types up to a declared prime
//! limit — and that family's own blindness is reported as part of the return, not hidden by it.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::arithmetic_fiber::ArithmeticFiberEvent;
use crate::arithmetic_monodromy::{
    ArithmeticMonodromyError, ArithmeticMonodromyEvent, ArithmeticMonodromyLaw,
    ArithmeticMonodromyStanding, IntegralQuinticProblem, QuinticIrreducibility,
    QuinticTransitiveGroup, SolvabilityConstraint, catalogued_transitive_degree,
};
use crate::causal::EventId;
use crate::rational_polynomial::{
    BivariatePolynomial, CensusWork, ExactPolynomialError, RationalPolynomial, RationalRootCensus,
    ResultantWork, monic_from_power_sums, newton_power_sums, rational_root_census,
    resultant_in_eliminated_variable,
};
use crate::world::CausalWorld;

const CHART_PROBLEM_EVENT: EventId = EventId(1_000_000_000);

/// The degree at and below which `S_n` is solvable, so the radical chart returns.
///
/// **MATERIAL, and the theorem is Abel–Ruffini.** `S_n` is solvable exactly for `n <= 4`:
/// `S_1`, `S_2`, `S_3` and `S_4` have derived series reaching the trivial group, while `A_5` is
/// simple and non-abelian, so `S_n` for `n >= 5` does not. This is the one number in this organ
/// that does **not** move with the degree, and lifting the degree pin is precisely what makes it
/// visible: at `n <= 4` the radical chart returns and at `n >= 5` it may refuse.
const SOLVABLE_SYMMETRIC_DEGREE: usize = 4;

/// The charts this organ owns. Named by mechanism, never by ordinal.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub enum QuinticChart {
    /// Write the roots as nested radicals.
    Radical,
    /// Kill the fourth-degree coefficient.
    Depressed,
    /// Kill the fourth- and third-degree coefficients.
    Principal,
    /// Kill the fourth-, third- and second-degree coefficients: Bring–Jerrard form `y^5 + py + q`.
    Bring,
}

impl QuinticChart {
    /// The three transporting charts, in the order the atlas reads them.
    pub const TRANSPORTING: [Self; 3] = [Self::Depressed, Self::Principal, Self::Bring];

    pub fn name(self) -> &'static str {
        match self {
            Self::Radical => "radical",
            Self::Depressed => "depressed",
            Self::Principal => "principal",
            Self::Bring => "bring",
        }
    }

    /// How many coefficients below the leading one this chart kills. This **is** the degree of the
    /// Tschirnhaus transform it needs, because `k` homogeneous conditions on the transform's
    /// coefficients cut a point population out of `P^(k-1)` only when the transform has `k+1`
    /// coefficients.
    pub fn killed_count(self) -> usize {
        match self {
            Self::Radical => 0,
            Self::Depressed => 1,
            Self::Principal => 2,
            Self::Bring => 3,
        }
    }

    /// The lowest source degree at which this chart is defined at all.
    ///
    /// Killing `x^(n-1) .. x^(n-k)` must leave the constant term alive: `n - k >= 1`. A chart whose
    /// killed set reached `x^0` would force every root to the origin, which is a degeneration and
    /// not a chart. Hence `n >= k + 1`, and the radical chart — which kills nothing — is defined
    /// wherever a discriminant is, at `n >= 2`.
    pub fn least_source_degree(self) -> usize {
        (self.killed_count() + 1).max(2)
    }

    /// The coefficients this chart's transported form must carry as exact zero, at this degree.
    ///
    /// `[n-1, n-2, ..., n-k]`, descending. Empty when the chart is not defined at this degree.
    pub fn killed_degrees(self, source_degree: usize) -> Vec<usize> {
        if source_degree < self.least_source_degree() {
            return Vec::new();
        }
        (0..self.killed_count())
            .map(|offset| source_degree - 1 - offset)
            .collect()
    }

    /// The Bezout cost of entering this chart, computed rather than commented.
    pub fn cost(self) -> TschirnhausCost {
        tschirnhaus_cost(self.killed_count())
    }
}

/// What a Tschirnhaus transform of degree `k` costs, by Bezout, at **any** source degree.
///
/// `p_1 = 0` is homogeneous of degree one and solves linearly for `c_0`. What remains is `k-1`
/// homogeneous conditions of degrees `2, 3, ..., k` on the projective parameter space `P^(k-1)` of
/// `[c_1 : ... : c_k]`, and Bezout's theorem counts their common zeros with multiplicity as the
/// product of the degrees.
///
/// **The source degree does not appear.** That is the content: the cost of the chart change is a
/// property of the *transform*, not of the polynomial it acts on, which is why the same six-point
/// count governs Bring reduction at every rung.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TschirnhausCost {
    /// `k`, the transform's degree and the number of coefficients killed.
    pub transform_degree: usize,
    /// `[2, 3, ..., k]`, the homogeneous degrees of the conditions that survive eliminating `c_0`.
    pub condition_degrees: Vec<usize>,
    /// `k - 1`, the dimension of the projective parameter space the conditions live on.
    pub parameter_space_dimension: usize,
    /// `2 * 3 * ... * k = k!`, the Bezout number.
    pub bezout_number: BigUint,
    /// The largest radical degree the classical solution of those conditions can require, which is
    /// the largest condition degree — `1` when there is no condition left to solve.
    pub maximum_radical_degree: usize,
}

impl TschirnhausCost {
    /// `k!` written as its own factorisation, which is the sentence the header states at `k = 3`.
    pub fn written(&self) -> String {
        if self.condition_degrees.is_empty() {
            return format!(
                "k = {}: no condition survives eliminating c_0, so the transform is unique and \
                 rational — Bezout number 1",
                self.transform_degree
            );
        }
        format!(
            "k = {}: conditions of degrees {} on P^{}, meeting in {} = {} points by Bezout; \
             radicals of degree at most {}",
            self.transform_degree,
            self.condition_degrees
                .iter()
                .map(usize::to_string)
                .collect::<Vec<_>>()
                .join(" * "),
            self.parameter_space_dimension,
            self.condition_degrees
                .iter()
                .map(usize::to_string)
                .collect::<Vec<_>>()
                .join(" * "),
            self.bezout_number,
            self.maximum_radical_degree
        )
    }
}

/// The Bezout cost of a Tschirnhaus transform of degree `k`, at any `k`.
pub fn tschirnhaus_cost(transform_degree: usize) -> TschirnhausCost {
    let condition_degrees = (2..=transform_degree).collect::<Vec<_>>();
    let bezout_number = condition_degrees
        .iter()
        .fold(BigUint::one(), |product, degree| {
            product * BigUint::from(*degree)
        });
    TschirnhausCost {
        transform_degree,
        parameter_space_dimension: transform_degree.saturating_sub(1),
        maximum_radical_degree: condition_degrees.iter().copied().max().unwrap_or(1),
        condition_degrees,
        bezout_number,
    }
}

/// The exact certificate that a returned transport really carries the source to the returned form.
///
/// Three independent statements, none of them an assertion about the code that produced them:
/// the substitution residue, the Sylvester resultant, and the discriminant pair.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct TransportCertificate {
    /// `F(g(x))` reduced modulo `f(x)`, over `Q`. Zero, or the transport is not what it claims.
    pub substitution_residue: RationalPolynomial,
    pub substitution_vanishes: bool,
    /// `Res_x(f(x), y - g(x))`, computed independently by fraction-free Bareiss over `Q[y]`.
    pub resultant_form: RationalPolynomial,
    pub resultant_agrees: bool,
    pub source_discriminant: Rat,
    pub transported_discriminant: Rat,
    /// False exactly when the transform identifies two roots of the source.
    pub roots_stay_apart: bool,
    pub newton_work: CensusWork,
    pub resultant_work: ResultantWork,
}

impl TransportCertificate {
    pub fn holds(&self) -> bool {
        self.substitution_vanishes && self.resultant_agrees
    }
}

/// A chart transport that returned: the transported form, and the transport itself.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChartTransport {
    pub chart: QuinticChart,
    /// The source degree this transport ran at. A transport with no degree on it cannot be read.
    pub source_degree: usize,
    pub source: RationalPolynomial,
    /// The Tschirnhaus transform `g`, exactly, ascending in degree.
    pub transport: RationalPolynomial,
    pub transported: RationalPolynomial,
    /// Which coefficients this chart promised to kill, and their exact returned values.
    pub killed: BTreeMap<usize, Rat>,
    pub aperture: String,
    /// The Bezout cost of this chart's transform degree, at this rung. Independent of the source
    /// degree, which is the point.
    pub cost: TschirnhausCost,
    pub certificate: TransportCertificate,
    /// Populated when the chart had to solve for a parameter: the auxiliary polynomial, and the
    /// rational root it took.
    pub auxiliary: Vec<AuxiliaryStep>,
}

/// One parameter the chart had to solve for, with the polynomial that decided it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct AuxiliaryStep {
    pub parameter: String,
    pub auxiliary: RationalPolynomial,
    pub census: RationalRootCensus,
    pub taken: Rat,
    /// Present for a degree-two auxiliary: the classical `B^2 - 4AC` whose rational-square status
    /// is exactly the obstruction.
    pub quadratic_discriminant: Option<Rat>,
}

/// Why a chart could not be entered. Every species carries the evidence that refused it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ChartObstructionSpecies {
    /// The radical chart. The observed monodromy refutes solvability, so no stack of
    /// one-winding-at-a-time forgettings reaches the roots.
    NonSolvableMonodromy {
        /// **Degree five only.** Every transitive group the catalogue still admits; empty at every
        /// other degree, where the catalogue does not apply.
        admitted: BTreeSet<QuinticTransitiveGroup>,
        irreducibility: QuinticIrreducibility,
        /// The degree-general criterion that refused, with its witness prime and cycle type.
        solvability: SolvabilityConstraint,
        /// The obstruction, named.
        named: String,
    },
    /// The chart is not defined at this source degree, and the reason is a fact about the degree.
    ///
    /// Killing `k` coefficients below the leading one requires `n >= k + 1`; otherwise the killed
    /// set reaches the constant term and forces every root to the origin. A cubic has no Bring
    /// chart in the same way a point has no tangent line: nothing failed.
    ChartUndefinedAtDegree {
        source_degree: usize,
        killed_count: usize,
        least_source_degree: usize,
    },
    /// The eliminant the Bring chart produced exceeds the Bezout number its own transform degree
    /// allows. This is the cost law firing as a falsifier, not a resource refusal.
    EliminantExceedsBezoutBound {
        eliminant_degree: usize,
        cost: TschirnhausCost,
    },
    /// The chart change needs a root of `auxiliary`, and `auxiliary` has none in `Q`. The complete
    /// census is carried: the real roots exist and are certified, they are simply not rational.
    AuxiliaryRootNotRational {
        parameter: String,
        auxiliary: RationalPolynomial,
        census: RationalRootCensus,
        /// Present for a degree-two auxiliary: the quantity whose square root the chart wanted.
        quadratic_discriminant: Option<Rat>,
    },
    /// The eliminated parameter came out rational and its partner did not. Retained per value:
    /// the chart got half of the way in and the half is exhibited.
    PartnerNotRational {
        retained_parameter: String,
        retained_value: Rat,
        partner_parameter: String,
        partner_auxiliary: RationalPolynomial,
        census: RationalRootCensus,
    },
    /// The resultant vanished identically: the two conditions share a component, so elimination
    /// returns no finite candidate population at all.
    EliminationDegenerate { eliminated_parameter: String },
    /// The auxiliary polynomial is a nonzero constant: the chart's parameter has no value at all.
    AuxiliaryHasNoRoot {
        parameter: String,
        auxiliary: RationalPolynomial,
    },
    /// A candidate transform identified two roots of the source, so the transported quintic is not
    /// a chart of the same root population.
    TransportCollapsesRoots {
        transport: RationalPolynomial,
        transported_discriminant: Rat,
    },
    /// The declared transform aperture cannot express what the chart needs.
    OutsideTransformAperture { declared: String, reason: String },
}

/// A refusal, as a first-class return.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ChartObstruction {
    pub chart: QuinticChart,
    /// Which step of the chart change refused.
    pub step: String,
    pub species: ChartObstructionSpecies,
}

impl ChartObstruction {
    pub fn written(&self) -> String {
        let detail = match &self.species {
            ChartObstructionSpecies::NonSolvableMonodromy {
                admitted, named, ..
            } => format!(
                "non-solvable monodromy; admitted {}; obstruction: {named}",
                written_groups(admitted)
            ),
            ChartObstructionSpecies::ChartUndefinedAtDegree {
                source_degree,
                killed_count,
                least_source_degree,
            } => format!(
                "killing {killed_count} coefficients below the leading one needs degree at least \
                 {least_source_degree}; at degree {source_degree} the killed set reaches the \
                 constant term and forces every root to the origin"
            ),
            ChartObstructionSpecies::EliminantExceedsBezoutBound {
                eliminant_degree,
                cost,
            } => format!(
                "the eliminant has degree {eliminant_degree}, above the Bezout number {} — {}",
                cost.bezout_number,
                cost.written()
            ),
            ChartObstructionSpecies::AuxiliaryRootNotRational {
                parameter,
                auxiliary,
                census,
                quadratic_discriminant,
            } => {
                let discriminant = quadratic_discriminant
                    .as_ref()
                    .map(|value| format!("; needs sqrt({value})"))
                    .unwrap_or_default();
                format!(
                    "{parameter} needs a root of {} [{} real, {} rational]{discriminant}",
                    auxiliary.written(parameter),
                    census.distinct_real_roots,
                    census.rational_roots.len()
                )
            }
            ChartObstructionSpecies::PartnerNotRational {
                retained_parameter,
                retained_value,
                partner_parameter,
                partner_auxiliary,
                census,
            } => format!(
                "{retained_parameter} = {retained_value} is rational but {partner_parameter} is not: \
                 {} has {} real and {} rational roots",
                partner_auxiliary.written(partner_parameter),
                census.distinct_real_roots,
                census.rational_roots.len()
            ),
            ChartObstructionSpecies::EliminationDegenerate {
                eliminated_parameter,
            } => format!("elimination of {eliminated_parameter} vanished identically"),
            ChartObstructionSpecies::AuxiliaryHasNoRoot {
                parameter,
                auxiliary,
            } => format!(
                "{parameter} has no value: {} is a nonzero constant",
                auxiliary.written(parameter)
            ),
            ChartObstructionSpecies::TransportCollapsesRoots {
                transport,
                transported_discriminant,
            } => format!(
                "the transform {} identifies two roots (transported discriminant {transported_discriminant})",
                transport.written("x")
            ),
            ChartObstructionSpecies::OutsideTransformAperture { declared, reason } => {
                format!("outside the declared aperture [{declared}]: {reason}")
            }
        };
        format!("{} / {}: {detail}", self.chart.name(), self.step)
    }
}

fn written_groups(groups: &BTreeSet<QuinticTransitiveGroup>) -> String {
    if groups.is_empty() {
        return "{}".to_owned();
    }
    let names = groups
        .iter()
        .map(|group| format!("{group:?}"))
        .collect::<Vec<_>>();
    format!("{{{}}}", names.join(", "))
}

/// Returned or refused. There is no third state and no partial credit.
///
/// The refusal variant is the large one because a refusal here carries its whole census — the
/// auxiliary polynomial, every isolated real root and its Sturm certificate. That is the point of
/// the organ, so the evidence is held inline rather than behind an indirection.
#[allow(clippy::large_enum_variant)]
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ChartOutcome {
    Returned(Box<ChartTransport>),
    Refused(ChartObstruction),
}

impl ChartOutcome {
    pub fn transport(&self) -> Option<&ChartTransport> {
        match self {
            Self::Returned(transport) => Some(transport),
            Self::Refused(_) => None,
        }
    }

    pub fn obstruction(&self) -> Option<&ChartObstruction> {
        match self {
            Self::Returned(_) => None,
            Self::Refused(obstruction) => Some(obstruction),
        }
    }
}

/// What the radical chart returns when it returns: an exhibited root expression, never a verdict
/// on its own.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RadicalReturn {
    /// The rational-root receiver deflated the quintic below the degree-five wall. Every remaining
    /// factor has degree at most four, so Cardano and Ferrari write the roots in radicals.
    BelowTheWall {
        rational_roots: Vec<Rat>,
        residual_degree: usize,
    },
    /// The depressed form is a binomial `y^n + q`. The `n` roots are the `n`-th roots of `-q` times
    /// the `n`-th roots of unity, and the chart writes them out.
    DepressedBinomial {
        degree: usize,
        shift: Rat,
        constant: Rat,
        written: Vec<String>,
    },
}

/// The radical chart's verdict is a **population**, because its receiver family returns a
/// population.
///
/// `Open` is the honest third state and it is not a failure: the Frobenius cycle-type receiver can
/// exclude a group only by observing a cycle type that group does not have, and `S_5` has every
/// cycle type while `A_5` has every cycle type `C_5` has. So this receiver can certify `A_5` or
/// `S_5` uniquely and can **never** certify `C_5`, `D_5` or `F_20` uniquely. A scalar answer here
/// would be a lie; the population is the truth.
#[allow(clippy::large_enum_variant)]
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum RadicalChartVerdict {
    Returns(RadicalReturn),
    Refuses(ChartObstruction),
    Open {
        solvable: BTreeSet<QuinticTransitiveGroup>,
        nonsolvable: BTreeSet<QuinticTransitiveGroup>,
    },
}

impl RadicalChartVerdict {
    pub fn label(&self) -> &'static str {
        match self {
            Self::Returns(_) => "RETURNS",
            Self::Refuses(_) => "REFUSES",
            Self::Open { .. } => "OPEN",
        }
    }
}

/// Everything the declared receiver family saw, and what the radical chart made of it.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct RadicalChartReading {
    pub degree: usize,
    pub prime_limit: u64,
    pub discriminant: BigInt,
    pub discriminant_is_square: bool,
    pub irreducibility: QuinticIrreducibility,
    pub observed_cycle_types: BTreeMap<Vec<u32>, BTreeSet<u64>>,
    /// The degree-general criterion: Galois's theorem on solvable equations of prime degree, run
    /// against the observed cycle types. This is the route that works at every rung.
    pub solvability: SolvabilityConstraint,
    /// **Degree five only.** Empty at every other degree; [`Self::catalogue_applies`] separates
    /// "obstructed" from "does not apply".
    pub admitted_groups: BTreeSet<QuinticTransitiveGroup>,
    pub solvable_admitted: BTreeSet<QuinticTransitiveGroup>,
    pub nonsolvable_admitted: BTreeSet<QuinticTransitiveGroup>,
    /// `Some(true)` when both routes applied and agreed, `Some(false)` when they disagreed —
    /// a defect in one of them — and `None` when only one route applied.
    pub criterion_agrees_with_catalogue: Option<bool>,
    /// The rational-root receiver's complete return on the normalised monic source.
    pub rational_roots: Vec<Rat>,
    pub residual_degree_after_deflation: usize,
    /// Present exactly when the depressed form is `y^n + q`.
    pub depressed_binomial_constant: Option<Rat>,
    pub verdict: RadicalChartVerdict,
}

impl RadicalChartReading {
    /// Whether the degree-five transitive catalogue is inside its own aperture here.
    pub fn catalogue_applies(&self) -> bool {
        self.degree == catalogued_transitive_degree()
    }

    /// The transitive-group fiber classifies an **irreducible quintic**. Until irreducibility is
    /// certified by a prime whose reduction stays irreducible of full degree, the catalogue is
    /// conditional and an empty candidate set means "obstructed", not "no group" — and at any
    /// degree but five it does not apply at all.
    pub fn transitive_receiver_applies(&self) -> bool {
        self.catalogue_applies()
            && matches!(
                self.irreducibility,
                QuinticIrreducibility::CertifiedByPrime { .. }
            )
    }

    /// The cross-check demanded of any chart verdict: it must be consistent with the group
    /// population `solvable_by_radicals()` admits.
    ///
    /// A return requires at least one admitted group to be solvable; a refusal requires none to be.
    /// This is the honest predicate, because the fiber returns a *set* and the chart returns a
    /// verdict, and only a set-versus-verdict statement can be checked without inventing a
    /// certainty neither side has. Where **both** routes apply their verdicts must also agree with
    /// each other, and a disagreement is reported as a failure of this predicate rather than
    /// narrated away.
    ///
    /// When the catalogue does not apply — a degree other than five, or irreducibility not yet
    /// certified — agreement is the requirement that the chart did **not refuse on the catalogue's
    /// authority**. A refusal driven by the degree-general prime-degree criterion is lawful there,
    /// and is exactly what a degree-seven input is expected to produce. Reading a receiver outside
    /// its declared aperture is the defect `CLAUDE.md` §8 convicts.
    pub fn agrees_with_group_fiber(&self) -> bool {
        if self.criterion_agrees_with_catalogue == Some(false) {
            return false;
        }
        if !self.transitive_receiver_applies() {
            return match &self.verdict {
                RadicalChartVerdict::Refuses(_) => self.solvability.refutes_solvability(),
                _ => true,
            };
        }
        match &self.verdict {
            RadicalChartVerdict::Returns(_) => !self.solvable_admitted.is_empty(),
            RadicalChartVerdict::Refuses(_) => self.solvable_admitted.is_empty(),
            RadicalChartVerdict::Open {
                solvable,
                nonsolvable,
            } => !solvable.is_empty() && !nonsolvable.is_empty(),
        }
    }
}

/// One polynomial of any degree, read through every chart this organ owns.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QuinticChartAtlas {
    pub problem: IntegralQuinticProblem,
    /// The degree, read off the normalised source. Every chart below is a function of it.
    pub degree: usize,
    /// `g(y) = a_n^(n-1) f(y/a_n)`, monic over `Z`, which preserves the splitting field.
    pub monic_source: RationalPolynomial,
    pub root_scale: BigInt,
    pub power_sums: Vec<Rat>,
    pub radical: RadicalChartReading,
    pub depressed: ChartOutcome,
    pub principal: ChartOutcome,
    pub bring: ChartOutcome,
    /// Every refusal from every chart, retained whole. A population, not a first failure.
    pub obstructions: Vec<ChartObstruction>,
}

impl QuinticChartAtlas {
    pub fn outcomes(&self) -> [(QuinticChart, &ChartOutcome); 3] {
        [
            (QuinticChart::Depressed, &self.depressed),
            (QuinticChart::Principal, &self.principal),
            (QuinticChart::Bring, &self.bring),
        ]
    }

    /// Every returned transport whose certificate holds. A transport whose substitution residue is
    /// nonzero is not counted as a return anywhere.
    pub fn verified_transports(&self) -> Vec<&ChartTransport> {
        self.outcomes()
            .into_iter()
            .filter_map(|(_, outcome)| outcome.transport())
            .filter(|transport| transport.certificate.holds())
            .collect()
    }
}

/// Read one integral polynomial of **any** degree through the whole chart family.
///
/// `horn_local_section_limit` is the caller's declaration of how many affine integer-polynomial
/// torsors one horn-resolution event of the arithmetic-monodromy fiber may retain. It moved out of
/// `prime_ecology` on 2026-08-09 (`canon/THE_CONTAMINANT_PROTOCOL.md` §2.5) and is passed straight
/// through: this organ does not pick it either.
///
/// The degree is read off the normalised source and nothing here is pinned to it. A chart that is
/// not defined at that degree returns [`ChartObstructionSpecies::ChartUndefinedAtDegree`] rather
/// than being skipped, so the population of refusals stays complete.
pub fn read_quintic_charts(
    problem: &IntegralQuinticProblem,
    prime_limit: u64,
    horn_local_section_limit: u64,
) -> Result<QuinticChartAtlas, QuinticChartError> {
    let normalized = problem.normalize()?;
    let monic_source = RationalPolynomial::from_integers(&normalized.coefficients);
    let degree = normalized.degree();
    if monic_source.degree() != Some(degree) || !monic_source.is_monic() {
        return Err(QuinticChartError::NotMonicOfTheDeclaredDegree {
            declared: degree,
            found: monic_source.degree(),
        });
    }
    // The transported power sums of a degree-`k` transform reach `p_n`, and `g^n` has degree `k n`
    // in `x`, so the source's own power sums are needed up to `k n`. `k` is the largest transform
    // degree any chart in the family declares, read off the family rather than written down.
    let widest_transform = QuinticChart::TRANSPORTING
        .iter()
        .map(|chart| chart.killed_count())
        .max()
        .unwrap_or(1);
    let power_sums = newton_power_sums(&monic_source, widest_transform * degree)?;

    let mut obstructions = Vec::new();
    let depressed = depressed_chart(&monic_source, degree, &power_sums)?;
    if let Some(obstruction) = depressed.obstruction() {
        obstructions.push(obstruction.clone());
    }
    let principal = principal_chart(&monic_source, degree, &power_sums, &mut obstructions)?;
    if let Some(obstruction) = principal.obstruction() {
        obstructions.push(obstruction.clone());
    }
    let bring = bring_chart(&monic_source, degree, &power_sums, &mut obstructions)?;
    if let Some(obstruction) = bring.obstruction() {
        obstructions.push(obstruction.clone());
    }

    let radical = radical_chart(
        problem,
        &monic_source,
        degree,
        &depressed,
        prime_limit,
        horn_local_section_limit,
    )?;
    if let RadicalChartVerdict::Refuses(obstruction) = &radical.verdict {
        obstructions.push(obstruction.clone());
    }
    // An intermediate refusal a chart already retained on its way to its final one must not be
    // counted twice: a population with a repeat reports a size that is not its content.
    let mut seen = Vec::new();
    obstructions.retain(|obstruction| {
        if seen.contains(obstruction) {
            false
        } else {
            seen.push(obstruction.clone());
            true
        }
    });

    Ok(QuinticChartAtlas {
        problem: problem.clone(),
        degree,
        monic_source,
        root_scale: normalized.root_scale,
        power_sums,
        radical,
        depressed,
        principal,
        bring,
        obstructions,
    })
}

// ---------------------------------------------------------------------------------------------
// the transport itself
// ---------------------------------------------------------------------------------------------

/// `p_k = sum_i g(x_i)^k`, from the source's power sums and the ordinary `k`-th power of `g`.
///
/// No root, no reduction modulo `f`, no matrix. `g(x_i)^k` expands as a polynomial in `x_i`, and
/// summing over `i` replaces `x_i^m` by `s_m`.
fn transported_power_sum(
    transform: &RationalPolynomial,
    source_power_sums: &[Rat],
    order: usize,
) -> Result<Rat, QuinticChartError> {
    let mut power = RationalPolynomial::one();
    for _ in 0..order {
        power = power.times(transform);
    }
    let mut total = Rat::zero();
    for (degree, coefficient) in power.coefficients().iter().enumerate() {
        if coefficient.is_zero() {
            continue;
        }
        let sum = source_power_sums
            .get(degree)
            .ok_or(QuinticChartError::InsufficientPowerSums)?;
        total += coefficient * sum;
    }
    Ok(total)
}

/// The symbolic form of the same identity, with each transform coefficient a polynomial in two
/// declared parameters.
fn symbolic_transported_power_sum(
    transform: &[BivariatePolynomial],
    source_power_sums: &[Rat],
    order: usize,
) -> Result<BivariatePolynomial, QuinticChartError> {
    let mut power = vec![BivariatePolynomial::retained(RationalPolynomial::one())];
    for _ in 0..order {
        let mut next = vec![BivariatePolynomial::zero(); power.len() + transform.len() - 1];
        for (left_degree, left) in power.iter().enumerate() {
            if left.is_zero() {
                continue;
            }
            for (right_degree, right) in transform.iter().enumerate() {
                next[left_degree + right_degree] =
                    next[left_degree + right_degree].plus(&left.times(right));
            }
        }
        power = next;
    }
    let mut total = BivariatePolynomial::zero();
    for (degree, coefficient) in power.iter().enumerate() {
        if coefficient.is_zero() {
            continue;
        }
        let sum = source_power_sums
            .get(degree)
            .ok_or(QuinticChartError::InsufficientPowerSums)?;
        total = total.plus(&coefficient.scaled_by_rational(sum));
    }
    Ok(total)
}

/// `prod_i (y - g(x_i))`, by the Newton identities on the transported power sums.
///
/// The transported form has the same degree as the source: a Tschirnhaus transform relabels the
/// root population, it does not resize it. `p_0` is therefore the source's own `s_0`, taken from
/// the source's power sums rather than restated.
fn transported_form(
    transform: &RationalPolynomial,
    source_power_sums: &[Rat],
    degree: usize,
) -> Result<(RationalPolynomial, CensusWork), QuinticChartError> {
    let mut work = CensusWork::default();
    let mut sums = vec![
        source_power_sums
            .first()
            .cloned()
            .ok_or(QuinticChartError::InsufficientPowerSums)?,
    ];
    for order in 1..=degree {
        work.exact_evaluations += 1;
        sums.push(transported_power_sum(transform, source_power_sums, order)?);
    }
    let form = monic_from_power_sums(&sums, degree)?;
    Ok((form, work))
}

/// `Res_x(f(x), y - g(x))` by fraction-free Bareiss on the Sylvester matrix over `Q[y]`.
fn resultant_transported_form(
    source: &RationalPolynomial,
    transform: &RationalPolynomial,
) -> Result<(RationalPolynomial, ResultantWork), QuinticChartError> {
    let source_bivariate = BivariatePolynomial::new(
        source
            .coefficients()
            .iter()
            .map(|coefficient| RationalPolynomial::constant(coefficient.clone()))
            .collect(),
    );
    let mut shifted = transform
        .coefficients()
        .iter()
        .map(|coefficient| RationalPolynomial::constant(-coefficient.clone()))
        .collect::<Vec<_>>();
    if shifted.is_empty() {
        shifted.push(RationalPolynomial::zero());
    }
    // The `x^0` coefficient carries the retained variable `y`.
    shifted[0] = shifted[0].plus(&RationalPolynomial::variable());
    let shifted = BivariatePolynomial::new(shifted);
    let (form, work) = resultant_in_eliminated_variable(&source_bivariate, &shifted)?;
    Ok((form, work))
}

/// `Res(p, p')` over `Q`, through the same Sylvester/Bareiss path.
fn univariate_discriminant(monic: &RationalPolynomial) -> Result<Rat, QuinticChartError> {
    let degree = monic.degree().ok_or(QuinticChartError::ZeroSource)?;
    let derivative = monic.derivative();
    if derivative.is_zero() {
        return Ok(Rat::zero());
    }
    let lift = |polynomial: &RationalPolynomial| {
        BivariatePolynomial::new(
            polynomial
                .coefficients()
                .iter()
                .map(|coefficient| RationalPolynomial::constant(coefficient.clone()))
                .collect(),
        )
    };
    let (resultant, _) = resultant_in_eliminated_variable(&lift(monic), &lift(&derivative))?;
    let value = resultant.coefficient(0);
    let triangular = degree * (degree - 1) / 2;
    Ok(if triangular % 2 == 0 { value } else { -value })
}

/// Build and certify one transport, refusing when the transform collapses the root population.
///
/// Eight arguments because eight independent things decide a transport, and bundling them into a
/// struct would hide which of them the chart declared and which the material supplied.
#[allow(clippy::too_many_arguments)]
fn certified_transport(
    chart: QuinticChart,
    source: &RationalPolynomial,
    degree: usize,
    source_power_sums: &[Rat],
    source_discriminant: &Rat,
    transform: RationalPolynomial,
    aperture: &str,
    auxiliary: Vec<AuxiliaryStep>,
) -> Result<ChartOutcome, QuinticChartError> {
    let (transported, newton_work) = transported_form(&transform, source_power_sums, degree)?;
    let (resultant_form, resultant_work) = resultant_transported_form(source, &transform)?;
    let transported_discriminant = univariate_discriminant(&transported)?;
    if transported_discriminant.is_zero() && !source_discriminant.is_zero() {
        return Ok(ChartOutcome::Refused(ChartObstruction {
            chart,
            step: "root population".to_owned(),
            species: ChartObstructionSpecies::TransportCollapsesRoots {
                transport: transform,
                transported_discriminant,
            },
        }));
    }
    // F(g(x)) reduced modulo f(x): the transport verified by literal substitution.
    let composed = transported.composed_with(&transform);
    let (_, substitution_residue) = composed.divided_by(source)?;
    let substitution_vanishes = substitution_residue.is_zero();
    let resultant_agrees = resultant_form == transported;
    let killed = chart
        .killed_degrees(degree)
        .into_iter()
        .map(|killed_degree| (killed_degree, transported.coefficient(killed_degree)))
        .collect::<BTreeMap<_, _>>();
    // A chart that promised to kill a coefficient and did not has left its aperture, and that is a
    // typed refusal rather than a return whose caller has to notice.
    if let Some((degree, value)) = killed.iter().find(|(_, value)| !value.is_zero()) {
        return Ok(ChartOutcome::Refused(ChartObstruction {
            chart,
            step: format!("kill x^{degree}"),
            species: ChartObstructionSpecies::OutsideTransformAperture {
                declared: aperture.to_owned(),
                reason: format!(
                    "the transported form kept x^{degree} = {value} under g = {}",
                    transform.written("x")
                ),
            },
        }));
    }
    Ok(ChartOutcome::Returned(Box::new(ChartTransport {
        chart,
        source_degree: degree,
        source: source.clone(),
        transport: transform,
        transported,
        killed,
        aperture: aperture.to_owned(),
        cost: chart.cost(),
        certificate: TransportCertificate {
            substitution_residue,
            substitution_vanishes,
            resultant_form,
            resultant_agrees,
            source_discriminant: source_discriminant.clone(),
            transported_discriminant,
            roots_stay_apart: true,
            newton_work,
            resultant_work,
        },
        auxiliary,
    })))
}

// ---------------------------------------------------------------------------------------------
// the parameter space, and the declared affine sub-charts of it
// ---------------------------------------------------------------------------------------------

/// `c_0`, eliminated from `p_1 = 0`, as a polynomial in whatever the higher coefficients depend on.
///
/// `p_1 = C_0 s_0 + sum_{j>=1} C_j s_j`, and **`s_0` is the degree** — the zeroth power sum of the
/// source, which is `power_sums[0]` and was written as the literal five until 2026-08-09. That is
/// why this elimination is available over `Q` unconditionally at every rung, and it is the one step
/// of every chart that never refuses.
fn eliminate_constant_univariate(
    higher: &[RationalPolynomial],
    power_sums: &[Rat],
) -> RationalPolynomial {
    let degree_as_power_sum = &power_sums[0];
    let mut total = RationalPolynomial::zero();
    for (index, coefficient) in higher.iter().enumerate() {
        total = total.plus(&coefficient.scaled(&power_sums[index + 1]));
    }
    total.scaled(&(-Rat::one() / degree_as_power_sum))
}

fn eliminate_constant_bivariate(
    higher: &[BivariatePolynomial],
    power_sums: &[Rat],
) -> BivariatePolynomial {
    let degree_as_power_sum = &power_sums[0];
    let mut total = BivariatePolynomial::zero();
    for (index, coefficient) in higher.iter().enumerate() {
        total = total.plus(&coefficient.scaled_by_rational(&power_sums[index + 1]));
    }
    total.scaled_by_rational(&(-Rat::one() / degree_as_power_sum))
}

/// The transform coefficient vector for the sub-chart in which every parameter above `c_0` is
/// pinned to a declared constant.
fn pinned_coefficients(higher: &[Rat], power_sums: &[Rat]) -> Vec<RationalPolynomial> {
    let higher = higher
        .iter()
        .map(|value| RationalPolynomial::constant(value.clone()))
        .collect::<Vec<_>>();
    let constant = eliminate_constant_univariate(&higher, power_sums);
    let mut coefficients = vec![constant];
    coefficients.extend(higher);
    coefficients
}

/// The transform coefficient vector for the sub-chart with exactly one free parameter, which sits
/// at `c_1`.
fn one_parameter_coefficients(leading: &[Rat], power_sums: &[Rat]) -> Vec<RationalPolynomial> {
    let mut higher = vec![RationalPolynomial::variable()];
    higher.extend(
        leading
            .iter()
            .map(|value| RationalPolynomial::constant(value.clone())),
    );
    let constant = eliminate_constant_univariate(&higher, power_sums);
    let mut coefficients = vec![constant];
    coefficients.extend(higher);
    coefficients
}

fn instantiate(coefficients: &[RationalPolynomial], parameter: &Rat) -> RationalPolynomial {
    RationalPolynomial::new(
        coefficients
            .iter()
            .map(|coefficient| coefficient.evaluate(parameter))
            .collect(),
    )
}

// ---------------------------------------------------------------------------------------------
// the depressed chart
// ---------------------------------------------------------------------------------------------

/// Kill `x^(n-1)`. `p_1 = n c_0 + s_1 = 0` has the single rational solution `c_0 = -s_1 / n`, so
/// this chart change is available over `Q` at every degree and refuses nothing.
fn depressed_chart(
    source: &RationalPolynomial,
    degree: usize,
    power_sums: &[Rat],
) -> Result<ChartOutcome, QuinticChartError> {
    if let Some(undefined) = chart_undefined_at_degree(QuinticChart::Depressed, degree) {
        return Ok(undefined);
    }
    let coefficients = pinned_coefficients(&[Rat::one()], power_sums);
    let transform = instantiate(&coefficients, &Rat::zero());
    let discriminant = univariate_discriminant(source)?;
    certified_transport(
        QuinticChart::Depressed,
        source,
        degree,
        power_sums,
        &discriminant,
        transform,
        &format!(
            "rational shift g = x + c_0; the condition is linear with leading coefficient \
             s_0 = {degree}"
        ),
        Vec::new(),
    )
}

/// The typed refusal a chart returns below its own rung, or `None` when it is defined here.
///
/// Not a skip and not a `None` the caller has to interpret: the population of obstructions stays
/// complete, and the reason it carries is a statement about the degree.
fn chart_undefined_at_degree(chart: QuinticChart, degree: usize) -> Option<ChartOutcome> {
    let least = chart.least_source_degree();
    (degree < least).then(|| {
        ChartOutcome::Refused(ChartObstruction {
            chart,
            step: "the chart at this degree".to_owned(),
            species: ChartObstructionSpecies::ChartUndefinedAtDegree {
                source_degree: degree,
                killed_count: chart.killed_count(),
                least_source_degree: least,
            },
        })
    })
}

// ---------------------------------------------------------------------------------------------
// the principal chart
// ---------------------------------------------------------------------------------------------

const PRINCIPAL_APERTURE: &str = "transforms of degree at most two up to projective scale, \
    [c_1 : c_2] in P^1 with c_0 eliminated by p_1 = 0; searched through the two declared affine \
    sub-charts c_2 = 0 (linear) and c_2 = 1 (quadratic), lowest transform degree first";

/// Kill `x^(n-1)` and `x^(n-2)`.
///
/// The conditions are `p_1 = 0` and `p_2 = 0` at every degree, and this is a theorem rather than a
/// coincidence: `e_1 = 0` gives `p_2 = e_1 p_1 - 2 e_2 = -2 e_2`, so `p_2 = 0` is exactly
/// `e_2 = 0` — the coefficient of `x^(n-2)`. Nothing in the pair mentions `n`.
///
/// `p_1 = 0` and `p_2 = 0` are homogeneous of degrees one and two in `(c_0, c_1, c_2)`, so the
/// parameter space is `P^2` and `p_1 = 0` cuts it to a `P^1`. **Both affine charts of that `P^1`
/// are searched**, and the reason is a defect this organ had until it was measured: pinning
/// `c_2 = 1` silently excludes the point at infinity, which is exactly the linear transform — and
/// for a source already in principal form the linear transform is the *only* solution. A chart that
/// refuses because its own coordinate patch missed the answer has reported an obstruction that does
/// not exist.
///
/// The sub-charts are searched from the lowest transform degree upward, so the returned transport
/// is the simplest chart change that works rather than the first one an arbitrary order produced.
fn principal_chart(
    source: &RationalPolynomial,
    degree: usize,
    power_sums: &[Rat],
    obstructions: &mut Vec<ChartObstruction>,
) -> Result<ChartOutcome, QuinticChartError> {
    if let Some(undefined) = chart_undefined_at_degree(QuinticChart::Principal, degree) {
        return Ok(undefined);
    }
    let discriminant = univariate_discriminant(source)?;

    // Sub-chart c_2 = 0: g = x + c_0, no free parameter. The condition is p_2 = 0 outright.
    let linear = pinned_coefficients(&[Rat::one()], power_sums);
    let linear_condition = univariate_power_sum(&linear, power_sums, 2)?;
    if linear_condition.is_zero() {
        let transform = instantiate(&linear, &Rat::zero());
        let outcome = certified_transport(
            QuinticChart::Principal,
            source,
            degree,
            power_sums,
            &discriminant,
            transform,
            PRINCIPAL_APERTURE,
            Vec::new(),
        )?;
        match outcome {
            ChartOutcome::Returned(transport) => return Ok(ChartOutcome::Returned(transport)),
            ChartOutcome::Refused(obstruction) => obstructions.push(obstruction),
        }
    }

    // Sub-chart c_2 = 1: g = x^2 + c_1 x + c_0, one free parameter and a quadratic condition.
    let quadratic = one_parameter_coefficients(&[Rat::one()], power_sums);
    let auxiliary = univariate_power_sum(&quadratic, power_sums, 2)?;
    if auxiliary.is_zero() {
        // Every parameter value satisfies the condition. Taking c_1 = 0 is a declared choice, and
        // it is a choice between equals rather than a selection by any scalar.
        let transform = instantiate(&quadratic, &Rat::zero());
        return certified_transport(
            QuinticChart::Principal,
            source,
            degree,
            power_sums,
            &discriminant,
            transform,
            PRINCIPAL_APERTURE,
            Vec::new(),
        );
    }
    let second_killed = degree - 2;
    let step_name = format!("kill x^{second_killed}");
    let auxiliary_degree = auxiliary
        .degree()
        .expect("a nonzero polynomial has a degree");
    if auxiliary_degree == 0 {
        return Ok(ChartOutcome::Refused(ChartObstruction {
            chart: QuinticChart::Principal,
            step: step_name,
            species: ChartObstructionSpecies::AuxiliaryHasNoRoot {
                parameter: "c_1".to_owned(),
                auxiliary,
            },
        }));
    }
    let quadratic_discriminant = (auxiliary_degree == 2).then(|| {
        let a = auxiliary.coefficient(2);
        let b = auxiliary.coefficient(1);
        let c = auxiliary.coefficient(0);
        &b * &b - Rat::from_integer(BigInt::from(4)) * a * c
    });
    let census = rational_root_census(&auxiliary)?;
    if census.rational_roots.is_empty() {
        return Ok(ChartOutcome::Refused(ChartObstruction {
            chart: QuinticChart::Principal,
            step: step_name,
            species: ChartObstructionSpecies::AuxiliaryRootNotRational {
                parameter: "c_1".to_owned(),
                auxiliary,
                census,
                quadratic_discriminant,
            },
        }));
    }
    let mut last_refusal = None;
    for taken in &census.rational_roots {
        let step = AuxiliaryStep {
            parameter: "c_1".to_owned(),
            auxiliary: auxiliary.clone(),
            census: census.clone(),
            taken: taken.clone(),
            quadratic_discriminant: quadratic_discriminant.clone(),
        };
        let transform = instantiate(&quadratic, taken);
        let outcome = certified_transport(
            QuinticChart::Principal,
            source,
            degree,
            power_sums,
            &discriminant,
            transform,
            PRINCIPAL_APERTURE,
            vec![step],
        )?;
        match outcome {
            ChartOutcome::Returned(transport) => return Ok(ChartOutcome::Returned(transport)),
            ChartOutcome::Refused(obstruction) => {
                obstructions.push(obstruction.clone());
                last_refusal = Some(obstruction);
            }
        }
    }
    Ok(ChartOutcome::Refused(last_refusal.unwrap_or(
        ChartObstruction {
            chart: QuinticChart::Principal,
            step: step_name,
            species: ChartObstructionSpecies::OutsideTransformAperture {
                declared: PRINCIPAL_APERTURE.to_owned(),
                reason:
                    "no rational point of the parameter P^1 produced a usable transform".to_owned(),
            },
        },
    )))
}

/// A power sum where every transform coefficient is a polynomial in one parameter.
fn univariate_power_sum(
    coefficients: &[RationalPolynomial],
    source_power_sums: &[Rat],
    order: usize,
) -> Result<RationalPolynomial, QuinticChartError> {
    let mut power = vec![RationalPolynomial::one()];
    for _ in 0..order {
        let mut next = vec![RationalPolynomial::zero(); power.len() + coefficients.len() - 1];
        for (left_degree, left) in power.iter().enumerate() {
            if left.is_zero() {
                continue;
            }
            for (right_degree, right) in coefficients.iter().enumerate() {
                next[left_degree + right_degree] =
                    next[left_degree + right_degree].plus(&left.times(right));
            }
        }
        power = next;
    }
    let mut total = RationalPolynomial::zero();
    for (degree, coefficient) in power.iter().enumerate() {
        if coefficient.is_zero() {
            continue;
        }
        let sum = source_power_sums
            .get(degree)
            .ok_or(QuinticChartError::InsufficientPowerSums)?;
        total = total.plus(&coefficient.scaled(sum));
    }
    Ok(total)
}

// ---------------------------------------------------------------------------------------------
// the Bring chart
// ---------------------------------------------------------------------------------------------

const BRING_APERTURE: &str = "transforms of degree at most three up to projective scale, \
    [c_1 : c_2 : c_3] in P^2 with c_0 eliminated by p_1 = 0; searched through the three declared \
    affine sub-charts c_3 = c_2 = 0 (linear), c_3 = 0 (quadratic) and c_3 = 1 (cubic), lowest \
    transform degree first";

/// Kill `x^(n-1)`, `x^(n-2)` and `x^(n-3)`, reaching Bring–Jerrard form `y^n + ... + p y + q`.
///
/// Three homogeneous conditions of degrees one, two and three live on the transform's projective
/// parameter space. `p_1 = 0` is linear and eliminates `c_0`, leaving a conic and a cubic in the
/// `P^2` of `[c_1 : c_2 : c_3]`; by Bezout they meet in six points, which is why a cubic transform
/// is the natural aperture and also why the classical Bring reduction costs a square root and a
/// cube root — six is `2 * 3`. [`TschirnhausCost`] returns that as a figure and the eliminant's
/// degree is held against it below.
///
/// The three conditions are `p_1 = p_2 = p_3 = 0` at every degree: with `e_1 = e_2 = 0`, Newton
/// gives `p_3 = 3 e_3`, so `p_3 = 0` is exactly `e_3 = 0`, the coefficient of `x^(n-3)`.
///
/// All three affine sub-charts are searched, lowest transform degree first, for the same reason the
/// principal chart searches both of its own: a source already in Bring form is solved by the
/// *linear* transform, which lives at the excluded point of the `c_3 = 1` patch.
///
/// At `n = 4` the target is `y^4 + q`, a binomial, and this chart is where a quartic's radicals get
/// written. At `n = 3` the chart does not exist: killing `x^2`, `x^1` and `x^0` is killing every
/// coefficient below the leading one, which forces all three roots to the origin — so the organ
/// refuses with [`ChartObstructionSpecies::ChartUndefinedAtDegree`] before computing anything.
fn bring_chart(
    source: &RationalPolynomial,
    degree: usize,
    power_sums: &[Rat],
    obstructions: &mut Vec<ChartObstruction>,
) -> Result<ChartOutcome, QuinticChartError> {
    if let Some(undefined) = chart_undefined_at_degree(QuinticChart::Bring, degree) {
        return Ok(undefined);
    }
    let discriminant = univariate_discriminant(source)?;

    // Sub-chart c_3 = c_2 = 0: g = x + c_0. No free parameter; both conditions must already hold.
    let linear = pinned_coefficients(&[Rat::one()], power_sums);
    let linear_quadric = univariate_power_sum(&linear, power_sums, 2)?;
    let linear_cubic = univariate_power_sum(&linear, power_sums, 3)?;
    if linear_quadric.is_zero() && linear_cubic.is_zero() {
        let transform = instantiate(&linear, &Rat::zero());
        let outcome = certified_transport(
            QuinticChart::Bring,
            source,
            degree,
            power_sums,
            &discriminant,
            transform,
            BRING_APERTURE,
            Vec::new(),
        )?;
        match outcome {
            ChartOutcome::Returned(transport) => return Ok(ChartOutcome::Returned(transport)),
            ChartOutcome::Refused(obstruction) => obstructions.push(obstruction),
        }
    }

    // Sub-chart c_3 = 0, c_2 = 1: g = x^2 + c_1 x + c_0. One parameter, two conditions, so the
    // admissible values are the common roots and the instrument is a gcd rather than a solve.
    let quadratic = one_parameter_coefficients(&[Rat::one()], power_sums);
    let quadratic_quadric = univariate_power_sum(&quadratic, power_sums, 2)?;
    let quadratic_cubic = univariate_power_sum(&quadratic, power_sums, 3)?;
    let quadratic_common = common_condition(&quadratic_quadric, &quadratic_cubic)?;
    match quadratic_common {
        CommonCondition::Vacuous => {
            let transform = instantiate(&quadratic, &Rat::zero());
            let outcome = certified_transport(
                QuinticChart::Bring,
                source,
                degree,
                power_sums,
                &discriminant,
                transform,
                BRING_APERTURE,
                Vec::new(),
            )?;
            match outcome {
                ChartOutcome::Returned(transport) => return Ok(ChartOutcome::Returned(transport)),
                ChartOutcome::Refused(obstruction) => obstructions.push(obstruction),
            }
        }
        CommonCondition::Polynomial(condition) => {
            let census = rational_root_census(&condition)?;
            for taken in &census.rational_roots {
                let step = AuxiliaryStep {
                    parameter: "c_1".to_owned(),
                    auxiliary: condition.clone(),
                    census: census.clone(),
                    taken: taken.clone(),
                    quadratic_discriminant: None,
                };
                let transform = instantiate(&quadratic, taken);
                let outcome = certified_transport(
                    QuinticChart::Bring,
                    source,
                    degree,
                    power_sums,
                    &discriminant,
                    transform,
                    BRING_APERTURE,
                    vec![step],
                )?;
                match outcome {
                    ChartOutcome::Returned(transport) => {
                        return Ok(ChartOutcome::Returned(transport));
                    }
                    ChartOutcome::Refused(obstruction) => obstructions.push(obstruction),
                }
            }
        }
        CommonCondition::Impossible => {}
    }

    // Sub-chart c_3 = 1: g = x^3 + c_2 x^2 + c_1 x + c_0. Two parameters, so one is eliminated by
    // a fraction-free Sylvester resultant over Q[c_2] and its partner is recovered by a gcd.
    let higher = [
        BivariatePolynomial::eliminated_variable(),
        BivariatePolynomial::retained(RationalPolynomial::variable()),
        BivariatePolynomial::retained(RationalPolynomial::one()),
    ];
    let constant_term = eliminate_constant_bivariate(&higher, power_sums);
    let mut coefficients = vec![constant_term.clone()];
    coefficients.extend(higher);
    let quadric = symbolic_transported_power_sum(&coefficients, power_sums, 2)?;
    let cubic = symbolic_transported_power_sum(&coefficients, power_sums, 3)?;

    let eliminant = match (quadric.degree(), cubic.degree()) {
        (None, _) | (_, None) => None,
        (Some(0), Some(0)) => Some(quadric.coefficient(0).monic_gcd(&cubic.coefficient(0))?),
        (Some(0), _) => Some(quadric.coefficient(0)),
        (_, Some(0)) => Some(cubic.coefficient(0)),
        _ => Some(resultant_in_eliminated_variable(&quadric, &cubic)?.0),
    };
    let Some(eliminant) = eliminant else {
        return Ok(refuse_bring_with(
            obstructions,
            ChartObstruction {
                chart: QuinticChart::Bring,
                step: "eliminate c_1".to_owned(),
                species: ChartObstructionSpecies::EliminationDegenerate {
                    eliminated_parameter: "c_1".to_owned(),
                },
            },
        ));
    };
    if eliminant.is_zero() {
        return Ok(refuse_bring_with(
            obstructions,
            ChartObstruction {
                chart: QuinticChart::Bring,
                step: "eliminate c_1".to_owned(),
                species: ChartObstructionSpecies::EliminationDegenerate {
                    eliminated_parameter: "c_1".to_owned(),
                },
            },
        ));
    }
    // The cost law, consumed rather than commented. Three homogeneous conditions of degrees 1, 2
    // and 3 meet in `2 * 3 = 6` points of `P^2` after `c_0` is eliminated, so the eliminant in the
    // remaining parameter may not exceed the Bezout number. This bound can fail — it is a
    // falsifier on material the organ computes, not an assertion about its own code.
    let cost = QuinticChart::Bring.cost();
    if let Some(eliminant_degree) = eliminant.degree()
        && BigUint::from(eliminant_degree) > cost.bezout_number
    {
        return Ok(refuse_bring_with(
            obstructions,
            ChartObstruction {
                chart: QuinticChart::Bring,
                step: "eliminate c_1".to_owned(),
                species: ChartObstructionSpecies::EliminantExceedsBezoutBound {
                    eliminant_degree,
                    cost,
                },
            },
        ));
    }
    if eliminant.degree() == Some(0) {
        return Ok(refuse_bring_with(
            obstructions,
            ChartObstruction {
                chart: QuinticChart::Bring,
                step: "solve for c_2".to_owned(),
                species: ChartObstructionSpecies::AuxiliaryHasNoRoot {
                    parameter: "c_2".to_owned(),
                    auxiliary: eliminant,
                },
            },
        ));
    }
    let eliminant_census = rational_root_census(&eliminant)?;
    if eliminant_census.rational_roots.is_empty() {
        return Ok(refuse_bring_with(
            obstructions,
            ChartObstruction {
                chart: QuinticChart::Bring,
                step: "solve for c_2".to_owned(),
                species: ChartObstructionSpecies::AuxiliaryRootNotRational {
                    parameter: "c_2".to_owned(),
                    auxiliary: eliminant,
                    census: eliminant_census,
                    quadratic_discriminant: None,
                },
            },
        ));
    }

    let mut last_refusal = None;
    for retained in &eliminant_census.rational_roots {
        let quadric_at = quadric.with_retained(retained);
        let cubic_at = cubic.with_retained(retained);
        let mut partner_step = None;
        let partner_values = match common_condition(&quadric_at, &cubic_at)? {
            CommonCondition::Vacuous => vec![Rat::zero()],
            CommonCondition::Impossible => Vec::new(),
            CommonCondition::Polynomial(condition) => {
                let census = rational_root_census(&condition)?;
                partner_step = Some((condition.clone(), census.clone()));
                if census.rational_roots.is_empty() {
                    let obstruction = ChartObstruction {
                        chart: QuinticChart::Bring,
                        step: "solve for c_1".to_owned(),
                        species: ChartObstructionSpecies::PartnerNotRational {
                            retained_parameter: "c_2".to_owned(),
                            retained_value: retained.clone(),
                            partner_parameter: "c_1".to_owned(),
                            partner_auxiliary: condition,
                            census,
                        },
                    };
                    obstructions.push(obstruction.clone());
                    last_refusal = Some(obstruction);
                    continue;
                }
                census.rational_roots.clone()
            }
        };
        if partner_values.is_empty() {
            let obstruction = ChartObstruction {
                chart: QuinticChart::Bring,
                step: "solve for c_1".to_owned(),
                species: ChartObstructionSpecies::OutsideTransformAperture {
                    declared: BRING_APERTURE.to_owned(),
                    reason: format!(
                        "c_2 = {retained} is a root of the eliminant but no c_1 satisfies both \
                         conditions there"
                    ),
                },
            };
            obstructions.push(obstruction.clone());
            last_refusal = Some(obstruction);
            continue;
        }
        for partner in partner_values {
            let transform = RationalPolynomial::new(vec![
                constant_term.with_retained(retained).evaluate(&partner),
                partner.clone(),
                retained.clone(),
                Rat::one(),
            ]);
            let mut steps = vec![AuxiliaryStep {
                parameter: "c_2".to_owned(),
                auxiliary: eliminant.clone(),
                census: eliminant_census.clone(),
                taken: retained.clone(),
                quadratic_discriminant: None,
            }];
            if let Some((condition, census)) = &partner_step {
                steps.push(AuxiliaryStep {
                    parameter: "c_1".to_owned(),
                    auxiliary: condition.clone(),
                    census: census.clone(),
                    taken: partner.clone(),
                    quadratic_discriminant: None,
                });
            }
            let outcome = certified_transport(
                QuinticChart::Bring,
                source,
                degree,
                power_sums,
                &discriminant,
                transform,
                BRING_APERTURE,
                steps,
            )?;
            match outcome {
                ChartOutcome::Returned(transport) => return Ok(ChartOutcome::Returned(transport)),
                ChartOutcome::Refused(obstruction) => {
                    obstructions.push(obstruction.clone());
                    last_refusal = Some(obstruction);
                }
            }
        }
    }
    Ok(ChartOutcome::Refused(
        last_refusal.unwrap_or(ChartObstruction {
            chart: QuinticChart::Bring,
            step: "solve for c_1".to_owned(),
            species: ChartObstructionSpecies::OutsideTransformAperture {
                declared: BRING_APERTURE.to_owned(),
                reason: "no rational point of the parameter P^2 satisfied all three conditions"
                    .to_owned(),
            },
        }),
    ))
}

fn refuse_bring_with(
    obstructions: &mut Vec<ChartObstruction>,
    obstruction: ChartObstruction,
) -> ChartOutcome {
    obstructions.push(obstruction.clone());
    ChartOutcome::Refused(obstruction)
}

/// What two simultaneous univariate conditions leave.
enum CommonCondition {
    /// Both conditions vanish identically: every parameter value is admissible.
    Vacuous,
    /// One condition is a nonzero constant: no parameter value is admissible.
    Impossible,
    /// The admissible values are the roots of this polynomial.
    Polynomial(RationalPolynomial),
}

fn common_condition(
    left: &RationalPolynomial,
    right: &RationalPolynomial,
) -> Result<CommonCondition, QuinticChartError> {
    match (left.is_zero(), right.is_zero()) {
        (true, true) => Ok(CommonCondition::Vacuous),
        (true, false) => Ok(single_condition(right)),
        (false, true) => Ok(single_condition(left)),
        (false, false) => {
            if left.degree() == Some(0) || right.degree() == Some(0) {
                return Ok(CommonCondition::Impossible);
            }
            let gcd = left.monic_gcd(right)?;
            Ok(single_condition(&gcd))
        }
    }
}

fn single_condition(condition: &RationalPolynomial) -> CommonCondition {
    match condition.degree() {
        None => CommonCondition::Vacuous,
        Some(0) => CommonCondition::Impossible,
        Some(_) => CommonCondition::Polynomial(condition.clone()),
    }
}

// ---------------------------------------------------------------------------------------------
// the radical chart
// ---------------------------------------------------------------------------------------------

/// Read the radical chart through its declared receiver family.
///
/// Four receivers, each exact and each returning a population:
///
/// 1. **rational factorisation** — the complete rational-root census, deflated. A residual degree
///    of at most [`SOLVABLE_SYMMETRIC_DEGREE`] is below the wall, so Cardano and Ferrari write the
///    roots. **This is the receiver that makes the ladder mean something:** a quartic reaches it
///    and RETURNS, and the quintic's refusal is a statement only relative to that.
/// 2. **binomial recognition** — a depressed form `y^n + q` has its roots written directly as
///    `n`-th roots. This receiver sees the *transported* form, which is the whole point: the chart
///    change is what makes the radical chart able to read the input at all.
/// 3. **Galois's prime-degree criterion** — [`SolvabilityConstraint`], derived from the observed
///    Frobenius cycle types at every degree, with an explicit refusal to state a verdict at
///    composite degree.
/// 4. **the degree-five transitive catalogue** — the [`crate::arithmetic_monodromy`] fiber,
///    restricted by observed cycle types up to `prime_limit`, plus the discriminant-square parity
///    split. An independent second route where it applies, and nothing where it does not.
fn radical_chart(
    problem: &IntegralQuinticProblem,
    monic_source: &RationalPolynomial,
    degree: usize,
    depressed: &ChartOutcome,
    prime_limit: u64,
    horn_local_section_limit: u64,
) -> Result<RadicalChartReading, QuinticChartError> {
    let law = ArithmeticMonodromyLaw::with_horn_local_section_limit(1, horn_local_section_limit)?;
    let standing =
        ArithmeticMonodromyStanding::with_horn_local_section_limit(1, horn_local_section_limit)?;
    let mut world = CausalWorld::new(law, standing);
    world.receive(&ArithmeticMonodromyEvent::InheritQuintic {
        event: CHART_PROBLEM_EVENT,
        problem: problem.clone(),
    })?;
    for value in 2..=prime_limit {
        world.receive(&ArithmeticMonodromyEvent::AdmitInteger(
            ArithmeticFiberEvent {
                event: EventId(value),
                value,
            },
        ))?;
    }
    let fiber = &world
        .standing()
        .problems()
        .get(&problem.id)
        .ok_or(QuinticChartError::MissingProblemStanding)?
        .galois;

    let admitted_groups = fiber.transitive_candidates.clone();
    let solvable_admitted = admitted_groups
        .iter()
        .copied()
        .filter(|group| group.solvable_by_radicals())
        .collect::<BTreeSet<_>>();
    let nonsolvable_admitted = admitted_groups
        .iter()
        .copied()
        .filter(|group| !group.solvable_by_radicals())
        .collect::<BTreeSet<_>>();

    let census = rational_root_census(monic_source)?;
    let rational_roots = census.rational_roots.clone();
    let mut residual = monic_source.clone();
    for root in &rational_roots {
        let factor = RationalPolynomial::new(vec![-root.clone(), Rat::one()]);
        while residual.evaluate(root).is_zero() {
            residual = residual.divided_exactly_by(&factor)?;
        }
    }
    let residual_degree = residual.degree().unwrap_or(0);

    // `y^n + q`: every coefficient strictly between the leading one and the constant is zero.
    let depressed_binomial_constant = depressed.transport().and_then(|transport| {
        let form = &transport.transported;
        (1..degree)
            .all(|power| form.coefficient(power).is_zero())
            .then(|| form.coefficient(0))
    });

    let solvability = fiber.solvability.clone();
    let catalogue_applies = degree == catalogued_transitive_degree();
    let irreducibility_certified = matches!(
        fiber.irreducibility,
        QuinticIrreducibility::CertifiedByPrime { .. }
    );
    let catalogue_refuses = catalogue_applies
        && irreducibility_certified
        && !admitted_groups.is_empty()
        && solvable_admitted.is_empty();
    let verdict = if residual_degree <= SOLVABLE_SYMMETRIC_DEGREE {
        // Abel–Ruffini, the other way round: `S_n` is solvable for `n <= 4`, so once the rational
        // roots are deflated away the remaining factor is written by Cardano and Ferrari.
        RadicalChartVerdict::Returns(RadicalReturn::BelowTheWall {
            rational_roots: rational_roots.clone(),
            residual_degree,
        })
    } else if let Some(constant) = depressed_binomial_constant.clone() {
        let shift = depressed
            .transport()
            .map(|transport| transport.transport.coefficient(0))
            .unwrap_or_else(Rat::zero);
        let written = (0..degree)
            .map(|hand| {
                format!(
                    "x_{hand} = zeta_{degree}^{hand} * ({})^(1/{degree}) - ({shift})",
                    -constant.clone()
                )
            })
            .collect();
        RadicalChartVerdict::Returns(RadicalReturn::DepressedBinomial {
            degree,
            shift,
            constant,
            written,
        })
    } else if solvability.refutes_solvability() || catalogue_refuses {
        // Either route may refuse; where both apply they must agree, and
        // `criterion_agrees_with_catalogue` below is what says whether they did.
        let mut named = Vec::new();
        if catalogue_applies
            && (admitted_groups.contains(&QuinticTransitiveGroup::Alternating5)
                || admitted_groups.contains(&QuinticTransitiveGroup::Symmetric5))
        {
            named.push("A_5 is simple: the winding does not factor into single-hand steps".to_owned());
        }
        if solvability.refutes_solvability() {
            named.push(solvability.written());
        }
        if named.is_empty() {
            named.push("no admitted group is solvable".to_owned());
        }
        RadicalChartVerdict::Refuses(ChartObstruction {
            chart: QuinticChart::Radical,
            step: "write the roots".to_owned(),
            species: ChartObstructionSpecies::NonSolvableMonodromy {
                admitted: admitted_groups.clone(),
                irreducibility: fiber.irreducibility.clone(),
                solvability: solvability.clone(),
                named: named.join("; "),
            },
        })
    } else if catalogue_applies
        && irreducibility_certified
        && !solvable_admitted.is_empty()
        && nonsolvable_admitted.is_empty()
    {
        RadicalChartVerdict::Returns(RadicalReturn::BelowTheWall {
            rational_roots: rational_roots.clone(),
            residual_degree,
        })
    } else {
        // The honest third state. At a degree the catalogue does not reach, the two group sets are
        // empty and the population the reader wants is `solvability`, which is carried alongside.
        RadicalChartVerdict::Open {
            solvable: solvable_admitted.clone(),
            nonsolvable: nonsolvable_admitted.clone(),
        }
    };

    Ok(RadicalChartReading {
        degree,
        prime_limit,
        discriminant: fiber.discriminant.clone(),
        discriminant_is_square: fiber.discriminant_square_root.is_some(),
        irreducibility: fiber.irreducibility.clone(),
        observed_cycle_types: fiber.cycle_witnesses.clone(),
        solvability,
        admitted_groups,
        solvable_admitted,
        nonsolvable_admitted,
        criterion_agrees_with_catalogue: fiber.criterion_agrees_with_catalogue(),
        rational_roots,
        residual_degree_after_deflation: residual_degree,
        depressed_binomial_constant,
        verdict,
    })
}

#[derive(Clone, Debug, Error, PartialEq, Eq)]
pub enum QuinticChartError {
    #[error(transparent)]
    Polynomial(#[from] ExactPolynomialError),
    #[error(transparent)]
    Monodromy(#[from] ArithmeticMonodromyError),
    #[error(
        "the normalized source is not monic of its declared degree {declared} (found {found:?})"
    )]
    NotMonicOfTheDeclaredDegree {
        declared: usize,
        found: Option<usize>,
    },
    #[error("the zero polynomial has no degree and no discriminant")]
    ZeroSource,
    #[error("the source power sums do not reach the degree the transform needs")]
    InsufficientPowerSums,
    #[error("the monodromy standing lost the problem it was given")]
    MissingProblemStanding,
}

#[cfg(test)]
mod tests {
    use crate::arithmetic_monodromy::QuinticProblemId;

    use super::*;

    /// **What this test body declares as its horn local-section limit**, since `prime_ecology` no
    /// longer picks one (`canon/THE_CONTAMINANT_PROTOCOL.md` §2.5). The value reproduces the
    /// excised `DEFAULT_HORN_LOCAL_SECTION_LIMIT`.
    const TEST_HORN_LOCAL_SECTION_LIMIT: u64 = 1_000_000;

    /// The central contrast the degree pin deleted.
    ///
    /// `S_4` is solvable and `S_5` is not, so the radical chart must **return** for an irreducible
    /// quartic with the full symmetric group and **refuse** for the corresponding quintic. Neither
    /// half means anything without the other, and the pinned organ could not run the first half at
    /// all — `read_quintic_charts` refused a degree-four input at its first gate.
    #[test]
    fn the_quartic_returns_in_the_radical_chart_where_the_quintic_refuses() {
        // x^4 + x + 1, irreducible with Galois group S_4.
        let quartic = degree_problem("x^4+x+1", &[1, 1, 0, 0, 1]);
        let quartic_atlas =
            read_quintic_charts(&quartic, 41, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
        assert_eq!(quartic_atlas.degree, 4);
        assert_eq!(quartic_atlas.radical.residual_degree_after_deflation, 4);
        assert!(
            matches!(
                quartic_atlas.radical.verdict,
                RadicalChartVerdict::Returns(RadicalReturn::BelowTheWall { .. })
            ),
            "S_4 is solvable: the radical chart must return at degree four"
        );

        // x^5 - x - 1, irreducible with Galois group S_5.
        let quintic = degree_problem("x^5-x-1", &[-1, -1, 0, 0, 0, 1]);
        let quintic_atlas =
            read_quintic_charts(&quintic, 41, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
        assert_eq!(quintic_atlas.degree, 5);
        assert_eq!(quintic_atlas.radical.residual_degree_after_deflation, 5);
        assert!(
            matches!(
                quintic_atlas.radical.verdict,
                RadicalChartVerdict::Refuses(_)
            ),
            "A_5 is simple: the radical chart must refuse at degree five"
        );
        assert!(quartic_atlas.radical.agrees_with_group_fiber());
        assert!(quintic_atlas.radical.agrees_with_group_fiber());
    }

    /// A quartic runs the whole chart family, and `x^4 - 2` is *already* in Bring form: killing
    /// `x^3`, `x^2` and `x^1` at degree four leaves `y^4 + q`, a binomial.
    #[test]
    fn a_quartic_reaches_the_bring_chart_and_its_bring_form_is_a_binomial() {
        let problem = degree_problem("x^4-2", &[-2, 0, 0, 0, 1]);
        let atlas = read_quintic_charts(&problem, 41, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
        let transport = atlas
            .bring
            .transport()
            .expect("an already-Bring quartic transports linearly");
        assert_eq!(transport.source_degree, 4);
        assert_eq!(transport.transport.degree(), Some(1));
        assert_eq!(transport.transported, atlas.monic_source);
        assert_eq!(
            transport.killed.keys().copied().collect::<Vec<_>>(),
            vec![1, 2, 3]
        );
        assert!(transport.certificate.holds());
    }

    /// The Bring chart does not exist at degree three, and the reason is a fact about the degree.
    #[test]
    fn the_bring_chart_is_undefined_at_degree_three_and_the_refusal_names_why() {
        let problem = degree_problem("x^3-2", &[-2, 0, 0, 1]);
        let atlas = read_quintic_charts(&problem, 41, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
        let obstruction = atlas.bring.obstruction().expect("no Bring chart at degree 3");
        let ChartObstructionSpecies::ChartUndefinedAtDegree {
            source_degree,
            killed_count,
            least_source_degree,
        } = &obstruction.species
        else {
            panic!("the refusal must be typed, not an aperture excuse");
        };
        assert_eq!((*source_degree, *killed_count, *least_source_degree), (3, 3, 4));
        // And it is two-sided: the same chart is entered one rung up.
        let quartic = degree_problem("x^4-2", &[-2, 0, 0, 0, 1]);
        let quartic_atlas =
            read_quintic_charts(&quartic, 41, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
        assert!(quartic_atlas.bring.transport().is_some());
        // The principal chart has the rung below as its own floor.
        let quadratic = degree_problem("x^2-2", &[-2, 0, 1]);
        let quadratic_atlas =
            read_quintic_charts(&quadratic, 41, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
        assert!(matches!(
            quadratic_atlas.principal.obstruction().map(|o| &o.species),
            Some(ChartObstructionSpecies::ChartUndefinedAtDegree { .. })
        ));
        assert!(atlas.principal.transport().is_some());
    }

    /// The killed set follows the degree, and stops before the constant term at every rung.
    #[test]
    fn the_killed_degrees_track_the_source_degree() {
        assert_eq!(QuinticChart::Depressed.killed_degrees(7), vec![6]);
        assert_eq!(QuinticChart::Principal.killed_degrees(7), vec![6, 5]);
        assert_eq!(QuinticChart::Bring.killed_degrees(7), vec![6, 5, 4]);
        assert_eq!(QuinticChart::Bring.killed_degrees(4), vec![3, 2, 1]);
        assert_eq!(QuinticChart::Radical.killed_degrees(7), Vec::<usize>::new());
        for degree in 2..=12_usize {
            for chart in QuinticChart::TRANSPORTING {
                let killed = chart.killed_degrees(degree);
                if degree < chart.least_source_degree() {
                    assert!(killed.is_empty());
                    continue;
                }
                assert_eq!(killed.len(), chart.killed_count());
                assert!(
                    killed.iter().all(|power| *power >= 1),
                    "{} at degree {degree} reached the constant term",
                    chart.name()
                );
                assert_eq!(killed[0], degree - 1);
            }
        }
    }

    /// `2 * 3 * ... * k = k!`, computed two ways.
    #[test]
    fn the_bezout_number_of_a_degree_k_transform_is_k_factorial() {
        let mut factorial = BigUint::one();
        for k in 1..=10_usize {
            factorial *= BigUint::from(k);
            let cost = tschirnhaus_cost(k);
            assert_eq!(cost.bezout_number, factorial, "k = {k}");
            assert_eq!(cost.parameter_space_dimension, k.saturating_sub(1));
            assert_eq!(cost.condition_degrees, (2..=k).collect::<Vec<_>>());
        }
        // The three charts, and the sentence the header already carried at one rung.
        assert_eq!(
            QuinticChart::Depressed.cost().bezout_number,
            BigUint::from(1_u32)
        );
        assert_eq!(
            QuinticChart::Principal.cost().bezout_number,
            BigUint::from(2_u32)
        );
        assert_eq!(
            QuinticChart::Bring.cost().bezout_number,
            BigUint::from(6_u32)
        );
        // The bound is consumed by the Bring chart, and every returned eliminant sat under it.
        let problem = degree_problem("x^5+x^3+1", &[1, 0, 0, 1, 0, 1]);
        let atlas = read_quintic_charts(&problem, 41, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
        assert!(
            !atlas.obstructions.iter().any(|obstruction| matches!(
                obstruction.species,
                ChartObstructionSpecies::EliminantExceedsBezoutBound { .. }
            )),
            "the eliminant exceeded the Bezout number the transform degree allows"
        );
    }

    /// At degree five the catalogue and the prime-degree criterion are independent implementations
    /// of one predicate, and they must agree. At every other degree only one route applies.
    #[test]
    fn the_two_solvability_routes_agree_at_degree_five_and_only_there() {
        for (name, coefficients, refutes) in [
            ("x^5-x-1", &[-1_i64, -1, 0, 0, 0, 1][..], true),
            ("x^5+x^3+1", &[1, 0, 0, 1, 0, 1][..], true),
            ("cyclic-quintic", &[1, 3, -3, -4, 1, 1][..], false),
        ] {
            let problem = degree_problem(name, coefficients);
            let atlas = read_quintic_charts(&problem, 97, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
            assert_eq!(
                atlas.radical.criterion_agrees_with_catalogue,
                Some(true),
                "{name}: the two routes must agree at degree five"
            );
            assert_eq!(
                atlas.radical.solvability.refutes_solvability(),
                refutes,
                "{name}"
            );
            assert_eq!(atlas.radical.solvable_admitted.is_empty(), refutes, "{name}");
        }
        // Degree six: composite, so the criterion states nothing and the catalogue does not apply.
        let sextic = degree_problem("(x^2-2)(x^4-2)", &[4, 0, -2, 0, -2, 0, 1]);
        let sextic_atlas = read_quintic_charts(&sextic, 41, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
        assert_eq!(sextic_atlas.radical.criterion_agrees_with_catalogue, None);
        assert!(!sextic_atlas.radical.catalogue_applies());
        assert!(matches!(
            sextic_atlas.radical.solvability,
            SolvabilityConstraint::NoCriterionAtThisDegree {
                degree: 6,
                least_factor: 2
            }
        ));
        assert!(matches!(
            sextic_atlas.radical.verdict,
            RadicalChartVerdict::Open { .. }
        ));
        assert!(sextic_atlas.radical.agrees_with_group_fiber());
    }

    /// Prime degree seven, `x^7 - 7x + 3`, Galois group `PSL(2,7)` of order 168.
    ///
    /// Its involutions fix three of the seven points, giving cycle type `[1,1,1,2,2]`, which no
    /// affine map over `F_7` has: an affine map with `a != 1` fixes exactly one point. So the
    /// criterion refutes solvability with a named witness prime, at a degree the transitive
    /// catalogue says nothing about — and this is a return the pinned organ could not produce.
    #[test]
    fn a_septic_is_refuted_by_a_cycle_type_no_affine_map_over_f7_has() {
        let problem = degree_problem("x^7-7x+3", &[3, -7, 0, 0, 0, 0, 0, 1]);
        let atlas = read_quintic_charts(&problem, 97, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
        assert_eq!(atlas.degree, 7);
        assert!(!atlas.radical.catalogue_applies());
        assert!(atlas.radical.admitted_groups.is_empty());
        let SolvabilityConstraint::NotSolvable {
            degree, witness, ..
        } = &atlas.radical.solvability
        else {
            panic!("PSL(2,7) is not inside AGL(1,7) and the criterion must say so");
        };
        assert_eq!(*degree, 7);
        assert_eq!(witness.cycle_type, vec![1, 1, 1, 2, 2]);
        assert!(witness.prime >= 2);
        assert!(matches!(
            atlas.radical.verdict,
            RadicalChartVerdict::Refuses(_)
        ));
        assert!(atlas.radical.agrees_with_group_fiber());
        // The discriminant is a square, so G <= A_7 — the parity receiver is degree-general and
        // still speaks where the catalogue does not.
        assert!(atlas.radical.discriminant_is_square);
    }

    /// Every returned transport at every declared rung carries all three certificates.
    #[test]
    fn the_transport_certificates_hold_at_every_declared_degree() {
        for (name, coefficients) in [
            ("x^2-2", &[-2_i64, 0, 1][..]),
            ("x^3-3x-1", &[-1, -3, 0, 1][..]),
            ("x^4+x+1", &[1, 1, 0, 0, 1][..]),
            ("x^5-2x^3+x-1", &[-1, 1, 0, -2, 0, 1][..]),
            ("x^6-2", &[-2, 0, 0, 0, 0, 0, 1][..]),
            ("x^7-2", &[-2, 0, 0, 0, 0, 0, 0, 1][..]),
        ] {
            let problem = degree_problem(name, coefficients);
            let atlas = read_quintic_charts(&problem, 41, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
            assert_eq!(atlas.degree, coefficients.len() - 1);
            let mut returned = 0;
            for (chart, outcome) in atlas.outcomes() {
                let Some(transport) = outcome.transport() else {
                    continue;
                };
                returned += 1;
                assert!(
                    transport.certificate.substitution_vanishes,
                    "{name} / {}: F(g(x)) != 0 mod f(x)",
                    chart.name()
                );
                assert!(
                    transport.certificate.resultant_agrees,
                    "{name} / {}: Newton and Bareiss disagree",
                    chart.name()
                );
                for (killed, value) in &transport.killed {
                    assert!(value.is_zero(), "{name} / {}: y^{killed} alive", chart.name());
                }
                assert_eq!(transport.source_degree, atlas.degree);
            }
            assert!(returned >= 1, "{name} returned no transport at all");
        }
    }

    /// The Bring chart's own witness, unchanged by the excision.
    ///
    /// `x^5 - 2x^3 + x - 1` must still transport by `g = x^3 - x` to `y^5 - y - 1` over `Q`, with
    /// the radical chart still refusing. A regression here means the degree-five path moved.
    #[test]
    fn the_degree_five_witness_is_unmoved_by_the_ladder() {
        let problem = degree_problem("x^5-2x^3+x-1", &[-1, 1, 0, -2, 0, 1]);
        let atlas = read_quintic_charts(&problem, 41, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
        let transport = atlas.bring.transport().expect("the cubic sub-chart returns");
        assert_eq!(transport.transport, monic(&[0, -1, 0, 1]));
        assert_eq!(transport.transported, monic(&[-1, -1, 0, 0, 0, 1]));
        assert!(transport.certificate.holds());
        assert_eq!(transport.cost.bezout_number, BigUint::from(6_u32));
        assert!(matches!(
            atlas.radical.verdict,
            RadicalChartVerdict::Refuses(_)
        ));
        assert_eq!(
            atlas.radical.admitted_groups,
            BTreeSet::from([QuinticTransitiveGroup::Symmetric5])
        );
    }

    /// An input of any degree, not just five. The name is historical; the code imposes nothing.
    fn degree_problem(name: &str, coefficients: &[i64]) -> IntegralQuinticProblem {
        IntegralQuinticProblem::new(
            QuinticProblemId(11),
            name,
            coefficients
                .iter()
                .map(|value| BigInt::from(*value))
                .collect(),
        )
        .expect("declared polynomial")
    }

    fn quintic(name: &str, coefficients: &[i64]) -> IntegralQuinticProblem {
        IntegralQuinticProblem::new(
            QuinticProblemId(7),
            name,
            coefficients
                .iter()
                .map(|value| BigInt::from(*value))
                .collect(),
        )
        .expect("declared quintic")
    }

    fn monic(coefficients: &[i64]) -> RationalPolynomial {
        RationalPolynomial::new(
            coefficients
                .iter()
                .map(|value| Rat::from_integer(BigInt::from(*value)))
                .collect(),
        )
    }

    #[test]
    fn the_two_independent_transported_forms_agree_and_the_substitution_vanishes() {
        // x^5 - x - 1, the standard S_5 quintic. The Newton/power-sum route and the
        // Sylvester/Bareiss resultant are different algorithms; they must return the same object.
        let source = monic(&[-1, -1, 0, 0, 0, 1]);
        let power_sums = newton_power_sums(&source, 15).unwrap();
        let outcome = depressed_chart(&source, 5, &power_sums).unwrap();
        let transport = outcome
            .transport()
            .expect("the depressed chart always returns");
        assert!(transport.certificate.resultant_agrees);
        assert!(transport.certificate.substitution_vanishes);
        assert!(transport.certificate.substitution_residue.is_zero());
    }

    #[test]
    fn the_depressed_chart_kills_the_fourth_coefficient_over_every_declared_input() {
        for coefficients in [
            &[-1_i64, -1, 0, 0, 0, 1][..],
            &[3, 5, 10, 10, 5, 1][..],
            &[1, 3, -3, -4, 1, 1][..],
            &[-2, 0, 0, 0, 0, 1][..],
        ] {
            let source = monic(coefficients);
            let power_sums = newton_power_sums(&source, 15).unwrap();
            let outcome = depressed_chart(&source, 5, &power_sums).unwrap();
            let transport = outcome.transport().expect("a shift always exists over Q");
            assert!(transport.transported.coefficient(4).is_zero());
            assert!(transport.certificate.holds());
        }
    }

    #[test]
    fn the_transport_is_verified_by_substitution_and_not_by_assertion() {
        // Perturbing the returned transport must break the substitution residue. If it did not,
        // the residue would be measuring nothing.
        let source = monic(&[-1, -1, 0, 0, 0, 1]);
        let power_sums = newton_power_sums(&source, 15).unwrap();
        let transport = depressed_chart(&source, 5, &power_sums)
            .unwrap()
            .transport()
            .expect("returns")
            .clone();
        let wrong = transport
            .transport
            .plus(&RationalPolynomial::constant(Rat::one()));
        let composed = transport.transported.composed_with(&wrong);
        let (_, residue) = composed.divided_by(&source).unwrap();
        assert!(
            !residue.is_zero(),
            "the substitution check cannot fail, so it checks nothing"
        );
    }

    #[test]
    fn a_principal_chart_change_that_is_rational_returns_and_one_that_is_not_refuses() {
        // Both directions on declared inputs, which is what makes this a test rather than a
        // demonstration. x^5 + 5x^3 + 5x + 1 has auxiliary -10 c_1^2 + 10, roots +-1, rational.
        let rational = monic(&[1, 5, 0, 5, 0, 1]);
        let rational_sums = newton_power_sums(&rational, 15).unwrap();
        let mut retained = Vec::new();
        let returned = principal_chart(&rational, 5, &rational_sums, &mut retained).unwrap();
        let transport = returned
            .transport()
            .expect("x^5 + 5x^3 + 5x + 1 transports rationally");
        assert!(transport.transported.coefficient(4).is_zero());
        assert!(transport.transported.coefficient(3).is_zero());
        assert!(transport.certificate.holds());
        assert_eq!(transport.transport.degree(), Some(2));

        // x^5 + x^3 + 1 has auxiliary -2 c_1^2 + 6/5, whose discriminant 48/5 is not a rational
        // square, so the chart change lives in Q(sqrt(3/5)) and not in Q.
        let irrational = monic(&[1, 0, 0, 1, 0, 1]);
        let irrational_sums = newton_power_sums(&irrational, 15).unwrap();
        let mut retained = Vec::new();
        let refused = principal_chart(&irrational, 5, &irrational_sums, &mut retained).unwrap();
        let obstruction = refused
            .obstruction()
            .expect("x^5 + x^3 + 1 needs an irrational chart change");
        assert!(matches!(
            obstruction.species,
            ChartObstructionSpecies::AuxiliaryRootNotRational { .. }
        ));
    }

    #[test]
    fn a_source_already_in_principal_form_is_solved_by_the_point_at_infinity() {
        // x^5 - x - 1 already has e_1 = e_2 = 0, so the only transform that works is the LINEAR
        // one, which sits at the excluded point of the c_2 = 1 patch. A chart that searched one
        // affine patch would report an obstruction that does not exist.
        let source = monic(&[-1, -1, 0, 0, 0, 1]);
        let power_sums = newton_power_sums(&source, 15).unwrap();
        let mut retained = Vec::new();
        let outcome = principal_chart(&source, 5, &power_sums, &mut retained).unwrap();
        let transport = outcome
            .transport()
            .expect("the linear sub-chart solves an already-principal source");
        assert_eq!(transport.transport.degree(), Some(1));
        assert_eq!(transport.transported, source);
        assert!(transport.certificate.holds());
    }

    #[test]
    fn the_principal_obstruction_carries_the_quadratic_whose_square_root_it_wanted() {
        let source = monic(&[1, 0, 0, 1, 0, 1]);
        let power_sums = newton_power_sums(&source, 15).unwrap();
        let mut retained = Vec::new();
        let refused = principal_chart(&source, 5, &power_sums, &mut retained).unwrap();
        let ChartObstructionSpecies::AuxiliaryRootNotRational {
            auxiliary,
            census,
            quadratic_discriminant,
            ..
        } = &refused.obstruction().expect("refuses").species
        else {
            panic!("the principal chart must refuse with a named auxiliary");
        };
        assert_eq!(auxiliary.degree(), Some(2));
        assert!(census.rational_roots.is_empty());
        let discriminant = quadratic_discriminant
            .clone()
            .expect("a quadratic auxiliary carries its discriminant");
        assert_eq!(discriminant, Rat::new(BigInt::from(48), BigInt::from(5)));
        // Two real roots, both certified, neither rational: the obstruction is the field and not
        // the existence of the chart change.
        assert_eq!(census.distinct_real_roots, 2);
        assert_eq!(census.irrational_real_roots().len(), 2);
    }

    #[test]
    fn every_returned_transport_kills_exactly_what_its_chart_promised() {
        let problem = quintic("x^5-2", &[-2, 0, 0, 0, 0, 1]);
        let atlas = read_quintic_charts(&problem, 41, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
        for (chart, outcome) in atlas.outcomes() {
            if let Some(transport) = outcome.transport() {
                for degree in chart.killed_degrees(atlas.degree) {
                    assert!(
                        transport.transported.coefficient(degree).is_zero(),
                        "{} left x^{degree} alive",
                        chart.name()
                    );
                }
                assert!(transport.certificate.holds());
            }
        }
    }

    #[test]
    fn the_radical_chart_refuses_a_non_solvable_quintic_and_names_the_obstruction() {
        let problem = quintic("x^5-x-1", &[-1, -1, 0, 0, 0, 1]);
        let atlas = read_quintic_charts(&problem, 41, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
        let RadicalChartVerdict::Refuses(obstruction) = &atlas.radical.verdict else {
            panic!("x^5 - x - 1 has Galois group S_5 and the radical chart must refuse");
        };
        let ChartObstructionSpecies::NonSolvableMonodromy {
            named, admitted, ..
        } = &obstruction.species
        else {
            panic!("the refusal must name the monodromy obstruction");
        };
        assert!(named.contains("A_5 is simple"));
        assert_eq!(
            *admitted,
            BTreeSet::from([QuinticTransitiveGroup::Symmetric5])
        );
        assert!(atlas.radical.agrees_with_group_fiber());
    }

    #[test]
    fn the_radical_chart_returns_for_a_declared_solvable_quintic() {
        // (x - 1)(x^4 - 2): the rational-root receiver deflates below the degree-five wall.
        let problem = quintic("(x-1)(x^4-2)", &[2, -2, 0, 0, -1, 1]);
        let atlas = read_quintic_charts(&problem, 41, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
        let RadicalChartVerdict::Returns(RadicalReturn::BelowTheWall {
            residual_degree, ..
        }) = &atlas.radical.verdict
        else {
            panic!("a quintic with a rational root is solvable in the radical chart");
        };
        assert_eq!(*residual_degree, 4);
        assert!(atlas.radical.agrees_with_group_fiber());
    }

    #[test]
    fn the_chart_change_is_what_lets_the_radical_chart_read_a_binomial() {
        // (x+1)^5 + 2 is not a binomial; its depressed transport is. The radical chart returns on
        // the transported form and would be Open on the source without it.
        let problem = quintic("(x+1)^5+2", &[3, 5, 10, 10, 5, 1]);
        let atlas = read_quintic_charts(&problem, 41, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
        assert_eq!(
            atlas.radical.depressed_binomial_constant,
            Some(Rat::from_integer(BigInt::from(2)))
        );
        assert!(matches!(
            atlas.radical.verdict,
            RadicalChartVerdict::Returns(RadicalReturn::DepressedBinomial { .. })
        ));
        assert!(atlas.radical.agrees_with_group_fiber());
    }

    #[test]
    fn the_cycle_type_receiver_leaves_a_cyclic_quintic_open_and_the_chart_says_so() {
        // 2*cos(2*pi/11) has minimal polynomial x^5 + x^4 - 4x^3 - 3x^2 + 3x + 1, Galois group C_5,
        // discriminant 11^4. Every Frobenius cycle type is 1^5 or 5, and A_5 has both, so no
        // observation can ever exclude A_5. The fiber stays {C_5, A_5}: one solvable, one not.
        let problem = quintic("cyclic-quintic", &[1, 3, -3, -4, 1, 1]);
        let atlas = read_quintic_charts(&problem, 97, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
        // D_5 sits inside A_5 for degree five — a reflection on five points is a product of two
        // transpositions and therefore even — so a square discriminant admits {C_5, D_5, A_5}.
        assert_eq!(
            atlas.radical.admitted_groups,
            BTreeSet::from([
                QuinticTransitiveGroup::Cyclic5,
                QuinticTransitiveGroup::Dihedral5,
                QuinticTransitiveGroup::Alternating5
            ])
        );
        assert!(atlas.radical.transitive_receiver_applies());
        assert!(matches!(
            atlas.radical.verdict,
            RadicalChartVerdict::Open { .. }
        ));
        assert!(atlas.radical.agrees_with_group_fiber());
    }

    #[test]
    fn a_refusal_is_a_population_and_every_member_carries_what_refused_it() {
        // x^5 + x^3 + 1 refuses in three charts at once, for three different reasons.
        let problem = quintic("x^5+x^3+1", &[1, 0, 0, 1, 0, 1]);
        let atlas = read_quintic_charts(&problem, 41, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
        assert_eq!(
            atlas.obstructions.len(),
            3,
            "the principal, Bring and radical charts each refuse this input exactly once"
        );
        let charts = atlas
            .obstructions
            .iter()
            .map(|obstruction| obstruction.chart)
            .collect::<BTreeSet<_>>();
        assert_eq!(
            charts,
            BTreeSet::from([
                QuinticChart::Radical,
                QuinticChart::Principal,
                QuinticChart::Bring
            ])
        );
        for obstruction in &atlas.obstructions {
            let written = obstruction.written();
            assert!(!written.is_empty());
            assert!(
                !written.contains('.'),
                "a decimal expansion reached a presented obstruction: {written}"
            );
        }
    }

    #[test]
    fn a_transform_that_identifies_two_roots_is_refused_and_not_returned() {
        // x^5 - 5x^3 + 4x = x(x^2 - 1)(x^2 - 4) has roots 0, +-1, +-2. Squaring sends 1 and -1 to
        // the same place, so g = x^2 is not a chart change on this root population at all: the
        // transported quintic has a repeated root and its discriminant is exactly zero. The organ
        // must refuse rather than hand back a degenerate "transport". This is the branch that
        // proves the discriminant guard can fire.
        let source = monic(&[0, 4, 0, -5, 0, 1]);
        let power_sums = newton_power_sums(&source, 15).unwrap();
        let discriminant = univariate_discriminant(&source).unwrap();
        assert!(
            !discriminant.is_zero(),
            "the source has five distinct roots"
        );
        let outcome = certified_transport(
            QuinticChart::Depressed,
            &source,
            5,
            &power_sums,
            &discriminant,
            monic(&[0, 0, 1]),
            "test aperture",
            Vec::new(),
        )
        .unwrap();
        let obstruction = outcome.obstruction().expect("squaring collapses +-1");
        let ChartObstructionSpecies::TransportCollapsesRoots {
            transported_discriminant,
            ..
        } = &obstruction.species
        else {
            panic!("the refusal must name the collapse");
        };
        assert!(transported_discriminant.is_zero());
    }

    #[test]
    fn the_retained_population_holds_no_repeats() {
        for coefficients in [
            &[1_i64, 0, 0, 1, 0, 1][..],
            &[2, -2, 0, 0, -1, 1][..],
            &[1, 3, -3, -4, 1, 1][..],
        ] {
            let problem = quintic("population-probe", coefficients);
            let atlas = read_quintic_charts(&problem, 41, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
            let mut unique: Vec<&ChartObstruction> = Vec::new();
            for obstruction in &atlas.obstructions {
                if !unique.contains(&obstruction) {
                    unique.push(obstruction);
                }
            }
            assert_eq!(
                unique.len(),
                atlas.obstructions.len(),
                "a retained obstruction was counted twice"
            );
        }
    }

    #[test]
    fn the_bring_elimination_stays_inside_its_own_bezout_bound() {
        // Three homogeneous conditions of degrees 1, 2, 3 meet in six points of P^2 after c_0 is
        // eliminated, so the eliminant's degree may not exceed six. Six is also the degree of the
        // classical resolvent Bring's own reduction solves with a square root and a cube root.
        let source = monic(&[1, 0, 0, 1, 0, 1]);
        let power_sums = newton_power_sums(&source, 15).unwrap();
        let higher = [
            BivariatePolynomial::eliminated_variable(),
            BivariatePolynomial::retained(RationalPolynomial::variable()),
            BivariatePolynomial::retained(RationalPolynomial::one()),
        ];
        let constant_term = eliminate_constant_bivariate(&higher, &power_sums);
        let mut coefficients = vec![constant_term];
        coefficients.extend(higher);
        let quadric = symbolic_transported_power_sum(&coefficients, &power_sums, 2).unwrap();
        let cubic = symbolic_transported_power_sum(&coefficients, &power_sums, 3).unwrap();
        assert!(quadric.degree().is_some_and(|degree| degree >= 1));
        assert!(cubic.degree().is_some_and(|degree| degree >= 1));
        let (eliminant, work) = resultant_in_eliminated_variable(&quadric, &cubic).unwrap();
        assert_eq!(
            work.matrix_extent as usize,
            quadric.degree().unwrap() + cubic.degree().unwrap()
        );
        assert!(eliminant.degree().is_some_and(|degree| degree <= 6));
    }

    #[test]
    fn the_bring_chart_returns_a_genuine_cubic_transport_where_the_radical_chart_refuses() {
        // x^5 - 2x^3 + x - 1 has for its roots the SQUARES of the roots of y^5 - y - 1: if
        // y^5 = y + 1 and x = y^2 then x^3 - x = y^6 - y^2 = y(y + 1) - y^2 = y. So the cubic
        // Tschirnhaus transform g = x^3 - x carries it exactly back to Bring form, over Q, with no
        // radical anywhere — while its Galois group is still S_5 and the radical chart still
        // refuses. That is the tablet's sentence as a computation: not solvable IN THAT CHART.
        let problem = quintic("x^5-2x^3+x-1", &[-1, 1, 0, -2, 0, 1]);
        let atlas = read_quintic_charts(&problem, 41, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
        let transport = atlas
            .bring
            .transport()
            .expect("the cubic sub-chart reaches Bring form here");
        assert_eq!(transport.transport, monic(&[0, -1, 0, 1]));
        assert_eq!(transport.transported, monic(&[-1, -1, 0, 0, 0, 1]));
        assert!(transport.certificate.holds());
        assert!(matches!(
            atlas.radical.verdict,
            RadicalChartVerdict::Refuses(_)
        ));
    }

    #[test]
    fn a_source_already_in_bring_form_returns_the_linear_transform() {
        // x^5 - x - 1 IS Bring form. The organ must recognise that rather than hunt for a cubic
        // transform, and the transform it returns is the identity shift.
        let problem = quintic("x^5-x-1", &[-1, -1, 0, 0, 0, 1]);
        let atlas = read_quintic_charts(&problem, 41, TEST_HORN_LOCAL_SECTION_LIMIT).unwrap();
        let transport = atlas
            .bring
            .transport()
            .expect("an already-Bring source transports linearly");
        assert_eq!(transport.transport.degree(), Some(1));
        assert_eq!(transport.transported, atlas.monic_source);
        for degree in [4_usize, 3, 2] {
            assert!(transport.transported.coefficient(degree).is_zero());
        }
        assert!(transport.certificate.holds());
    }

    #[test]
    fn the_discriminant_agrees_with_the_inherited_integer_discriminant() {
        // The chart's own Sylvester/Bareiss discriminant over Q must reproduce what
        // `IntegralQuinticProblem::normalize` computes over Z through a different code path.
        for coefficients in [
            &[-1_i64, -1, 0, 0, 0, 1][..],
            &[-2, 0, 0, 0, 0, 1][..],
            &[1, 3, -3, -4, 1, 1][..],
        ] {
            let problem = quintic("discriminant-probe", coefficients);
            let normalized = problem.normalize().unwrap();
            let source = RationalPolynomial::from_integers(&normalized.coefficients);
            assert_eq!(
                univariate_discriminant(&source).unwrap(),
                Rat::from_integer(normalized.discriminant.clone())
            );
        }
    }
}

// -------------------------------------------------------------------------------------------------
// The compass rung, and the ladder the two rungs make
// -------------------------------------------------------------------------------------------------

/// **What the straightedge-and-compass rung says about a declared integer polynomial.**
///
/// The compass field is `crate::multiquadratic`'s: a tower of quadratic extensions, degree `2ⁿ`,
/// Galois group `(ℤ/2)ⁿ`. So a root reachable by compass has minimal-polynomial degree a power of
/// two, and **the direction of that implication is the whole content of this enum**.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CompassVerdict {
    /// **REFUSED, exactly and completely.** The polynomial is certified irreducible of a degree that
    /// is not a power of two, so no root of it lies in any tower of quadratic extensions. No bound
    /// this body declares can move this: it is a property of the field, not of a search.
    Refuses { degree: usize, certifying_prime: u64 },
    /// **The necessary condition holds, and that is all this says.** The degree is a power of two.
    /// Sufficiency requires the Galois closure to be a 2-group, which this function does not decide
    /// — a degree-four irreducible with Galois group `A₄` or `S₄` passes here and is *not*
    /// constructible. Reported as necessary-only rather than as an admission.
    NecessaryConditionHolds { degree: usize, tower_bound: u64 },
    /// Irreducibility was not certified over the declared receiver family, so the minimal-polynomial
    /// degree is unknown and no verdict is available. An `Open` is a return.
    Open { degree: usize },
}

impl CompassVerdict {
    pub fn label(&self) -> &'static str {
        match self {
            Self::Refuses { .. } => "REFUSES",
            Self::NecessaryConditionHolds { .. } => "NECESSARY-ONLY",
            Self::Open { .. } => "OPEN",
        }
    }

    /// Whether this rung refused. Deliberately not an `is_constructible`: the positive side of this
    /// verdict is necessary and not sufficient, and a method named for admission would invite a
    /// caller to read it as one.
    pub fn refuses(&self) -> bool {
        matches!(self, Self::Refuses { .. })
    }
}

/// **Read the compass rung on a declared problem.**
///
/// Irreducibility is taken from the same certified source the radical rung uses, so the two rungs
/// answer about the *same* object under the *same* receiver family and their disagreement is about
/// the instrument rather than about the material.
pub fn read_compass_rung(reading: &RadicalChartReading) -> CompassVerdict {
    let degree = reading.degree;
    match &reading.irreducibility {
        QuinticIrreducibility::CertifiedByPrime { prime, .. } => {
            let prime = *prime;
            if crate::multiquadratic::admits_degree(degree) {
                CompassVerdict::NecessaryConditionHolds {
                    degree,
                    tower_bound: 1u64 << degree.trailing_zeros(),
                }
            } else {
                CompassVerdict::Refuses {
                    degree,
                    certifying_prime: prime,
                }
            }
        }
        QuinticIrreducibility::Open => CompassVerdict::Open { degree },
    }
}

/// **One object read by two instruments**, so that a disagreement is legible as an aperture
/// difference and not as a defect in either rung.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LadderReading {
    pub degree: usize,
    pub compass: CompassVerdict,
    pub radical: RadicalChartVerdict,
}

impl LadderReading {
    /// **The rungs disagree**: one instrument refuses what the other returns.
    ///
    /// This is the ladder's whole point. `2^(1/3)` is refused by the compass — the Delian constant is
    /// not a Euclidean number — and returned by radicals, because every cubic is solvable. Neither
    /// verdict is wrong and neither instrument is better; **the aperture belongs to the instrument.**
    pub fn rungs_disagree(&self) -> bool {
        self.compass.refuses() && matches!(self.radical, RadicalChartVerdict::Returns(_))
    }

    pub fn written(&self) -> String {
        format!(
            "degree {} — compass {} · radical {}",
            self.degree,
            self.compass.label(),
            self.radical.label()
        )
    }
}

/// Read both rungs of the instrument ladder on one fiber.
pub fn read_ladder(reading: &RadicalChartReading) -> LadderReading {
    LadderReading {
        degree: reading.degree,
        compass: read_compass_rung(reading),
        radical: reading.verdict.clone(),
    }
}
