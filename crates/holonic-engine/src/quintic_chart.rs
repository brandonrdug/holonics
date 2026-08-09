//! The Tschirnhaus organ: transport a quintic to another chart, exhibit the transport, and refuse
//! — with the obstruction named — when the target chart cannot represent the answer.
//!
//! `canon/TABLET_THE_CHART.md:280` states the owed construction verbatim:
//!
//! > *"a Tschirnhaus organ. Take a degree-5 input, transport it to Bring form by an exact rational
//! > chart change, return the transported form and the transport, and refuse — with the obstruction
//! > named — when the target chart cannot represent the answer."*
//!
//! and §3.4 states why it matters: **the quintic is solvable; it is not solvable *in the radical
//! chart*.** Galois theory does not say "unsolvable". It says "not in this chart" and hands you the
//! obstruction group. Everything below is built so that a refusal is a *return carrying evidence*
//! and never a bool, never a panic, and never a tolerance.
//!
//! ## What a chart is here, and what a transport is
//!
//! A Tschirnhaus transform is an element `g` of `Q[x]/(f)`. It carries the root population
//! `{x_1..x_5}` of `f` to `{g(x_1)..g(x_5)}`, whose monic polynomial is
//!
//! ```text
//!   F(y) = prod_i (y - g(x_i))  =  Res_x( f(x), y - g(x) )
//! ```
//!
//! No root is ever computed. `F` is obtained from the power sums of `f` by the Newton identities:
//! `p_k = sum_i g(x_i)^k = sum_m [g^k]_m * s_m`, where `[g^k]_m` is the ordinary `m`-th coefficient
//! of the `k`-th power of `g` **as a polynomial**, and `s_m` are `f`'s own power sums. That identity
//! is why the whole organ needs no modular reduction and no linear algebra: raising a polynomial to
//! a power and pairing it against a fixed vector is the entire transport.
//!
//! The resultant is then computed **again, independently**, by fraction-free Bareiss elimination on
//! the Sylvester matrix over `Q[y]`, and the two must agree coefficient for coefficient. Two
//! independent implementations of the same object, per `CLAUDE.md` §8, with both work vectors
//! reported. A third, sharper check runs alongside: `F(g(x))` reduced modulo `f(x)` must be
//! **identically zero** — that is the transport verified by literal substitution, over `Q`.
//!
//! ## The chart family, and where each one refuses
//!
//! ```text
//!   depressed   kill x^4                 a rational shift             ALWAYS returns over Q
//!   principal   kill x^4 and x^3          one auxiliary QUADRATIC     returns iff it has a
//!                                                                     rational root
//!   Bring       kill x^4, x^3 and x^2     eliminate one parameter,    returns iff the resultant
//!                                         an auxiliary of degree <=6  has a rational root whose
//!                                                                     partner is also rational
//!   radical     write the roots           the monodromy population    refuses when every admitted
//!                                                                     group is non-solvable
//! ```
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
//!   `c_3 = 1` (cubic, where `c_1` is eliminated by a resultant). Three homogeneous conditions in
//!   `P^2` meet in six points by Bezout, which is also why the classical Bring reduction costs a
//!   square root and a cube root: six is `2 * 3`.
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

use num_bigint::BigInt;
use num_traits::{One, Zero};
use relational_geometry::Rat;
use serde::{Deserialize, Serialize};
use thiserror::Error;

use crate::arithmetic_fiber::ArithmeticFiberEvent;
use crate::arithmetic_monodromy::{
    ArithmeticMonodromyError, ArithmeticMonodromyEvent, ArithmeticMonodromyLaw,
    ArithmeticMonodromyStanding, IntegralQuinticProblem, QuinticIrreducibility,
    QuinticTransitiveGroup,
};
use crate::causal::EventId;
use crate::rational_polynomial::{
    BivariatePolynomial, CensusWork, ExactPolynomialError, RationalPolynomial, RationalRootCensus,
    ResultantWork, monic_from_power_sums, newton_power_sums, rational_root_census,
    resultant_in_eliminated_variable,
};
use crate::world::CausalWorld;

const QUINTIC_DEGREE: usize = 5;
const CHART_PROBLEM_EVENT: EventId = EventId(1_000_000_000);

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
    pub fn name(self) -> &'static str {
        match self {
            Self::Radical => "radical",
            Self::Depressed => "depressed",
            Self::Principal => "principal",
            Self::Bring => "bring",
        }
    }

    /// The coefficients this chart's transported form must carry as exact zero.
    pub fn killed_degrees(self) -> &'static [usize] {
        match self {
            Self::Radical => &[],
            Self::Depressed => &[4],
            Self::Principal => &[4, 3],
            Self::Bring => &[4, 3, 2],
        }
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
    pub source: RationalPolynomial,
    /// The Tschirnhaus transform `g`, exactly, ascending in degree.
    pub transport: RationalPolynomial,
    pub transported: RationalPolynomial,
    /// Which coefficients this chart promised to kill, and their exact returned values.
    pub killed: BTreeMap<usize, Rat>,
    pub aperture: String,
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
    /// The radical chart. Every transitive group the monodromy fiber still admits is non-solvable,
    /// so no stack of one-winding-at-a-time forgettings reaches the roots.
    NonSolvableMonodromy {
        admitted: BTreeSet<QuinticTransitiveGroup>,
        irreducibility: QuinticIrreducibility,
        /// The obstruction, named.
        named: String,
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
    /// The depressed form is a binomial `y^5 + q`. The five roots are the fifth roots of `-q` times
    /// the fifth roots of unity, and the chart writes them out.
    DepressedBinomial {
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
    pub prime_limit: u64,
    pub discriminant: BigInt,
    pub discriminant_is_square: bool,
    pub irreducibility: QuinticIrreducibility,
    pub observed_cycle_types: BTreeMap<Vec<u32>, BTreeSet<u64>>,
    pub admitted_groups: BTreeSet<QuinticTransitiveGroup>,
    pub solvable_admitted: BTreeSet<QuinticTransitiveGroup>,
    pub nonsolvable_admitted: BTreeSet<QuinticTransitiveGroup>,
    /// The rational-root receiver's complete return on the normalised monic source.
    pub rational_roots: Vec<Rat>,
    pub residual_degree_after_deflation: usize,
    /// Present exactly when the depressed form is `y^5 + q`.
    pub depressed_binomial_constant: Option<Rat>,
    pub verdict: RadicalChartVerdict,
}

impl RadicalChartReading {
    /// The transitive-group fiber classifies an **irreducible** quintic. Until irreducibility is
    /// certified by a prime whose reduction stays irreducible of degree five, the catalogue is
    /// conditional and an empty candidate set means "obstructed", not "no group".
    pub fn transitive_receiver_applies(&self) -> bool {
        matches!(
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
    /// certainty neither side has.
    ///
    /// When irreducibility is not certified the transitive catalogue does not apply at all — its
    /// own owner says so — and agreement is then the requirement that the chart did **not refuse on
    /// the catalogue's authority**. Reading a receiver outside its declared aperture is the defect
    /// `CLAUDE.md` §8 convicts, and a refusal is the one verdict that would be doing it.
    pub fn agrees_with_group_fiber(&self) -> bool {
        if !self.transitive_receiver_applies() {
            return !matches!(self.verdict, RadicalChartVerdict::Refuses(_));
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

/// One quintic, read through every chart this organ owns.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct QuinticChartAtlas {
    pub problem: IntegralQuinticProblem,
    /// `g(y) = a_5^4 f(y/a_5)`, monic over `Z`, which preserves the splitting field.
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

/// Read one integral quintic through the whole chart family.
pub fn read_quintic_charts(
    problem: &IntegralQuinticProblem,
    prime_limit: u64,
) -> Result<QuinticChartAtlas, QuinticChartError> {
    let normalized = problem.normalize()?;
    let monic_source = RationalPolynomial::from_integers(&normalized.coefficients);
    if monic_source.degree() != Some(QUINTIC_DEGREE) || !monic_source.is_monic() {
        return Err(QuinticChartError::NotAMonicQuintic);
    }
    // The Bring chart uses a cubic transform, so it needs power sums up to 3 * 3 = 9; the
    // transported form needs 5 * 3 = 15.
    let power_sums = newton_power_sums(&monic_source, 3 * QUINTIC_DEGREE)?;

    let mut obstructions = Vec::new();
    let depressed = depressed_chart(&monic_source, &power_sums)?;
    if let Some(obstruction) = depressed.obstruction() {
        obstructions.push(obstruction.clone());
    }
    let principal = principal_chart(&monic_source, &power_sums, &mut obstructions)?;
    if let Some(obstruction) = principal.obstruction() {
        obstructions.push(obstruction.clone());
    }
    let bring = bring_chart(&monic_source, &power_sums, &mut obstructions)?;
    if let Some(obstruction) = bring.obstruction() {
        obstructions.push(obstruction.clone());
    }

    let radical = radical_chart(problem, &monic_source, &depressed, prime_limit)?;
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
fn transported_form(
    transform: &RationalPolynomial,
    source_power_sums: &[Rat],
) -> Result<(RationalPolynomial, CensusWork), QuinticChartError> {
    let mut work = CensusWork::default();
    let mut sums = vec![Rat::from_integer(BigInt::from(QUINTIC_DEGREE))];
    for order in 1..=QUINTIC_DEGREE {
        work.exact_evaluations += 1;
        sums.push(transported_power_sum(transform, source_power_sums, order)?);
    }
    let form = monic_from_power_sums(&sums, QUINTIC_DEGREE)?;
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
    let degree = monic.degree().ok_or(QuinticChartError::NotAMonicQuintic)?;
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
fn certified_transport(
    chart: QuinticChart,
    source: &RationalPolynomial,
    source_power_sums: &[Rat],
    source_discriminant: &Rat,
    transform: RationalPolynomial,
    aperture: &str,
    auxiliary: Vec<AuxiliaryStep>,
) -> Result<ChartOutcome, QuinticChartError> {
    let (transported, newton_work) = transported_form(&transform, source_power_sums)?;
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
        .killed_degrees()
        .iter()
        .map(|degree| (*degree, transported.coefficient(*degree)))
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
        source: source.clone(),
        transport: transform,
        transported,
        killed,
        aperture: aperture.to_owned(),
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
/// `p_1 = C_0 s_0 + sum_{j>=1} C_j s_j`, and `s_0` is the degree five, so this elimination is
/// available over `Q` unconditionally. It is the one step of every chart that never refuses.
fn eliminate_constant_univariate(
    higher: &[RationalPolynomial],
    power_sums: &[Rat],
) -> RationalPolynomial {
    let five = Rat::from_integer(BigInt::from(QUINTIC_DEGREE));
    let mut total = RationalPolynomial::zero();
    for (index, coefficient) in higher.iter().enumerate() {
        total = total.plus(&coefficient.scaled(&power_sums[index + 1]));
    }
    total.scaled(&(-Rat::one() / &five))
}

fn eliminate_constant_bivariate(
    higher: &[BivariatePolynomial],
    power_sums: &[Rat],
) -> BivariatePolynomial {
    let five = Rat::from_integer(BigInt::from(QUINTIC_DEGREE));
    let mut total = BivariatePolynomial::zero();
    for (index, coefficient) in higher.iter().enumerate() {
        total = total.plus(&coefficient.scaled_by_rational(&power_sums[index + 1]));
    }
    total.scaled_by_rational(&(-Rat::one() / &five))
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

/// Kill `x^4`. `p_1 = 5 c_0 + s_1 = 0` has the single rational solution `c_0 = -s_1 / 5`, so this
/// chart change is available over `Q` for every quintic and refuses nothing.
fn depressed_chart(
    source: &RationalPolynomial,
    power_sums: &[Rat],
) -> Result<ChartOutcome, QuinticChartError> {
    let coefficients = pinned_coefficients(&[Rat::one()], power_sums);
    let transform = instantiate(&coefficients, &Rat::zero());
    let discriminant = univariate_discriminant(source)?;
    certified_transport(
        QuinticChart::Depressed,
        source,
        power_sums,
        &discriminant,
        transform,
        "rational shift g = x + c_0; the condition is linear with leading coefficient s_0 = 5",
        Vec::new(),
    )
}

// ---------------------------------------------------------------------------------------------
// the principal chart
// ---------------------------------------------------------------------------------------------

const PRINCIPAL_APERTURE: &str = "transforms of degree at most two up to projective scale, \
    [c_1 : c_2] in P^1 with c_0 eliminated by p_1 = 0; searched through the two declared affine \
    sub-charts c_2 = 0 (linear) and c_2 = 1 (quadratic), lowest transform degree first";

/// Kill `x^4` and `x^3`.
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
    power_sums: &[Rat],
    obstructions: &mut Vec<ChartObstruction>,
) -> Result<ChartOutcome, QuinticChartError> {
    let discriminant = univariate_discriminant(source)?;

    // Sub-chart c_2 = 0: g = x + c_0, no free parameter. The condition is p_2 = 0 outright.
    let linear = pinned_coefficients(&[Rat::one()], power_sums);
    let linear_condition = univariate_power_sum(&linear, power_sums, 2)?;
    if linear_condition.is_zero() {
        let transform = instantiate(&linear, &Rat::zero());
        let outcome = certified_transport(
            QuinticChart::Principal,
            source,
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
            power_sums,
            &discriminant,
            transform,
            PRINCIPAL_APERTURE,
            Vec::new(),
        );
    }
    let degree = auxiliary
        .degree()
        .expect("a nonzero polynomial has a degree");
    if degree == 0 {
        return Ok(ChartOutcome::Refused(ChartObstruction {
            chart: QuinticChart::Principal,
            step: "kill x^3".to_owned(),
            species: ChartObstructionSpecies::AuxiliaryHasNoRoot {
                parameter: "c_1".to_owned(),
                auxiliary,
            },
        }));
    }
    let quadratic_discriminant = (degree == 2).then(|| {
        let a = auxiliary.coefficient(2);
        let b = auxiliary.coefficient(1);
        let c = auxiliary.coefficient(0);
        &b * &b - Rat::from_integer(BigInt::from(4)) * a * c
    });
    let census = rational_root_census(&auxiliary)?;
    if census.rational_roots.is_empty() {
        return Ok(ChartOutcome::Refused(ChartObstruction {
            chart: QuinticChart::Principal,
            step: "kill x^3".to_owned(),
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
            step: "kill x^3".to_owned(),
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

/// Kill `x^4`, `x^3` and `x^2`, reaching Bring–Jerrard form `y^5 + p y + q`.
///
/// Three homogeneous conditions of degrees one, two and three live on the transform's projective
/// parameter space. `p_1 = 0` is linear and eliminates `c_0`, leaving a conic and a cubic in the
/// `P^2` of `[c_1 : c_2 : c_3]`; by Bezout they meet in six points, which is why a cubic transform
/// is the natural aperture and also why the classical Bring reduction costs a square root and a
/// cube root — six is `2 * 3`.
///
/// All three affine sub-charts are searched, lowest transform degree first, for the same reason the
/// principal chart searches both of its own: a source already in Bring form is solved by the
/// *linear* transform, which lives at the excluded point of the `c_3 = 1` patch.
fn bring_chart(
    source: &RationalPolynomial,
    power_sums: &[Rat],
    obstructions: &mut Vec<ChartObstruction>,
) -> Result<ChartOutcome, QuinticChartError> {
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
/// Three receivers, each exact and each returning a population:
///
/// 1. **rational factorisation** — the complete rational-root census, deflated. A residual degree
///    of at most four is below the wall, so Cardano and Ferrari write the roots.
/// 2. **binomial recognition** — a depressed form `y^5 + q` has its roots written directly as
///    fifth roots. This receiver sees the *transported* form, which is the whole point: the chart
///    change is what makes the radical chart able to read the input at all.
/// 3. **Frobenius cycle types** — the existing [`crate::arithmetic_monodromy`] fiber, restricted by
///    observed cycle types up to `prime_limit`, plus the discriminant-square parity split.
fn radical_chart(
    problem: &IntegralQuinticProblem,
    monic_source: &RationalPolynomial,
    depressed: &ChartOutcome,
    prime_limit: u64,
) -> Result<RadicalChartReading, QuinticChartError> {
    let law = ArithmeticMonodromyLaw::new(1)?;
    let standing = ArithmeticMonodromyStanding::new(1)?;
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

    let depressed_binomial_constant = depressed.transport().and_then(|transport| {
        let form = &transport.transported;
        (1..QUINTIC_DEGREE)
            .all(|degree| form.coefficient(degree).is_zero())
            .then(|| form.coefficient(0))
    });

    let irreducibility_certified = matches!(
        fiber.irreducibility,
        QuinticIrreducibility::CertifiedByPrime { .. }
    );
    let verdict = if residual_degree <= 4 {
        RadicalChartVerdict::Returns(RadicalReturn::BelowTheWall {
            rational_roots: rational_roots.clone(),
            residual_degree,
        })
    } else if let Some(constant) = depressed_binomial_constant.clone() {
        let shift = depressed
            .transport()
            .map(|transport| transport.transport.coefficient(0))
            .unwrap_or_else(Rat::zero);
        let written = (0..QUINTIC_DEGREE)
            .map(|hand| {
                format!(
                    "x_{hand} = zeta_5^{hand} * ({})^(1/5) - ({shift})",
                    -constant.clone()
                )
            })
            .collect();
        RadicalChartVerdict::Returns(RadicalReturn::DepressedBinomial {
            shift,
            constant,
            written,
        })
    } else if !irreducibility_certified {
        // The transitive catalogue classifies an irreducible quintic. Without that certificate the
        // chart may not refuse on the catalogue's authority, so it returns the population it has.
        RadicalChartVerdict::Open {
            solvable: solvable_admitted.clone(),
            nonsolvable: nonsolvable_admitted.clone(),
        }
    } else if !admitted_groups.is_empty() && solvable_admitted.is_empty() {
        RadicalChartVerdict::Refuses(ChartObstruction {
            chart: QuinticChart::Radical,
            step: "write the roots".to_owned(),
            species: ChartObstructionSpecies::NonSolvableMonodromy {
                admitted: admitted_groups.clone(),
                irreducibility: fiber.irreducibility.clone(),
                named: if admitted_groups.contains(&QuinticTransitiveGroup::Alternating5)
                    || admitted_groups.contains(&QuinticTransitiveGroup::Symmetric5)
                {
                    "A_5 is simple: the winding does not factor into single-hand steps".to_owned()
                } else {
                    "no admitted group is solvable".to_owned()
                },
            },
        })
    } else if !solvable_admitted.is_empty() && nonsolvable_admitted.is_empty() {
        RadicalChartVerdict::Returns(RadicalReturn::BelowTheWall {
            rational_roots: rational_roots.clone(),
            residual_degree,
        })
    } else {
        RadicalChartVerdict::Open {
            solvable: solvable_admitted.clone(),
            nonsolvable: nonsolvable_admitted.clone(),
        }
    };

    Ok(RadicalChartReading {
        prime_limit,
        discriminant: fiber.discriminant.clone(),
        discriminant_is_square: fiber.discriminant_square_root.is_some(),
        irreducibility: fiber.irreducibility.clone(),
        observed_cycle_types: fiber.cycle_witnesses.clone(),
        admitted_groups,
        solvable_admitted,
        nonsolvable_admitted,
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
    #[error("the normalized source is not a monic quintic")]
    NotAMonicQuintic,
    #[error("the source power sums do not reach the degree the transform needs")]
    InsufficientPowerSums,
    #[error("the monodromy standing lost the problem it was given")]
    MissingProblemStanding,
}

#[cfg(test)]
mod tests {
    use crate::arithmetic_monodromy::QuinticProblemId;

    use super::*;

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
        let outcome = depressed_chart(&source, &power_sums).unwrap();
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
            let outcome = depressed_chart(&source, &power_sums).unwrap();
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
        let transport = depressed_chart(&source, &power_sums)
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
        let returned = principal_chart(&rational, &rational_sums, &mut retained).unwrap();
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
        let refused = principal_chart(&irrational, &irrational_sums, &mut retained).unwrap();
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
        let outcome = principal_chart(&source, &power_sums, &mut retained).unwrap();
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
        let refused = principal_chart(&source, &power_sums, &mut retained).unwrap();
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
        let atlas = read_quintic_charts(&problem, 41).unwrap();
        for (chart, outcome) in atlas.outcomes() {
            if let Some(transport) = outcome.transport() {
                for degree in chart.killed_degrees() {
                    assert!(
                        transport.transported.coefficient(*degree).is_zero(),
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
        let atlas = read_quintic_charts(&problem, 41).unwrap();
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
        let atlas = read_quintic_charts(&problem, 41).unwrap();
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
        let atlas = read_quintic_charts(&problem, 41).unwrap();
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
        let atlas = read_quintic_charts(&problem, 97).unwrap();
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
        let atlas = read_quintic_charts(&problem, 41).unwrap();
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
            let atlas = read_quintic_charts(&problem, 41).unwrap();
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
        let atlas = read_quintic_charts(&problem, 41).unwrap();
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
        let atlas = read_quintic_charts(&problem, 41).unwrap();
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
