//! **The machine as chaser: the population reads the runner, and each motion is released through
//! the one decision law or its declared cornering arm** (THE_REBUILD F6, the action phase, and U3's
//! second loop; the record `2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_…`, §6, §12 items 5, 8,
//! 9 and 13, §14.3–§14.4 and §14.10; campaign 4, #27, #148). It replaces the reception's scripted
//! pursuer with the machine, a [`Chaser`] of `holarchy::terrain::pursuit`.
//!
//! [definition; agent-inferred] **The reading.** The machine holds the reception's population
//! (`ChaseFamily`, one family per declared candidate, escape mass `2^(−j)`), joined to the passage's
//! ports as the chaser writes them, and receives the runner's cell after each tick; its **fibre** is
//! the population's selected fibre (`selected_fibre`, the families of greatest posterior, exactly
//! the candidates no received cell contradicted), read uniform, as the posterior is on it. It also
//! carries each candidate's state past the received cells ([`Candidate::receive`]), so a fibre
//! member's law predicts its cell against any chaser position.
//!
//! [definition; agent-inferred] **What a move is worth**, for each admitted motion `u` at tick `t`
//! (the fibre `Θ` split into its observation classes by the cells against the present position
//! `c_t`, each class a common runner motion `r_(t+1)` at `t + 1`):
//! - **capture** `b(u)`: the capture basin over the fibre at the horizon `m` (`pursuit::capture_ticks`,
//!   the Pre recursion on the belief state, robust over every class): the ticks within which the
//!   chaser, moving to `u` and adapting to each later class, captures every member; none past `m`;
//! - **cornering** `K(u) = Σ_(θ ∈ Θ) |tube_n(r^θ_(t+1), f_θ; D(u))|`: the size of each member's viable
//!   tube (its robust viability kernel at horizon `n`, under its own constitution and slip counter
//!   `f_θ`) against the capture reach of the chaser at `u`, zero for a member `u` captures at `t + 1`;
//! - **nearness** `N(u) = Σ_(θ ∈ Θ) ⟨r^θ_(t+1) − x_u, r^θ_(t+1) − x_u⟩`;
//! - **information** `I(u) = I(Θ; Y_t, Y_(t+1) | h, do(u))` (§14.10), with `Θ` uniform and each
//!   member's cells its law's (the escape mass is the population's smoothing for the code, not a
//!   law of the runner): the partition of `Θ` by the pair of cells at `t` and `t + 1` has
//!   `I = log₂|Θ| − (1/|Θ|) Σ_c |c| log₂|c|`, so `I(u) > I(u′)` exactly when
//!   `∏_c |c|^|c| < ∏_c′ |c′|^|c′|`, an integer comparison; no logarithm is formed.
//!
//! [definition; agent-inferred; §12 item 5, §14.3; THE_REBUILD U3] **The decision: the one law's
//! arms, and the cornering arm beside them.**
//! - **The commit** `u*` is the least of the admitted motions in the order `(b(u) certified first,
//!   then b(u), then K(u), then N(u), then the canonical order)`: a certified capture in the fewest
//!   ticks, otherwise the move that corners, shrinking the fibre's viable tubes most, closing ties.
//! - **The probe** `u_p` is the least in `(−I(u), K(u), N(u), canonical order)`. It is **offered**
//!   while the fibre is plural and `I(u_p) > I(u*)`, as a `receiver::release::ObservationProbe`
//!   carrying its [`ProbePartition`]: its class sizes against the commit's, compared exactly as
//!   `∏_c |c|^|c|`.
//! - **The one law** (`receiver::release::release`, `DecisionRule(Release, Ask)` at tolerance zero)
//!   reads **the capture-within-`m` reading over the selected fibre**: its width is zero when the
//!   capture basin certifies `u*` (a strategy that captures every member within `b(u*) ≤ m` ticks:
//!   the reading is constant on the fibre, Lean `Foundation/ReceiverRelease.width_eq_zero_iff`), and
//!   otherwise the discrete band's one. Width zero returns `Released`, the certified capture, whether
//!   or not a probe is offered; beyond it the law asks the offered probe (`Ask`) and holds where none
//!   is offered (`Hold`: the fibre is one member, or no admitted move separates it beyond what `u*`
//!   separates, one future class for the probe's reach).
//! - **The cornering arm, declared separate.** An `Ask` is emitted only when the probe is affordable,
//!   `K(u_p) − K(u*) ≤ d·|Θ|`; the price `d` of a tick is declared in runner motions, the viable-tube
//!   states a probing tick may concede per fibre member against the commit. Where the concession
//!   exceeds the price, or the law holds, the machine commits to `u*` uncertified
//!   ([`MachineRelease::Commit`], carrying the law's return and the cost comparison). This is the
//!   Bellman stop law's one-step comparison of a viable probe against committing (§14.3): **the price
//!   is its separating term**, which no width or tolerance of the one law carries, so it stays its own
//!   arm (THE_REBUILD U3's failure branch).
//! - **No sequential test on accumulated log-odds is run** (F6's law, amended by U3's second loop).
//!   Under the declared deterministic candidate laws with their escape, every member of the selected
//!   fibre has the same likelihood `(1 − η)^n` (Lean `Population.survivors_share_one_likelihood`), so
//!   the log-odds between members are identically zero, and a threshold at most one contradiction's
//!   `log₂((1 − η)(A − 1)/η)` bits is crossed exactly when the fibre is one member, where the law
//!   already holds and the machine commits. The capture reading is coarser than the family's
//!   identity: it certifies the consequence over a plural fibre, where the test would still be
//!   sampling.
//! - **Each emission carries its predicted consequence** (§12 item 9): the leading class's cell (the
//!   largest class, the least cell on a tie) is read against the cell that unfolds; a miss is counted
//!   in the receipt.
//!
//! [definition; agent-inferred] **The plan** ([`Plan`]; THE_REBUILD U4's next loop), the commit
//! order's reading of the fibre:
//! - [`Plan::Robust`], the F6 action phase's rule above: the certificate `b(u)`, robust over the
//!   whole fibre, then `K(u)`, then `N(u)`;
//! - [`Plan::CertifiedExpected`]: the certificate first, and among the moves of the least
//!   certificate the least **expected capture** `E(u)` at the basin's horizon `m`
//!   (`pursuit::expected_ticks`: the members an adaptive strategy leaves uncaptured, then the sum of
//!   the others' capture ticks, the posterior's expectation over the fibre's classes, uniform on the
//!   fibre, then that strategy's own worst case), then `K(u)`, `N(u)`;
//! - [`Plan::Expected`], **the pledged expected plan**: `E(u)` read to the pledge (below) first,
//!   then the certificate, `K(u)`, `N(u)`.
//!
//! [measured] **Why** (the notebook's `hnn_chase diagnose`). On each of the 5 acceptance seeds where
//! the robust plan missed the truth-only least, the regret enters at one tick. On four the move the
//! truth needed tied the released move's certificate (or no move was certified) and the tie went to
//! the fibre-summed tube or, where the tube was flat across the moves, to the fibre-summed nearness;
//! the worst case over the fibre does not read the members it does not bind. On the fifth the truth
//! stood in one of two equally weighted observation classes whose needs part on the runner's cell of
//! that very tick, read only after the move. The expected capture reads every member at its
//! posterior weight.
//!
//! [measured] **The unpledged candidate, run once on a first fresh population** (pinned before the
//! run: 62 chased seeds of `20261101 + s`, `s < 64`; the plan as it stood at commit `7f2c5d4f`, `E`
//! read at `m` every tick and the commit's certificate released as its bound): 574 capture ticks
//! against the robust plan's 594, a regret of 9 against 29 to the truth-only least, and 12 won, 49
//! tied and 1 lost against it. Its release was not a promise it kept by construction (below), so it
//! was not adopted.
//!
//! [measured] **The pledged plan, chosen on the choosing seeds** (`hnn_chase choose 2 12 0
//! robust,certified-expected,expected`, the pinned rule: the least sum of capture ticks, then the
//! most seeds won against both controls, then the least work): the robust plan sums 150 (3 won
//! against both), the certified-then-expected plan 148 (4) and the pledged expected plan 147 (4), each
//! keeping every bound it released (144, 142 and 141 released ticks) and breaking no pledge. The
//! pledged plan's capture ticks equal the unpledged plan's on every choosing seed.
//!
//! [definition; proved-derived; agent-inferred] **What `Released` certifies: the pledge**
//! (THE_REBUILD U4, the pledge's loop). Every plan decides through the same [`release_among`]: the
//! commit in the plan's order, then the one law on the capture reading. A `Released` tick `t`
//! carries its **bound** `B_t` ([`MachineReceipt::certified`]): the ticks within which **the
//! machine's own continuation** captures every member of the fibre. The reading the law decides is
//! `R(θ) = 𝟙[θ captured by t + B_t under the commit and the plan's continuation]`, constant on the
//! fibre exactly when certified. The machine keeps the **pledge**, the deadline
//! `T = min_t (t + B_t)` over its released ticks.
//! - **Robust and certified-then-expected: `B_t = b(u*)`.** The runner's cell names the class `Θ_y`
//!   the fibre shrinks to, and the capture basin's strategy after `u*` captures `Θ_y` within
//!   `b(u*) − 1` ticks from `t + 1`. So the next tick's least certificate is at most `b(u*) − 1`, and
//!   both plans take a move of the least certificate: the bound is kept, the pledge never binds.
//! - **The pledged expected plan: `B_t = W(u*)`**, the expected recursion's own worst case
//!   (`pursuit::ExpectedCapture`: the least worst case among the strategies of the least sum, with
//!   `b(u*) ≤ W(u*) ≤ m`). Before any release `E` is read at the basin's horizon `m`. Once a pledge
//!   `T` stands, `E` is read **to the pledge**, at the depth `T − t − 1`: the horizon is frozen at the
//!   release. [proved-derived] **It keeps its bound.** At the release `E(u*) = (0, S, W)` is attained
//!   by a strategy that captures every member by `t + W`. After the cell the fibre is the class
//!   `Θ_y`, and that strategy's part for `Θ_y` captures it within `W − 1` ticks from `(u*, t + 1)`,
//!   so the recursion's child reads `U = 0` at depth `W − 1`. That child is the least, over the next
//!   tick's admitted moves `u′`, of `E(u′)` read at depth `W − 2 = T − (t + 1) − 1`: exactly the next
//!   tick's reading to the pledge. Its least move therefore has `U = 0`, is certified, and its own
//!   `W′ ≤ W − 1`. The deadline never moves later, each tick the remaining ticks fall by at least
//!   one, and every member is captured by `T`; each later bound is kept by the same argument from
//!   its own tick. The frozen reading is the Bellman value of the constrained problem, the least
//!   expected capture among the strategies that capture every member by `T`, and it continues the
//!   plan's own value from the release: the sum it read there is still attained.
//! - [agent-inferred] **Why the pledge, and why at `W`.** Each alternative fails a law:
//!   - *The commit's certificate `b(u*)` as the expected plan's bound*, with no pledge (the previous
//!     receipt): `E` chooses by a sum, and a sum can fall by delaying the worst member (captures at
//!     ticks `1` and `6` sum `7`, at `4` and `4` sum `8`), so the plan's own strategy may pass
//!     `b(u*)`. [measured] On the 94 seeds read (the 16 choosing and 16 acceptance seeds and the 62
//!     chased seeds of the spent fresh population), none of its 814 released bounds was passed: the
//!     bound held there by the terrain, not by the plan.
//!   - *`W` read with a sliding horizon* (`E` at `m` every tick): time-inconsistent. At `t + 1` the
//!     horizon is `t + 1 + m`, one tick past the release's, and a strategy that captures a member at
//!     `t + 1 + m` may sum fewer ticks than the continuation that captures every member by `t + W`;
//!     the plan takes it, so the bound can slide a tick every tick.
//!   - *A pledge at `b(u*)` with `E` inside it*: kept, but the release tick chose `u*` by a value its
//!     own pledge then forbids (the strategy `E(u*)` reads may need `W(u*) > b(u*)` ticks). The pledge
//!     at `W` continues the value the plan chose by.
//!   - *[`Plan::CertifiedExpected`]* keeps its bound already, reading `E` only among the least
//!     certificate's moves; the choosing seeds decide between it and the pledged plan.
//! - **A broken pledge.** The pledge is conditional on the runner being a member of the fibre at
//!   every tick (the truth in the declared family; then the fibre at `t + 1` is exactly the class its
//!   cell names). Where no admitted move keeps it (no certificate within `T − t`), the runner has left
//!   every member's law: the pledge is **broken**, counted in the receipt
//!   ([`MachineReceipt::broken`]) and dropped, and the plan reads on at `m`.
//!
//! [definition; agent-inferred] **The parameters**: the viable tube's horizon `n`, the capture
//! basin's horizon `m` and the price `d`, chosen on a pinned choosing set of seeds disjoint from the
//! acceptance seeds (the notebook's `hnn_chase choose`), never on the acceptance seeds: `n = 2`,
//! `m = 12`, `d = 0`. [measured] No probe fired on the choosing seeds at any price: at every plural
//! tick either every admitted move carried the same one-tick information or the commit was already
//! among the most informative.
//!
//! [definition] The computational object is the helical pair interaction: the machine and the
//! runner are a pair whose contact quadrance the machine closes by shrinking the runner's viable
//! tube against the walls and low-friction ground. Of the winding guide's six general objects this
//! owner touches **faces and placement** (each candidate's cell face, the fibre's classes) and the
//! **tube** (the viable tube and the passage); the **pair**, the **tower thread** (the classes'
//! restriction), the **helix** and the **cell holonomy** stay attached through the terrain's laws it
//! reads.

use std::collections::BTreeMap;
use std::sync::Arc;

use num_bigint::BigUint;
use num_traits::{One, Zero};

use std::cmp::Ordering;

use super::{ChaseFamily, Population, PopulationError, refuse, selected_fibre};
use crate::geometry::motion::quadrance;
use crate::holarchy::terrain::{
    Basin, BasinMemo, Candidate, Caps, CaptureReach, ChasePorts, ChaseView, Chaser,
    ExpectedCapture, ExpectedMemo, Motion, Moves, Pursuer, RunnerFamily, capture_ticks, classes,
    expected_ticks, viable_tube,
};
use crate::ratio::Rat;
use crate::receiver::face::{DiameterNorm, ReceiverWidth, WidthWitness};
use crate::receiver::release::{
    BeyondTolerance, DecisionRule, LawfulOptions, ObservationProbe, ProbePartition, ReleaseReturn,
    WithinTolerance, partition_product, release,
};

/// [definition] **The machine's declaration** (module header): the declared runner family it reads,
/// the population's escape exponent `j`, the viable tube's horizon `n ≥ 1`, the capture basin's
/// horizon `m ≥ 1` and the price `d` of a probing tick.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MachineDeclaration {
    pub family: RunnerFamily,
    pub escape: u32,
    pub horizon: usize,
    pub basin: usize,
    pub price: u64,
}

/// [definition; agent-inferred] **The plan** (module header): the commit order's reading of the
/// fibre. The default is [`MachineChaser::new`]'s.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Plan {
    /// The certificate over the whole fibre, then the cornering, then the nearness.
    #[default]
    Robust,
    /// The certificate, then the expected capture among the least certificate's moves, then the
    /// cornering and the nearness.
    CertifiedExpected,
    /// **The pledged expected plan**: the expected capture read to the pledge (at the basin's
    /// horizon before any release), then the certificate, the cornering and the nearness; a
    /// release's bound is the expected recursion's own worst case.
    Expected,
}

impl Plan {
    pub fn label(&self) -> &'static str {
        match self {
            Plan::Robust => "robust",
            Plan::CertifiedExpected => "certified, then expected",
            Plan::Expected => "expected, pledged",
        }
    }
}

/// [definition] The declared name of the rule the one law decides the chaser's tick by.
pub const CAPTURE_RULE: &str =
    "certified capture: release at tolerance zero, else ask the offered probe, else hold";

/// [definition] **What the machine released at a tick, by kind** (the receipt's reading of a
/// [`MachineRelease`]).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Release {
    /// The one law's `Released`: a commit the capture basin certified within the horizon.
    Certified,
    /// The cornering arm: an uncertified commit to the cornering move.
    Commit,
    /// The one law's `Ask`: the most informative move, affordable at the declared price.
    Probe,
}

/// [definition] **The cost comparison of the cornering arm**: the probe's concession
/// `K(u_p) − K(u*)` in viable-tube states (zero when the probe corners at least as much) against the
/// price `d·|Θ|`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ProbePrice {
    pub concession: usize,
    pub bound: u128,
}

impl ProbePrice {
    /// Whether the probe is affordable: its concession within the price.
    pub fn affordable(&self) -> bool {
        self.concession as u128 <= self.bound
    }
}

/// [definition] **What the machine released at a tick** (module header): a return of the one law,
/// or its declared cornering arm.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum MachineRelease {
    /// The one law's return, emitted: `Released` at tolerance zero on the capture reading (the
    /// certified capture, the commit), or `Ask` with its partition (the probe, within its price).
    Law(ReleaseReturn),
    /// **The cornering arm** (declared separate): the uncertified commit to the cornering move.
    Commit {
        /// What the one law returned: `Hold` (no probe offered) or the `Ask` the price refused.
        law: ReleaseReturn,
        /// The cost comparison, where a probe was offered.
        price: Option<ProbePrice>,
    },
}

impl MachineRelease {
    /// The release's kind.
    pub fn kind(&self) -> Release {
        match self {
            Self::Law(ReleaseReturn::Ask { .. }) => Release::Probe,
            Self::Law(_) => Release::Certified,
            Self::Commit { .. } => Release::Commit,
        }
    }
}

/// [definition] **The machine's receipt**: per tick its release, the fibre's size and, for a
/// certified release, its **bound** (module header, the pledge): the ticks within which the
/// machine's own continuation captures every member of the fibre; the misses of its predicted
/// consequence; and the pledges broken, ticks where no admitted move kept the pledge (the runner
/// had left every fibre member's law).
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MachineReceipt {
    pub releases: Vec<MachineRelease>,
    pub fibre: Vec<usize>,
    pub certified: Vec<Option<usize>>,
    pub misses: usize,
    pub broken: usize,
}

impl MachineReceipt {
    /// The ticks released as `release`.
    pub fn count(&self, release: Release) -> usize {
        self.releases.iter().filter(|r| r.kind() == release).count()
    }
}

/// **The machine as chaser** (module header).
pub struct MachineChaser {
    declaration: MachineDeclaration,
    plan: Plan,
    ports: Option<Arc<ChasePorts>>,
    population: Option<Population>,
    candidates: Vec<Candidate>,
    pursuer: Option<(Pursuer, Caps, Moves)>,
    predicted: Option<usize>,
    /// The pledge (module header): the tick by which every fibre member is captured, once released.
    pledge: Option<u64>,
    receipt: MachineReceipt,
}

/// A move's reading (module header): `b(u)`, `K(u)`, `N(u)`, and the class sizes of the fibre's
/// partition by the cells at `t` and `t + 1` with their product `∏_c |c|^|c|` (empty and one while
/// the fibre is one member).
struct Worth {
    capture: Option<usize>,
    expected: Option<ExpectedCapture>,
    cornering: usize,
    nearness: i64,
    classes: Vec<usize>,
    information: BigUint,
}

/// The certificate's key: a certified capture first, in the fewest ticks.
fn certificate(w: &Worth) -> (bool, Option<usize>) {
    (w.capture.is_none(), w.capture)
}

/// **The plan's commit order** (module header, [`Plan`]) on two motions' readings.
fn commit_order(plan: Plan, a: &Worth, b: &Worth) -> Ordering {
    let tail = |w: &Worth| (w.cornering, w.nearness);
    match plan {
        Plan::Robust => (certificate(a), tail(a)).cmp(&(certificate(b), tail(b))),
        Plan::CertifiedExpected => {
            (certificate(a), a.expected, tail(a)).cmp(&(certificate(b), b.expected, tail(b)))
        }
        Plan::Expected => {
            (a.expected, certificate(a), tail(a)).cmp(&(b.expected, certificate(b), tail(b)))
        }
    }
}

/// **The release among the admitted motions' readings** (module header): the commit in the plan's
/// order, the probe the owner offers, the one law's decision at tolerance zero on the capture
/// reading, and the cornering arm's cost comparison. Returns the release and the index of the motion
/// it emits.
fn release_among(
    worths: &[Worth],
    plan: Plan,
    fibre: usize,
    price: u64,
) -> Result<(MachineRelease, usize), PopulationError> {
    let commit = (0..worths.len())
        .min_by(|&i, &j| commit_order(plan, &worths[i], &worths[j]))
        .ok_or_else(|| {
            refuse(
                "a machine chaser's decision",
                "its admitted motions are not empty",
            )
        })?;
    let probe = (0..worths.len())
        .min_by(|&a, &b| {
            let (wa, wb) = (&worths[a], &worths[b]);
            (&wa.information, wa.cornering, wa.nearness).cmp(&(
                &wb.information,
                wb.cornering,
                wb.nearness,
            ))
        })
        .filter(|&p| fibre > 1 && worths[p].information < worths[commit].information);
    let offered = match probe {
        Some(p) => Some(ObservationProbe {
            observation: format!("admitted motion {p} of {}", worths.len()),
            partition: ProbePartition::new(
                worths[p].classes.clone(),
                worths[commit].classes.clone(),
            )?,
        }),
        None => None,
    };
    let certified = worths[commit].capture.is_some();
    let width = ReceiverWidth::declared(
        "capture within the released bound under the commit and the machine's own continuation",
        "the population's selected fibre",
        DiameterNorm::Supremum,
        if certified { Rat::zero() } else { Rat::one() },
        if certified {
            WidthWitness::Point
        } else {
            WidthWitness::Coordinate { coordinate: 0 }
        },
        fibre,
    )?;
    let options = LawfulOptions::assemble(&width, Rat::zero(), offered, true)?;
    let rule = DecisionRule::new(CAPTURE_RULE, WithinTolerance::Release, BeyondTolerance::Ask);
    match (release(&rule, &options)?, probe) {
        (law @ ReleaseReturn::Released { .. }, _) => Ok((MachineRelease::Law(law), commit)),
        (law @ ReleaseReturn::Ask { .. }, Some(p)) => {
            let cost = ProbePrice {
                concession: worths[p].cornering.saturating_sub(worths[commit].cornering),
                bound: u128::from(price) * fibre as u128,
            };
            if cost.affordable() {
                Ok((MachineRelease::Law(law), p))
            } else {
                Ok((
                    MachineRelease::Commit {
                        law,
                        price: Some(cost),
                    },
                    commit,
                ))
            }
        }
        (ReleaseReturn::Hold, _) => Ok((
            MachineRelease::Commit {
                law: ReleaseReturn::Hold,
                price: None,
            },
            commit,
        )),
        _ => Err(refuse(
            "a machine chaser's decision",
            "the capture rule returns a release, the offered probe or a hold",
        )),
    }
}

/// **A certified commit's bound** (module header, the pledge): the commit's certificate `b(u*)`
/// under the robust and certified-then-expected plans, the expected recursion's own worst case
/// `W(u*)` under the pledged expected plan; refused where the commit is not certified, or the
/// expected reading leaves a member uncaptured beside a certificate (the two readings disagree).
fn released_bound(plan: Plan, commit: &Worth) -> Result<usize, PopulationError> {
    let disagree = || {
        refuse(
            "a machine chaser's released bound",
            "the commit is certified, and under the pledged expected plan its reading captures every member",
        )
    };
    let certificate = commit.capture.ok_or_else(disagree)?;
    match plan {
        Plan::Robust | Plan::CertifiedExpected => Ok(certificate),
        Plan::Expected => match commit.expected {
            Some(e) if e.uncaptured == 0 && certificate <= e.worst => Ok(e.worst),
            _ => Err(disagree()),
        },
    }
}

impl MachineChaser {
    /// The machine of a declaration under the default plan ([`Plan::default`]); refused at a
    /// horizon of zero.
    pub fn new(declaration: MachineDeclaration) -> Result<Self, PopulationError> {
        Self::planning(declaration, Plan::default())
    }

    /// The machine of a declaration under a plan; refused at a horizon of zero.
    pub fn planning(declaration: MachineDeclaration, plan: Plan) -> Result<Self, PopulationError> {
        if declaration.horizon == 0 || declaration.basin == 0 {
            return Err(refuse(
                "a machine chaser's horizons",
                "each is at least one tick",
            ));
        }
        Ok(Self {
            declaration,
            plan,
            ports: None,
            population: None,
            candidates: Vec::new(),
            pursuer: None,
            predicted: None,
            pledge: None,
            receipt: MachineReceipt::default(),
        })
    }

    pub fn receipt(&self) -> &MachineReceipt {
        &self.receipt
    }

    /// The machine's plan.
    pub fn plan(&self) -> Plan {
        self.plan
    }

    /// **The pledge** (module header): the tick by which every fibre member is captured, once a
    /// release stands.
    pub fn pledge(&self) -> Option<u64> {
        self.pledge
    }

    /// The population it reads, once opened.
    pub fn population(&self) -> Option<&Population> {
        self.population.as_ref()
    }

    /// **The fibre**: the population's selected fibre, every candidate when none is selected.
    pub fn fibre(&self) -> Vec<usize> {
        let fibre = self
            .population
            .as_ref()
            .map(selected_fibre)
            .unwrap_or_default();
        if fibre.is_empty() {
            (0..self.candidates.len()).collect()
        } else {
            fibre
        }
    }

    /// **A move's worth** (module header).
    fn worth(
        &self,
        basin: &Basin<'_>,
        memo: &mut BasinMemo,
        parts: &[(usize, Vec<Candidate>)],
        next: Motion,
        tick: u64,
        plural: bool,
    ) -> Result<Worth, PopulationError> {
        let horizon = self.declaration.horizon;
        let capture = capture_ticks(basin, memo, parts, next, tick, self.declaration.basin - 1)?;
        let reach = CaptureReach::of(
            basin.arena,
            basin.pursuer,
            basin.caps,
            basin.disk,
            next,
            horizon,
        )?;
        let mut tubes: BTreeMap<(usize, i64, Vec<i64>, u64), usize> = BTreeMap::new();
        let (mut cornering, mut nearness) = (0usize, 0i64);
        let mut sizes: Vec<usize> = Vec::new();
        for (part, (_, class)) in parts.iter().enumerate() {
            let motion = class[0].state.motion;
            let gap = quadrance([
                motion.position[0] - next.position[0],
                motion.position[1] - next.position[1],
            ]);
            nearness += gap * class.len() as i64;
            if !basin.pursuer.captures(motion.position, next.position) {
                for member in class {
                    let caps = &member.law.caps;
                    let key = (part, caps.speed, caps.classes.clone(), member.state.held);
                    let size = match tubes.get(&key) {
                        Some(&size) => size,
                        None => {
                            let size =
                                viable_tube(basin.arena, caps, motion, member.state.held, &reach)?
                                    .size();
                            tubes.insert(key, size);
                            size
                        }
                    };
                    cornering += size;
                }
            }
            if plural {
                for (_, split) in classes(basin.arena, basin.moves, class, next.position, tick + 1)?
                {
                    sizes.push(split.len());
                }
            }
        }
        let information = partition_product(&sizes);
        Ok(Worth {
            capture,
            expected: None,
            cornering,
            nearness,
            classes: sizes,
            information,
        })
    }
}

impl Chaser for MachineChaser {
    type Error = PopulationError;

    fn label(&self) -> String {
        format!(
            "the machine (tube horizon {}, basin horizon {}, price {}, plan {})",
            self.declaration.horizon,
            self.declaration.basin,
            self.declaration.price,
            self.plan.label()
        )
    }

    fn open(&mut self, ports: &Arc<ChasePorts>, pursuer: &Pursuer) -> Result<(), PopulationError> {
        let family = &self.declaration.family;
        self.population = Some(Population::new(ChaseFamily::declare_on(
            ports,
            family,
            self.declaration.escape,
        )?)?);
        self.candidates = Candidate::opening(family, &ports.arena, ports.opening.position)?;
        let caps = pursuer.law.caps(ports.arena.declaration())?;
        let disk = Moves::within(caps.top())?;
        self.pursuer = Some((pursuer.clone(), caps, disk));
        self.ports = Some(Arc::clone(ports));
        self.predicted = None;
        self.pledge = None;
        self.receipt = MachineReceipt::default();
        Ok(())
    }

    fn decide(&mut self, view: &ChaseView<'_>) -> Result<Motion, PopulationError> {
        let (Some(ports), Some((pursuer, caps, disk))) = (&self.ports, &self.pursuer) else {
            return Err(refuse(
                "a machine chaser's decision",
                "it has opened on the passage's ports",
            ));
        };
        let tick = view.tick as u64;
        let fibre: Vec<Candidate> = self
            .fibre()
            .into_iter()
            .map(|index| self.candidates[index].clone())
            .collect();
        let plural = fibre.len() > 1;
        let parts = classes(
            &ports.arena,
            &ports.moves,
            &fibre,
            view.chaser.position,
            tick,
        )?;
        let basin = Basin {
            arena: &ports.arena,
            moves: &ports.moves,
            pursuer,
            caps,
            disk,
        };
        let admitted = view.admitted()?;
        let mut memo = BasinMemo::default();
        let mut worths = Vec::with_capacity(admitted.len());
        for &next in &admitted {
            worths.push(self.worth(&basin, &mut memo, &parts, next, tick, plural)?);
        }
        // The pledge is kept while some admitted move is certified within its remaining ticks;
        // otherwise the runner has left every member's law, and the pledge is broken and dropped.
        if let Some(deadline) = self.pledge {
            let remaining = deadline.saturating_sub(tick);
            if !worths
                .iter()
                .any(|w| w.capture.is_some_and(|b| b as u64 <= remaining))
            {
                self.receipt.broken += 1;
                self.pledge = None;
            }
        }
        // The expected capture's depth: to the pledge under the pledged expected plan (the horizon
        // frozen at the release), the basin's horizon otherwise.
        let depth = match (self.plan, self.pledge) {
            (Plan::Expected, Some(deadline)) => (deadline - tick - 1) as usize,
            _ => self.declaration.basin - 1,
        };
        let reads = |w: &Worth| match self.plan {
            Plan::Robust => false,
            Plan::CertifiedExpected => Some(certificate(w)) == worths.iter().map(certificate).min(),
            Plan::Expected => true,
        };
        let reading: Vec<bool> = worths.iter().map(reads).collect();
        let mut expected_memo = ExpectedMemo::default();
        for (i, worth) in worths.iter_mut().enumerate() {
            if reading[i] {
                worth.expected = Some(expected_ticks(
                    &basin,
                    &mut expected_memo,
                    &parts,
                    admitted[i],
                    tick,
                    depth,
                )?);
            }
        }
        let (released, chosen) =
            release_among(&worths, self.plan, fibre.len(), self.declaration.price)?;
        self.predicted = parts
            .iter()
            .max_by(|a, b| a.1.len().cmp(&b.1.len()).then(b.0.cmp(&a.0)))
            .map(|(cell, _)| *cell);
        let bound = match released.kind() {
            Release::Certified => Some(released_bound(self.plan, &worths[chosen])?),
            _ => None,
        };
        if let Some(bound) = bound {
            let deadline = tick + bound as u64;
            self.pledge = Some(self.pledge.map_or(deadline, |pledge| pledge.min(deadline)));
        }
        self.receipt.certified.push(bound);
        self.receipt.releases.push(released);
        self.receipt.fibre.push(fibre.len());
        Ok(admitted[chosen])
    }

    fn receive(&mut self, cell: usize) -> Result<(), PopulationError> {
        let (Some(ports), Some(population)) = (&self.ports, &mut self.population) else {
            return Err(refuse(
                "a machine chaser's reception",
                "it has opened on the passage's ports",
            ));
        };
        population.receive(cell)?;
        self.candidates = self
            .candidates
            .iter()
            .map(|candidate| candidate.receive(&ports.arena, &ports.moves, cell))
            .collect::<Result<_, _>>()?;
        if self.predicted.is_some_and(|predicted| predicted != cell) {
            self.receipt.misses += 1;
        }
        Ok(())
    }
}

#[cfg(test)]
#[path = "chaser_tests.rs"]
mod tests;
