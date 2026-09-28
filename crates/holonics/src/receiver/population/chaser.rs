//! **The machine as chaser: the population reads the runner, and each motion is a threshold
//! commit that corners** (THE_REBUILD F6, the action phase; the record
//! `2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_…`, §6, §12 items 5, 8, 9 and 13, §14.3–§14.4
//! and §14.10; campaign 4, #27, #148). It replaces the reception's scripted pursuer with the machine,
//! a [`Chaser`] of `holarchy::terrain::pursuit`.
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
//! [definition; agent-inferred; §12 item 5, §14.3] **The decision rule: a threshold commit.**
//! - **The commit** `u*` is the least of the admitted motions in the order `(b(u) certified first,
//!   then b(u), then K(u), then N(u), then the canonical order)`: a certified capture in the fewest
//!   ticks, otherwise the move that corners, shrinking the fibre's viable tubes most, closing ties.
//! - **The probe** `u_p` is the least in `(−I(u), K(u), N(u), canonical order)`.
//! - **The threshold.** The statistic is the population's posterior over the fibre's future
//!   classes. The machine commits when the threshold is crossed: when the fibre is one member (its
//!   log-odds against every other candidate at least one contradiction, `12 + log₂(A − 1)` bits),
//!   when the capture basin certifies `u*`, when no admitted move separates the fibre beyond what
//!   `u*` separates (`I(u_p) ≤ I(u*)`: the fibre is one future class for the probe's reach), or when
//!   the probe is not affordable: `K(u_p) − K(u*) > d·|Θ|`.
//! - **The price of a tick** `d` is declared in runner motions: the viable-tube states a probing
//!   tick may concede, per fibre member, against the commit. Otherwise the machine emits the probe.
//! - **Each emission carries its predicted consequence** (§12 item 9): the leading class's cell (the
//!   largest class, the least cell on a tie) is read against the cell that unfolds; a miss is counted
//!   in the receipt.
//!
//! [definition; agent-inferred] **The plan** ([`Plan`]; THE_REBUILD U4's next loop), the commit
//! order's reading of the fibre:
//! - [`Plan::Robust`], the F6 action phase's rule above: the certificate `b(u)`, robust over the
//!   whole fibre, then `K(u)`, then `N(u)`;
//! - [`Plan::CertifiedExpected`]: the certificate first, and among the moves of the least
//!   certificate the least **expected capture** `E(u)` (`pursuit::expected_ticks`: the members an
//!   adaptive strategy leaves uncaptured within `m`, then the sum of the others' capture ticks, the
//!   posterior's expectation over the fibre's classes, uniform on the fibre), then `K(u)`, `N(u)`;
//! - [`Plan::Expected`]: `E(u)` first, then the certificate, `K(u)`, `N(u)`.
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
//! [measured] **The candidate, run once on a fresh population** (the notebook's `hnn_chase fresh`,
//! pinned before the run: 62 chased seeds of `20261101 + s`, `s < 64`): the expected plan (chosen on
//! the choosing seeds, 147 against the robust plan's 150 and the certified-then-expected plan's 148)
//! sums 574 capture ticks against the robust plan's 594, a regret of 9 against 29 to the truth-only
//! least, and wins 12, ties 49 and loses 1 against it. [agent-inferred] [`MachineChaser::new`] stays
//! the robust plan: U3's next loop reproduces the robust receipts through `receiver::release`, and
//! the expected plan's certified release is no longer a promise (the plan may leave the minimax
//! strategy after it), so its arm in the release law is read by that parity first.
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

use std::cmp::Ordering;

use super::{ChaseFamily, Population, PopulationError, refuse, selected_fibre};
use crate::geometry::motion::quadrance;
use crate::holarchy::terrain::{
    Basin, BasinMemo, Candidate, Caps, CaptureReach, ChasePorts, ChaseView, Chaser,
    ExpectedCapture, ExpectedMemo, Motion, Moves, Pursuer, RunnerFamily, capture_ticks, classes,
    expected_ticks, viable_tube,
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
/// fibre.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub enum Plan {
    /// The certificate over the whole fibre, then the cornering, then the nearness.
    #[default]
    Robust,
    /// The certificate, then the expected capture among the least certificate's moves, then the
    /// cornering and the nearness.
    CertifiedExpected,
    /// The expected capture, then the certificate, the cornering and the nearness.
    Expected,
}

impl Plan {
    pub fn label(&self) -> &'static str {
        match self {
            Plan::Robust => "robust",
            Plan::CertifiedExpected => "certified, then expected",
            Plan::Expected => "expected",
        }
    }
}

/// [definition] **What the machine released at a tick.**
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Release {
    /// A commit the capture basin certified within the horizon.
    Certified,
    /// A commit to the cornering move.
    Commit,
    /// A probe: the most informative move, affordable at the declared price.
    Probe,
}

/// [definition] **The machine's receipt**: per tick its release, the fibre's size and, for a
/// certified release, the ticks within which the capture basin certified capture; the misses of
/// its predicted consequence.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct MachineReceipt {
    pub releases: Vec<Release>,
    pub fibre: Vec<usize>,
    pub certified: Vec<Option<usize>>,
    pub misses: usize,
}

impl MachineReceipt {
    /// The ticks released as `release`.
    pub fn count(&self, release: Release) -> usize {
        self.releases.iter().filter(|&&r| r == release).count()
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
    receipt: MachineReceipt,
}

/// A move's reading (module header).
struct Worth {
    capture: Option<usize>,
    expected: Option<ExpectedCapture>,
    cornering: usize,
    nearness: i64,
    information: BigUint,
}

impl MachineChaser {
    /// The machine of a declaration under the robust plan; refused at a horizon of zero.
    pub fn new(declaration: MachineDeclaration) -> Result<Self, PopulationError> {
        Self::planning(declaration, Plan::Robust)
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
            receipt: MachineReceipt::default(),
        })
    }

    pub fn receipt(&self) -> &MachineReceipt {
        &self.receipt
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
        let information = sizes.iter().fold(BigUint::from(1u32), |product, &size| {
            product * BigUint::from(size).pow(size as u32)
        });
        Ok(Worth {
            capture,
            expected: None,
            cornering,
            nearness,
            information,
        })
    }
}

impl Chaser for MachineChaser {
    type Error = PopulationError;

    fn label(&self) -> String {
        let plan = match self.plan {
            Plan::Robust => String::new(),
            plan => format!(", plan {}", plan.label()),
        };
        format!(
            "the machine (tube horizon {}, basin horizon {}, price {}{plan})",
            self.declaration.horizon, self.declaration.basin, self.declaration.price
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
        let certificate = |w: &Worth| (w.capture.is_none(), w.capture);
        let reads = |w: &Worth| match self.plan {
            Plan::Robust => false,
            Plan::CertifiedExpected => {
                Some(certificate(w)) == worths.iter().map(certificate).min()
            }
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
                    self.declaration.basin - 1,
                )?);
            }
        }
        let tail = |w: &Worth| (w.cornering, w.nearness);
        let order = |a: &Worth, b: &Worth| -> Ordering {
            match self.plan {
                Plan::Robust => (certificate(a), tail(a)).cmp(&(certificate(b), tail(b))),
                Plan::CertifiedExpected => (certificate(a), a.expected, tail(a)).cmp(&(
                    certificate(b),
                    b.expected,
                    tail(b),
                )),
                Plan::Expected => (a.expected, certificate(a), tail(a)).cmp(&(
                    b.expected,
                    certificate(b),
                    tail(b),
                )),
            }
        };
        let commit = (0..admitted.len())
            .min_by(|&i, &j| order(&worths[i], &worths[j]))
            .ok_or_else(|| {
                refuse(
                    "a machine chaser's decision",
                    "its admitted motions are not empty",
                )
            })?;
        let mut release = if worths[commit].capture.is_some() {
            Release::Certified
        } else {
            Release::Commit
        };
        let mut chosen = commit;
        if plural && release == Release::Commit {
            let probe = (0..admitted.len())
                .min_by(|&a, &b| {
                    let (wa, wb) = (&worths[a], &worths[b]);
                    (&wa.information, wa.cornering, wa.nearness).cmp(&(
                        &wb.information,
                        wb.cornering,
                        wb.nearness,
                    ))
                })
                .expect("a nonempty admitted set");
            let concession = worths[probe]
                .cornering
                .saturating_sub(worths[commit].cornering);
            let affordable =
                (concession as u128) <= u128::from(self.declaration.price) * (fibre.len() as u128);
            if worths[probe].information < worths[commit].information && affordable {
                release = Release::Probe;
                chosen = probe;
            }
        }
        self.predicted = parts
            .iter()
            .max_by(|a, b| a.1.len().cmp(&b.1.len()).then(b.0.cmp(&a.0)))
            .map(|(cell, _)| *cell);
        self.receipt.releases.push(release);
        self.receipt.fibre.push(fibre.len());
        self.receipt.certified.push(match release {
            Release::Certified => worths[chosen].capture,
            _ => None,
        });
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
