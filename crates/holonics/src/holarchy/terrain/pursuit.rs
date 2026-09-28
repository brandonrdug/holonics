//! **The chase's action phase: the chaser moves, and cornering is read as the runner's robust
//! viability kernel** (THE_REBUILD F6; the record `2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_…`,
//! §6, §13 and §14.4; campaign 4, #27, #148). The terrain's laws the action phase reads: the chaser's
//! capture reach, the runner's viable tube, the capture basin over a fibre of candidate runners, the
//! chaser's port and admissibility, the two controls and the passage. The machine that chases
//! (`receiver::population::chaser`) is a [`Chaser`] reading these.
//!
//! [definition; agent-inferred] **The order of a tick** (as in the reception's [`Chase::run`]): at
//! tick `t` capture is read on the present positions, `⟨x_R − x_C, x_R − x_C⟩ ≤ ρ²`, and ends the
//! passage; otherwise the chaser writes its present motion `c_t` to its port, the runner's cell is
//! read against `c_t`, and both move at once: the runner by its cell, the chaser to the motion it
//! released at `t`. Neither sees the other's move of the same tick.
//!
//! [definition; agent-inferred] **The chaser's admissibility.** Every motion a chaser emits is one
//! of its traction-admitted motions ([`Pursuer::motions`]): its velocity change `Δv` satisfies
//! `⟨Δv, Δv⟩ ≤ (γ_C μ_c g h²/ℓ)²` on the class `c` of the cell it stands on, its velocity
//! `⟨v, v⟩ ≤ v_C²`, and its step stays in the arena. [`act`] refuses any other motion by name, and
//! refuses a chaser that cannot always stop ([`Pursuer::stops`]), so the admitted set is never empty
//! and the wall law never moves the chaser.
//!
//! [proved-derived; the record's §14.4] **The capture reach** ([`CaptureReach`]). From the chaser's
//! motion `c₀`, its reach `C₀ = {c₀}`, `C_(k+1) = ⋃_(c ∈ C_k) admitted(c)`, and the capture reach at
//! tick `k`, `D_k = {x : ∃ c ∈ C_k, ⟨x − x_c, x − x_c⟩ ≤ ρ²}`: every position where some chaser word
//! of `k` ticks captures.
//!
//! [proved-derived; the record's §14.4, agent-inferred horizon] **The runner's viable tube: its
//! robust viability kernel at a bounded horizon `n`** ([`viable_tube`]). The runner's admitted
//! successors `Post(r)` under its constitution: while a slip holds (the first `f` ticks, `f` its
//! held counter) its kept motion; otherwise every `(x + v′, v′)` with `⟨v′ − v, v′ − v⟩` within the
//! traction cap of the cell it stands on, `⟨v′, v′⟩` within its speed cap and `x + v′` inside,
//! and the wall law's motion when none is (the runner as an adversary never demands a slip: a
//! slip's next motion is the rest change's, with fewer options after it). With the safe sets
//! `S_k = {r : x_r ∉ D_k}`, the forward viable reach `F₀ = {r₀} ∩ S₀`, `F_(k+1) = Post(F_k) ∩ S_(k+1)`,
//! and the **Pre recursion** backward over it:
//!
//! ```text
//! K_n = F_n,    K_k = F_k ∩ Pre(K_(k+1)),    Pre(S) = {r : ∃u ∀w, T(r, u, w) ∈ S}
//! ```
//!
//! with `u` the runner's admitted move and `w` the chaser's word, which enters through `D_(k+1)`, the
//! union over every chaser word (§14.4's recursion `K_(n+1) = K_n ∩ Pre(K_n)` on the time-expanded
//! runner state, the chaser as a set-valued disturbance). `K_k` is the set of runner motions at tick
//! `k` on some `n`-tick path from the present that stays outside the chaser's capture reach at
//! every tick; `r₀ ∈ K₀` is the runner inside its robust viability kernel. [counterexample-bounded]
//! The runner here does not see the chaser's later moves (the disturbance is unobserved), so the tube
//! is an inner reading of the closed-loop kernel on the joint state: an empty tube certifies that
//! every runner word of `n` ticks meets some chaser word's capture, not that one chaser strategy
//! captures every runner. **The cornering reading** is the tube's size `|K₁| + … + |K_n|`, counted
//! in runner motions `(x, v)`, read tick by tick from the present joint state.
//!
//! [proved-derived; the record's §14.4 under partial observation] **The capture basin over a fibre
//! of candidates** ([`capture_ticks`]). The chaser reads the runner through candidates (its law, caps
//! and state each), all agreeing with the observed motion. A candidate's cell against the chaser's
//! position is its law's; the fibre splits by cell into observation classes ([`classes`]), each
//! advanced past its own cell. On the belief state `(c, class)`, `C₀ = {captured}` and
//! `C_(j+1) = C_j ∪ Pre(C_j)`, `Pre(S) = {z : ∃u ∀y, T(z, u, y) ∈ S}`, `u` the chaser's admitted motion
//! and `y` the class the runner's cell names: the least `j ≤ m` for which the chaser has an adaptive
//! strategy capturing every candidate within `j` ticks, none past the horizon `m`.
//!
//! [definition; agent-inferred] **The controls** under the same traction bound: [`PurePursuit`] heads
//! at the runner's present position (the admitted motion whose position is nearest it in
//! quadrance, [`Pursuer::step`]). [`ConstantBearing`] holds a collision course: with
//! `r = x_R − x_C` and the relative velocity `ṙ = v_R − v′_C` (the runner read as keeping its
//! velocity), an approaching motion (`⟨r, ṙ⟩ < 0`) where one is admitted, least in `|det(r, ṙ)|`,
//! then in `⟨r + ṙ, r + ṙ⟩` (the closing), then in canonical order. §14.4: `d/dt arg r =
//! det(r, ṙ)/|r|²` is the bearing receiver's lock, which permits radial slip, and approach also
//! needs `⟨r, ṙ⟩ < 0`. [measured] Without the approach condition the law stalls: against a runner at
//! rest, resting nulls `det(r, ṙ)` exactly, and the first acceptance run's constant bearing stood
//! still for hundreds of ticks (the notebook README's action section keeps that run).
//!
//! [definition] The computational object is the helical pair interaction: the runner and the chaser
//! are a pair whose contact quadrance `Q = ⟨x_R − x_C, x_R − x_C⟩` the chaser closes, each meeting the
//! arena's friction field at its ground contact. Of the winding guide's six general objects this
//! owner touches four: the **pair** (the contact's quadrance, capture and the capture reach),
//! **faces and placement** (the friction field keeps absolute placement in the state; the tube is
//! counted in lattice motions), the **tube** (the passage one tick a cell, and the viable tube, the
//! bounded span of the runner's paths) and the **tower thread** (the fibre's observation classes, a
//! candidate set restricted by each cell). The **helix** (the zig-zag's sheet, read through the
//! runner's law) and the **cell holonomy** (the loop closure over three observation channels, the
//! faulty-sensor switch) stay attached.

use std::collections::{BTreeMap, BTreeSet, HashMap};
use std::sync::Arc;

use num_traits::Signed;

use super::chase::{
    Arena, Caps, Chase, ChasePorts, ChaserPort, Motion, Moves, Point, Pursuer, Runner,
    RunnerFamily, RunnerState, add, floor_cap, quadrance, sub,
};
use super::{TerrainError, refuse};
use crate::ratio::Rat;

/// [definition; agent-inferred] **The kernel lattice's declared reach**: the runner's motions a
/// tube indexes densely, `W·H·(2R + 1)²` with `R = ⌊√(speed cap)⌋`, at most `2^22`.
pub const TUBE_STATE_LIMIT: usize = 1 << 22;

/// `det(a, b) = a_x b_y − a_y b_x`, twice the oriented area: the line of sight's rotation.
pub fn det(a: Point, b: Point) -> i64 {
    a[0] * b[1] - a[1] * b[0]
}

/// The lattice offsets `o` with `⟨o, o⟩ ≤ ⌊ρ²⌋`: the capture disk.
fn capture_disk(capture: &Rat) -> Result<Vec<Point>, TerrainError> {
    let cap = floor_cap(capture)?;
    let mut radius = 0i64;
    while (radius + 1) * (radius + 1) <= cap {
        radius += 1;
    }
    Ok((-radius..=radius)
        .flat_map(|dx| (-radius..=radius).map(move |dy| [dx, dy]))
        .filter(|&o| quadrance(o) <= cap)
        .collect())
}

// -------------------------------------------------------------------------------------------
// the capture reach

/// [definition] **The chaser's capture reach** over a horizon (module header): `D_k` for
/// `k = 0, …, n`, each a mask over the arena's positions (row-major).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CaptureReach {
    width: i64,
    masks: Vec<Vec<bool>>,
}

impl CaptureReach {
    /// **The capture reach of a chaser's motion** over `horizon` ticks: every chaser word of `k`
    /// admitted motions ([`Pursuer::admitted`]), each position's capture disk.
    pub fn of(
        arena: &Arena,
        pursuer: &Pursuer,
        caps: &Caps,
        disk: &Moves,
        chaser: Motion,
        horizon: usize,
    ) -> Result<Self, TerrainError> {
        let declaration = arena.declaration();
        let (width, height) = (declaration.width, declaration.height);
        let offsets = capture_disk(&pursuer.capture)?;
        let mut frontier: BTreeSet<Motion> = BTreeSet::from([chaser]);
        let mut masks = Vec::with_capacity(horizon + 1);
        for k in 0..=horizon {
            if k > 0 {
                let mut next = BTreeSet::new();
                for motion in &frontier {
                    next.extend(pursuer.admitted(arena, disk, caps, motion)?);
                }
                frontier = next;
            }
            let mut mask = vec![false; (width * height) as usize];
            for motion in &frontier {
                for &o in &offsets {
                    let x = add(motion.position, o);
                    if arena.inside(x) {
                        mask[(x[1] * width + x[0]) as usize] = true;
                    }
                }
            }
            masks.push(mask);
        }
        Ok(Self { width, masks })
    }

    /// The horizon `n`.
    pub fn horizon(&self) -> usize {
        self.masks.len() - 1
    }

    /// **Whether some chaser word of `k` ticks captures at `x`**: `x ∈ D_k`.
    pub fn covers(&self, k: usize, x: Point) -> bool {
        self.masks
            .get(k)
            .is_some_and(|mask| mask[(x[1] * self.width + x[0]) as usize])
    }

    /// `|D_k|`, the positions some word of `k` ticks captures.
    pub fn size(&self, k: usize) -> usize {
        self.masks
            .get(k)
            .map_or(0, |mask| mask.iter().filter(|&&c| c).count())
    }
}

// -------------------------------------------------------------------------------------------
// the runner's viable tube

/// [definition] **The runner's viable tube** at horizon `n` (module header): per tick
/// `k = 1, …, n` the viable reach `|F_k|` and the kernel `|K_k|`, and whether the present motion
/// lies in `K₀`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ViableTube {
    pub reach: Vec<usize>,
    pub kernel: Vec<usize>,
    pub inside: bool,
}

/// [definition] **The tube's layers** (module header): the forward viable reach `F_k` and the
/// kernel `K_k` for `k = 0, …, n`, each in the order the recursion met its motions.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ViableLayers {
    pub reach: Vec<Vec<Motion>>,
    pub kernel: Vec<Vec<Motion>>,
}

impl ViableTube {
    /// **The cornering reading** `|K₁| + … + |K_n|`.
    pub fn size(&self) -> usize {
        self.kernel.iter().sum()
    }
}

/// The runner's lattice of motions, indexed densely: position, then velocity in the speed disk's
/// bounding square.
struct RunnerLattice<'a> {
    arena: &'a Arena,
    caps: &'a Caps,
    width: i64,
    radius: i64,
    side: usize,
    /// The next velocities the speed cap admits.
    velocities: Vec<Point>,
}

impl<'a> RunnerLattice<'a> {
    fn new(arena: &'a Arena, caps: &'a Caps) -> Result<Self, TerrainError> {
        let mut radius = 0i64;
        while (radius + 1) * (radius + 1) <= caps.speed {
            radius += 1;
        }
        let side = (2 * radius + 1) as usize;
        let declaration = arena.declaration();
        if declaration
            .positions()
            .checked_mul(side * side)
            .is_none_or(|states| states > TUBE_STATE_LIMIT)
        {
            return Err(refuse(
                "a runner's viable tube",
                "its lattice holds at most 2^22 runner motions",
            ));
        }
        let velocities = (-radius..=radius)
            .flat_map(|vx| (-radius..=radius).map(move |vy| [vx, vy]))
            .filter(|&v| quadrance(v) <= caps.speed)
            .collect();
        Ok(Self {
            arena,
            caps,
            width: declaration.width,
            radius,
            side,
            velocities,
        })
    }

    fn states(&self) -> usize {
        self.arena.declaration().positions() * self.side * self.side
    }

    fn index(&self, motion: &Motion) -> usize {
        let p = (motion.position[1] * self.width + motion.position[0]) as usize;
        let v = ((motion.velocity[0] + self.radius) as usize) * self.side
            + (motion.velocity[1] + self.radius) as usize;
        p * self.side * self.side + v
    }

    /// **The runner's admitted successors** (module header): the kept motion while forced,
    /// otherwise every admitted next velocity's motion, the wall law's when none.
    fn post(&self, motion: &Motion, forced: bool, out: &mut Vec<Motion>) {
        out.clear();
        if forced {
            let stepped = add(motion.position, motion.velocity);
            out.push(if self.arena.inside(stepped) {
                Motion {
                    position: stepped,
                    velocity: motion.velocity,
                }
            } else {
                self.arena.wall(motion)
            });
            return;
        }
        let class = self
            .arena
            .class(motion.position)
            .expect("a runner motion in the arena");
        let cap = self.caps.classes[class];
        for &velocity in &self.velocities {
            let position = add(motion.position, velocity);
            if quadrance(sub(velocity, motion.velocity)) <= cap && self.arena.inside(position) {
                out.push(Motion { position, velocity });
            }
        }
        if out.is_empty() {
            out.push(self.arena.wall(motion));
        }
    }
}

/// **The runner's viable tube** (module header) from its present motion, forced to keep its
/// velocity for its first `forced` ticks, against a chaser's capture reach of horizon `n ≥ 1`: the
/// sizes of [`viable_layers`].
pub fn viable_tube(
    arena: &Arena,
    caps: &Caps,
    runner: Motion,
    forced: u64,
    reach: &CaptureReach,
) -> Result<ViableTube, TerrainError> {
    let layers = viable_layers(arena, caps, runner, forced, reach)?;
    Ok(ViableTube {
        reach: layers.reach[1..].iter().map(Vec::len).collect(),
        kernel: layers.kernel[1..].iter().map(Vec::len).collect(),
        inside: !layers.kernel[0].is_empty(),
    })
}

/// **The tube's layers** (module header): the forward viable reach, then the Pre recursion backward
/// over it. Refused when the present motion lies outside the arena or its speed bound, or the
/// lattice passes [`TUBE_STATE_LIMIT`].
pub fn viable_layers(
    arena: &Arena,
    caps: &Caps,
    runner: Motion,
    forced: u64,
    reach: &CaptureReach,
) -> Result<ViableLayers, TerrainError> {
    let horizon = reach.horizon();
    if horizon == 0 {
        return Err(refuse(
            "a runner's viable tube",
            "its horizon is at least one tick",
        ));
    }
    if !arena.inside(runner.position) || quadrance(runner.velocity) > caps.speed {
        return Err(refuse(
            "a runner's viable tube",
            "the runner stands in the arena within its speed bound",
        ));
    }
    let lattice = RunnerLattice::new(arena, caps)?;
    let states = lattice.states();
    // The forward viable reach, layer by layer.
    let mut layers: Vec<Vec<Motion>> = Vec::with_capacity(horizon + 1);
    layers.push(if reach.covers(0, runner.position) {
        Vec::new()
    } else {
        vec![runner]
    });
    let mut stamp = vec![usize::MAX; states];
    let mut next = Vec::new();
    for k in 0..horizon {
        let forced_here = (k as u64) < forced;
        let mut layer = Vec::new();
        for motion in &layers[k] {
            lattice.post(motion, forced_here, &mut next);
            for successor in &next {
                let index = lattice.index(successor);
                if stamp[index] != k + 1 && !reach.covers(k + 1, successor.position) {
                    stamp[index] = k + 1;
                    layer.push(*successor);
                }
            }
        }
        layers.push(layer);
    }
    // The Pre recursion backward: K_n = F_n, K_k = F_k ∩ Pre(K_(k+1)).
    let mut kernel: Vec<Vec<Motion>> = vec![Vec::new(); horizon + 1];
    let mut held = vec![false; states];
    for motion in &layers[horizon] {
        held[lattice.index(motion)] = true;
    }
    kernel[horizon] = layers[horizon].clone();
    for k in (0..horizon).rev() {
        let forced_here = (k as u64) < forced;
        let mut members = Vec::new();
        for motion in &layers[k] {
            lattice.post(motion, forced_here, &mut next);
            if next.iter().any(|s| held[lattice.index(s)]) {
                members.push(*motion);
            }
        }
        for motion in &layers[k + 1] {
            held[lattice.index(motion)] = false;
        }
        for motion in &members {
            held[lattice.index(motion)] = true;
        }
        kernel[k] = members;
    }
    Ok(ViableLayers {
        reach: layers,
        kernel,
    })
}

// -------------------------------------------------------------------------------------------
// the capture basin over a fibre of candidates

/// [definition] **A candidate's law on the arena**: the runner (its constitution, slip hold and
/// navigator) and its caps on the arena's lattice.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct CandidateLaw {
    pub runner: Runner,
    pub caps: Caps,
}

/// [definition] **A candidate the chaser reads**: its index in the declared family, its law and its
/// state, which agrees with the observed motion (only the slip counter is its own).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Candidate {
    pub index: usize,
    pub law: Arc<CandidateLaw>,
    pub state: RunnerState,
}

impl Candidate {
    /// **Every candidate of a family** at the runner's opening.
    pub fn opening(
        family: &RunnerFamily,
        arena: &Arena,
        opening: Point,
    ) -> Result<Vec<Self>, TerrainError> {
        (0..family.len())
            .map(|index| {
                let runner = family.candidate(index)?;
                Ok(Self {
                    index,
                    law: Arc::new(CandidateLaw {
                        caps: runner.law.caps(arena.declaration())?,
                        runner,
                    }),
                    state: RunnerState::opening(arena, opening)?,
                })
            })
            .collect()
    }

    /// **The candidate's cell** at a tick against the chaser's position.
    pub fn cell(
        &self,
        arena: &Arena,
        moves: &Moves,
        chaser: Point,
        tick: u64,
    ) -> Result<usize, TerrainError> {
        self.law
            .runner
            .cell(arena, moves, &self.law.caps, &self.state, chaser, tick)
    }

    /// **The candidate past a received cell**: its state follows the cell ([`Runner::receive`]).
    pub fn receive(&self, arena: &Arena, moves: &Moves, cell: usize) -> Result<Self, TerrainError> {
        Ok(Self {
            index: self.index,
            law: Arc::clone(&self.law),
            state: self.law.runner.receive(arena, moves, &self.state, cell)?,
        })
    }
}

/// **The observation classes of a fibre at a tick** (module header): each candidate's cell against
/// the chaser's position, the candidates grouped by cell in ascending cell order, each advanced past
/// its own cell.
pub fn classes(
    arena: &Arena,
    moves: &Moves,
    candidates: &[Candidate],
    chaser: Point,
    tick: u64,
) -> Result<Vec<(usize, Vec<Candidate>)>, TerrainError> {
    let mut parts: BTreeMap<usize, Vec<Candidate>> = BTreeMap::new();
    for candidate in candidates {
        let cell = candidate.cell(arena, moves, chaser, tick)?;
        parts
            .entry(cell)
            .or_default()
            .push(candidate.receive(arena, moves, cell)?);
    }
    Ok(parts.into_iter().collect())
}

/// [definition] **The chaser's reading context** for the capture basin: the arena, the runner's
/// alphabet, the chaser's constitution, its caps and its move disk.
#[derive(Clone, Copy, Debug)]
pub struct Basin<'a> {
    pub arena: &'a Arena,
    pub moves: &'a Moves,
    pub pursuer: &'a Pursuer,
    pub caps: &'a Caps,
    pub disk: &'a Moves,
}

/// A belief node: the chaser's motion, the tick, and the class's candidates by index and state.
type Node = (Motion, u64, Vec<(usize, RunnerState)>);

/// [definition] **The capture basin's memo** within one decision: each belief node read, with the
/// depth it was read at and its value there. A value `Some(j)` is the least capture within any
/// depth at least `j`, none within less; `None` read at depth `d` is none within every depth at
/// most `d`. It is a quotient of the recursion's own nodes, dropped after the decision.
#[derive(Clone, Debug, Default)]
pub struct BasinMemo(HashMap<Node, (usize, Option<usize>)>);

impl BasinMemo {
    /// The nodes read.
    pub fn len(&self) -> usize {
        self.0.len()
    }

    pub fn is_empty(&self) -> bool {
        self.0.is_empty()
    }
}

impl Basin<'_> {
    /// **The capture basin's value of a class** (module header): the least `j ≤ depth` for which
    /// the chaser at `chaser` captures every candidate of the class within `j` ticks under some
    /// adaptive strategy, the class's candidates sharing their observed motion; none past `depth`.
    pub fn capture_ticks(
        &self,
        memo: &mut BasinMemo,
        chaser: Motion,
        tick: u64,
        class: &[Candidate],
        depth: usize,
    ) -> Result<Option<usize>, TerrainError> {
        let Some(first) = class.first() else {
            return Ok(Some(0));
        };
        if self
            .pursuer
            .captures(first.state.motion.position, chaser.position)
        {
            return Ok(Some(0));
        }
        if depth == 0 {
            return Ok(None);
        }
        let node: Node = (
            chaser,
            tick,
            class.iter().map(|c| (c.index, c.state)).collect(),
        );
        match memo.0.get(&node) {
            Some(&(_, Some(j))) => return Ok((j <= depth).then_some(j)),
            Some(&(read, None)) if depth <= read => return Ok(None),
            _ => {}
        }
        let parts = classes(self.arena, self.moves, class, chaser.position, tick)?;
        let mut best: Option<usize> = None;
        for next in self
            .pursuer
            .motions(self.arena, self.disk, self.caps, &chaser)?
        {
            let Some(worst) = self.worst(memo, next, tick + 1, &parts, depth - 1, best)? else {
                continue;
            };
            best = Some(worst + 1);
            if worst == 0 {
                break;
            }
        }
        memo.0.insert(node, (depth, best));
        Ok(best)
    }

    /// **The capture basin's value of the classes after a move**: the greatest of the classes'
    /// values with the chaser at `chaser` at `tick`, none when a class is not captured within
    /// `depth`, or not within `better − 1` when a value `better` is already in hand.
    pub fn worst(
        &self,
        memo: &mut BasinMemo,
        chaser: Motion,
        tick: u64,
        parts: &[(usize, Vec<Candidate>)],
        depth: usize,
        better: Option<usize>,
    ) -> Result<Option<usize>, TerrainError> {
        // A value is useful here only below `better − 1` ticks.
        let depth = match better {
            Some(0) | Some(1) => return Ok(None),
            Some(b) => depth.min(b - 2),
            None => depth,
        };
        let mut worst = 0;
        for (_, class) in parts {
            match self.capture_ticks(memo, chaser, tick, class, depth)? {
                Some(j) => worst = worst.max(j),
                None => return Ok(None),
            }
        }
        Ok(Some(worst))
    }
}

/// **The capture basin's value of a fibre's move** (module header): with the fibre split into its
/// classes at tick `tick` against the chaser's present position, the chaser's move to `next`
/// captures every candidate within `1 + j` ticks, `j ≤ depth` the least value the basin certifies;
/// none past the horizon.
pub fn capture_ticks(
    basin: &Basin<'_>,
    memo: &mut BasinMemo,
    parts: &[(usize, Vec<Candidate>)],
    next: Motion,
    tick: u64,
    depth: usize,
) -> Result<Option<usize>, TerrainError> {
    Ok(basin
        .worst(memo, next, tick + 1, parts, depth, None)?
        .map(|j| j + 1))
}

// -------------------------------------------------------------------------------------------
// the chasers

/// [definition] **What a chaser reads at a tick**: the ports (its own motions written so far, the
/// present one included), its constitution, the runner's present observed motion, its own present
/// motion and the tick.
#[derive(Clone, Copy, Debug)]
pub struct ChaseView<'a> {
    pub ports: &'a Arc<ChasePorts>,
    pub pursuer: &'a Pursuer,
    pub runner: Motion,
    pub chaser: Motion,
    pub tick: usize,
}

impl ChaseView<'_> {
    /// **The chaser's traction-admitted motions** at the tick.
    pub fn admitted(&self) -> Result<Vec<Motion>, TerrainError> {
        let caps = self.pursuer.law.caps(self.ports.arena.declaration())?;
        let disk = Moves::within(caps.top())?;
        self.pursuer
            .motions(&self.ports.arena, &disk, &caps, &self.chaser)
    }
}

/// [definition] **A chaser**: it opens on a passage's ports, releases one motion a tick from what
/// it reads, and receives the runner's cell after both move.
pub trait Chaser {
    type Error: From<TerrainError>;
    /// The chaser's declaration, for a receipt.
    fn label(&self) -> String;
    /// **Open on a passage's ports** (a chaser that reads the runner joins them here).
    fn open(&mut self, _ports: &Arc<ChasePorts>, _pursuer: &Pursuer) -> Result<(), Self::Error> {
        Ok(())
    }
    /// **Release the next motion**, one of the view's admitted motions.
    fn decide(&mut self, view: &ChaseView<'_>) -> Result<Motion, Self::Error>;
    /// **Receive the runner's cell** of the tick just moved.
    fn receive(&mut self, _cell: usize) -> Result<(), Self::Error> {
        Ok(())
    }
}

/// [definition] **Pure pursuit** (module header): head at the runner's present position.
#[derive(Clone, Copy, Debug, Default)]
pub struct PurePursuit;

impl Chaser for PurePursuit {
    type Error = TerrainError;

    fn label(&self) -> String {
        "pure pursuit".to_string()
    }

    fn decide(&mut self, view: &ChaseView<'_>) -> Result<Motion, TerrainError> {
        let admitted = view.admitted()?;
        let target = view.runner.position;
        admitted
            .into_iter()
            .min_by_key(|next| quadrance(sub(next.position, target)))
            .ok_or_else(|| refuse("a chaser's motion", "its admitted motions are not empty"))
    }
}

/// [definition] **Constant bearing** (module header): null the line-of-sight rotation, then close.
#[derive(Clone, Copy, Debug, Default)]
pub struct ConstantBearing;

impl ConstantBearing {
    /// Its order on an admitted motion: `(⟨r, ṙ⟩ ≥ 0, |det(r, ṙ)|, ⟨r + ṙ, r + ṙ⟩)`, least first:
    /// an approaching motion before any other.
    pub fn key(runner: &Motion, chaser: &Motion, next: &Motion) -> (bool, i64, i64) {
        let line = sub(runner.position, chaser.position);
        let rate = sub(runner.velocity, next.velocity);
        let closing = line[0] * rate[0] + line[1] * rate[1];
        (
            closing >= 0,
            det(line, rate).abs(),
            quadrance(add(line, rate)),
        )
    }
}

impl Chaser for ConstantBearing {
    type Error = TerrainError;

    fn label(&self) -> String {
        "constant bearing".to_string()
    }

    fn decide(&mut self, view: &ChaseView<'_>) -> Result<Motion, TerrainError> {
        view.admitted()?
            .into_iter()
            .min_by_key(|next| Self::key(&view.runner, &view.chaser, next))
            .ok_or_else(|| refuse("a chaser's motion", "its admitted motions are not empty"))
    }
}

// -------------------------------------------------------------------------------------------
// the passage

/// [definition] **The action passage's declaration**: the chaser's constitution and capture, the
/// passage's tick cap, and the cornering receipt's horizon `n ≥ 1`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActionDeclaration {
    pub pursuer: Pursuer,
    pub ticks: usize,
    pub horizon: usize,
}

/// [definition] **An action passage's receipt**: the chaser's label, the truth (the candidate's
/// index and law), the runner's cells and motions, the ports (the chaser's port holds its motion at
/// every tick and the one after), the capture tick, the runner's slips (onsets and slipping ticks)
/// and wall meetings, and the cornering receipt: the runner's viable tube, under the truth's
/// constitution, at every tick before capture.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActionPassage {
    pub chaser: String,
    pub index: usize,
    pub runner: Runner,
    pub cells: Vec<usize>,
    pub path: Vec<Motion>,
    pub ports: Arc<ChasePorts>,
    pub captured: Option<usize>,
    pub slips: usize,
    pub slip_ticks: usize,
    pub walls: usize,
    pub tubes: Vec<ViableTube>,
}

impl ActionPassage {
    /// **The ticks to capture**, the passage's cap when not captured (a lower bound then).
    pub fn ticks(&self) -> usize {
        self.captured.unwrap_or(self.cells.len())
    }

    /// **The cornering receipt's sum** over the passage's first `ticks` ticks.
    pub fn kernel_sum(&self, ticks: usize) -> usize {
        self.tubes.iter().take(ticks).map(ViableTube::size).sum()
    }
}

/// **The action passage** (module header) of candidate `index` of the family on an arena from its
/// openings, against a chaser, for at most the declared ticks. Refused unless the openings lie in
/// the arena outside capture, the chaser is slower and of larger traction than the runner and can
/// always stop, the horizon is at least one tick, and every motion the chaser releases is one of its
/// admitted motions.
pub fn act<C: Chaser>(
    arena: Arena,
    family: &RunnerFamily,
    index: usize,
    openings: [Point; 2],
    declaration: &ActionDeclaration,
    chaser: &mut C,
) -> Result<ActionPassage, C::Error> {
    let pursuer = &declaration.pursuer;
    let runner = family.candidate(index)?;
    let arena_declaration = arena.declaration().clone();
    let [runner_start, chaser_start] = openings;
    if pursuer.capture.is_negative() || declaration.horizon == 0 {
        return Err(refuse(
            "an action passage",
            "its capture radius squared is nonnegative and its horizon at least one tick",
        )
        .into());
    }
    if !arena.inside(runner_start)
        || !arena.inside(chaser_start)
        || pursuer.captures(runner_start, chaser_start)
    {
        return Err(refuse(
            "a chase's openings",
            "the runner and the chaser open in the arena, outside capture",
        )
        .into());
    }
    if pursuer.law.speed >= runner.law.speed
        || pursuer.law.traction <= runner.law.traction
        || !pursuer.stops(&arena_declaration)?
    {
        return Err(refuse(
            "a chase's chaser",
            "it is slower than the runner, of larger traction, and can always stop",
        )
        .into());
    }
    let moves = family.moves(&arena_declaration)?;
    let caps = runner.law.caps(&arena_declaration)?;
    let chaser_caps = pursuer.law.caps(&arena_declaration)?;
    let disk = Moves::within(chaser_caps.top())?;
    let mut state = RunnerState::opening(&arena, runner_start)?;
    let ports = Arc::new(ChasePorts {
        arena,
        moves,
        chaser: ChaserPort::default(),
        opening: state.motion,
    });
    chaser.open(&ports, pursuer)?;
    let (arena, moves) = (&ports.arena, &ports.moves);
    let mut present = Motion::rest(chaser_start);
    let (mut cells, mut path, mut tubes) = (Vec::new(), Vec::new(), Vec::new());
    let (mut slips, mut slip_ticks, mut walls, mut captured) = (0, 0, 0, None);
    for tick in 0..declaration.ticks {
        if pursuer.captures(state.motion.position, present.position) {
            captured = Some(tick);
            break;
        }
        ports.chaser.push(present);
        let reach = CaptureReach::of(
            arena,
            pursuer,
            &chaser_caps,
            &disk,
            present,
            declaration.horizon,
        )?;
        tubes.push(viable_tube(arena, &caps, state.motion, state.held, &reach)?);
        let view = ChaseView {
            ports: &ports,
            pursuer,
            runner: state.motion,
            chaser: present,
            tick,
        };
        let next = chaser.decide(&view)?;
        if !pursuer
            .motions(arena, &disk, &chaser_caps, &present)?
            .contains(&next)
        {
            return Err(refuse(
                "a chaser's motion",
                "it satisfies the chaser's traction and speed bounds and stays in the arena",
            )
            .into());
        }
        let cell = runner.cell(arena, moves, &caps, &state, present.position, tick as u64)?;
        if cell == moves.slip() {
            slip_ticks += 1;
            slips += usize::from(state.held == 0);
        }
        walls += usize::from(cell == moves.wall());
        state = runner.receive(arena, moves, &state, cell)?;
        chaser.receive(cell)?;
        cells.push(cell);
        path.push(state.motion);
        present = next;
    }
    if captured.is_none() && pursuer.captures(state.motion.position, present.position) {
        captured = Some(cells.len());
    }
    ports.chaser.push(present);
    Ok(ActionPassage {
        chaser: chaser.label(),
        index,
        runner,
        cells,
        path,
        ports,
        captured,
        slips,
        slip_ticks,
        walls,
        tubes,
    })
}

/// **A seed's action passage** (module header): the reception's draw ([`Chase::drawn`]), the same
/// candidate, arena and openings, against a chaser.
pub fn act_drawn<C: Chaser>(
    arena_declaration: &super::chase::ArenaDeclaration,
    family: &RunnerFamily,
    declaration: &ActionDeclaration,
    seed: u64,
    chaser: &mut C,
) -> Result<ActionPassage, C::Error> {
    let (index, arena, openings) = Chase::drawn(arena_declaration, family, seed)?;
    act(arena, family, index, openings, declaration, chaser)
}
