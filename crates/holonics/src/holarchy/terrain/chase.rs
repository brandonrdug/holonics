//! **The chase terrain: a fast runner on a bounded exact arena, its motion read as cells** (THE_REBUILD
//! F6; the record `2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_…`, §13 and §14.4; campaign 4,
//! #27, #148). The reception phase: the machine reads the runner's passage and selects its
//! constitution, the chaser here a declared scripted pursuer. The action phase, where the machine
//! chases, is `holarchy::terrain::pursuit` (and `receiver::population::chaser`); it reads this
//! terrain's arena, runner and ports, and the same draw ([`Chase::drawn`]).
//!
//! [definition; agent-inferred] **The arena** ([`ArenaDeclaration`], [`Arena`]). A bounded lattice
//! `[0, W) × [0, H)` of integer positions, spacing `ℓ` and tick `h`, under gravity `g`, all declared
//! rationals. Each cell has a friction class `μ` from a declared finite set of positive rationals,
//! drawn per square patch of declared side (ground comes in patches: a patch of ice is where a turn
//! is forced to fail). Positions and velocities are integers on the lattice (steps, and steps a
//! tick), and a velocity moves the position once a tick, `x′ = x + v′`. The walls make forced
//! turning possible: in an open arena a faster runner moving straight away is never caught (§14.4).
//!
//! [definition; the record's §13] **The constitution at the ground contact** ([`RunnerLaw`]):
//! a speed bound `v` and a traction coefficient `γ`. A move `(v, v′)`, velocities in lattice steps
//! a tick, carried undivided ([`Move`], `geometry::motion`), is admitted on a cell of class `μ` only
//! if its change `Δv = v′ − v` lies in the traction disk
//!
//! ```text
//! ⟨Δv, Δv⟩ ≤ (γ μ g h²/ℓ)²        (the physical |Δv|·ℓ/h ≤ γ μ g h, read in the lattice chart)
//! ```
//!
//! an exact quadrance inequality in ℚ (Lean `Geometry/Motion.traction_disk`: where `v ≠ 0`, the disk
//! `|k − 1|²|v|² ≤ r²` about `1` of the move ratio `k = v′/v`; the pair is carried, not `k`, because
//! the opening velocity is zero, a stop has `k = 0` and a held slip `k = 1`), and a velocity only if
//! `⟨v, v⟩ ≤ v²`. There is no square root: the integer quadrance `q` meets a rational bound `b ≥ 0`
//! exactly when `q ≤ ⌊b⌋` ([`Caps`], [`Move::within_cap`], an identity, not a rounding). For a pure
//! turn the bound gives the radius at least `v²/(γμg)` (the record's §6). [agent-inferred] A class
//! whose bound lies below one lattice step admits only rest there, so a runner at rest on it could
//! never move: the declared classes must resolve on the lattice (every receipt here declares bounds
//! of at least one step).
//!
//! [definition; agent-inferred] **The runner** ([`Runner`]): its constitution, its declared hybrid
//! slip law (a hold of `s ≥ 1` ticks) and its evasion navigator ([`Evasion`]). Each tick:
//! - while a slip holds, it keeps its velocity (the cell [`Letter::Slip`]; its realized move is the
//!   held one, [`Move::held`]);
//! - otherwise it **demands** the change its navigator scores best among the changes its
//!   constitution admits on the ground it **last pushed from** (the class of its previous position;
//!   at the opening, its own), within its speed bound and keeping it inside the arena, ties broken
//!   by the canonical order of the moves ([`Moves`]);
//! - a demand within the traction of the cell it stands on is realized (the cell is the move's
//!   index); a demand beyond it slips: the runner keeps its velocity for `s` ticks. So a slip is the
//!   surprise of ground of lower friction than the ground behind it: a turn demanded as on track
//!   fails on the ice it has just run onto;
//! - the **wall law**: a runner that cannot stay inside (no admitted demand, or a kept velocity
//!   that leaves the arena) meets the wall ([`Letter::Wall`]): its position is clamped to the
//!   arena, the components of its velocity that crossed a wall are zeroed, and a slip ends.
//!
//! [definition; agent-inferred] **The evasion navigators** ([`Evasion`]), each a score over the next
//! position `x′ = x + v + Δv`, least best:
//! - **flee**: maximize the pair contact's next quadrance `Q = ⟨x′ − x_C, x′ − x_C⟩` to the chaser
//!   (§14.4's contact reading). Agent-inferred against the brief's reflected-position target
//!   `S_x(x_C) = 2x − x_C` (the half-turn of the chaser about the runner): that target lies at the pair's
//!   own distance, so near contact it asks for less speed than the runner has; maximizing `Q` runs
//!   at the runner's full admitted reach and meets the walls, which the cornering needs;
//! - **circle**: steer to the oriented quarter-turn of its offset from the arena's centre `c`,
//!   `x + σJ(x − c)`, `J(a, b) = (−b, a)` (the quarter-turn whose square is the half-turn, §14.9), `σ = ±1`
//!   its orientation; read in doubled coordinates, so the centre `(W − 1, H − 1)/2` stays integral;
//! - **zig-zag at period `P`**: steer to `x + d + σ_t J d`, `d = x − x_C` the flee direction and
//!   `σ_t` the half-turn sheet of a ring of period `2P` (`+1` on the ports `t mod 2P < P`, else
//!   `−1`): a grating's sheet, as in the moiré.
//!
//! [definition; agent-inferred] **The scripted pursuer** ([`Pursuer`]): pure pursuit, the admitted
//! change minimizing the quadrance of its next position to the runner's present position, under its
//! own constitution on its own cell (it never demands beyond its traction, so it never slips; with
//! no admitted change it meets the wall law). It is slower and of larger traction than the runner
//! (the record: `v_C < v_R`), refused otherwise. It moves the runner's context; it is not the
//! machine, whose action phase is `holarchy::terrain::pursuit`. **Capture** (the record's §13) is the pair's
//! quadrance at most the declared `ρ²`, `Q = ⟨x_R − x_C, x_R − x_C⟩ ≤ ρ²`; the chase, and so the
//! passage, ends at the first tick it holds (after it the two would stand locked and every candidate
//! would read alike).
//!
//! [definition; agent-inferred] **The cells** ([`Moves`]): the runner's motion read as a finite
//! alphabet. The lattice moves `Δv` with `⟨Δv, Δv⟩` at most the declared family's greatest
//! traction bound (its greatest coefficient on the highest class), ordered canonically by quadrance, then `Δx`, then `Δy`; then the slip letter and
//! the wall letter. The observed motion follows from the cells and the opening motion alone
//! ([`Arena::observe`]): a move letter changes the velocity by its move, a slip keeps it, a wall
//! applies the wall law; the ground last pushed from is the class of the previous position. Only a
//! candidate's slip counter is its own.
//!
//! [definition] **The truth** ([`ChaseTruth`]): the drawn candidate (constitution, slip law and
//! navigator) and its index in the declared family, the pursuer, the drawn friction field, the
//! opening positions (velocities zero), the seed, the realized motions, the slips (onsets and held
//! ticks), the wall meetings and the capture tick, and the key description `⌈log₂ |key space|⌉`, the key space
//! `N · m^P · WH · (WH − 1)` (the candidate, each patch's class, the runner's cell and the chaser's
//! other cell, each uniform: [`Chase::draw`]).
//!
//! [proved-derived; the record's §14.10] **Identifiability.** Two constitutions that emit alike
//! under every observed action are one fibre for the passage: two speed bounds are
//! indistinguishable while every demanded motion stays below both, and two slip holds while no slip
//! is demanded. So reception selects a **fibre**, the candidates whose law emits every received cell
//! ([`Chase::fibre`]); the exact candidate is required only where the passage separates it.
//! [`Chase::futures`] reads the fibre's classes of future equivalence over every admitted chaser
//! action word of a declared horizon (the pursuer's admitted moves), and a separating word where one
//! exists: the probe the action phase may emit (item 13's action-sufficient retention).
//!
//! [definition] The computational object is the helical pair interaction: the runner's navigator
//! meets the arena's friction field at its contact (the traction law is that contact's constitution:
//! it admits or slips), and the runner and the pursuer are a pair whose quadrance
//! `Q = ⟨x_R − x_C, x_R − x_C⟩` the flee navigator raises and the pursuer lowers. Of the winding
//! guide's six general objects this owner touches four: the **pair** (the ground contact and the
//! runner–pursuer contact's quadrance), the **helix** (the zig-zag's side is a ring's half-turn
//! sheet with its carry; the draw is a Weyl rotation), **faces and placement** (the cell alphabet as
//! the receiver's face; the friction field keeps absolute placement in the state, §14.4) and the
//! **tube** (the passage, one cell a tick; a slip's hold is a span of it). The **cell holonomy**
//! (the loop-closure reading over three observation channels belongs to the faulty-sensor switch of
//! the action phase) and the **tower thread** (the patch-to-cell restriction of the friction field
//! is declared, no gluing is read) stay attached.

use std::collections::BTreeMap;
use std::sync::{Arc, PoisonError, RwLock};

use num_bigint::{BigInt, BigUint};
use num_traits::{Signed, ToPrimitive};

use super::{Draw, TerrainError, refuse};
use crate::compression::cost::ceil_log2;
use crate::geometry::motion::{Move, add, quarter_turn, scale, sub};
// A lattice point or displacement in lattice steps (a velocity: steps a tick) and its quadrance:
// the motion owner's Gaussian integers, shared with the tests.
pub(super) use crate::geometry::motion::{Point, quadrance};
use crate::ratio::Rat;

/// [definition; agent-inferred] **The lattice's declared reach**: an arena side of at most `2^15`
/// positions and a move alphabet's cap of at most `2^12`, so every position, velocity and score the
/// law forms stays below `2^40` in magnitude, far inside a machine word and inside the motion
/// owner's reach (`geometry::motion::LATTICE_REACH`, `2^30` a component), and an alphabet holds at
/// most `(2·2^6 + 1)² = 16641 = 3²·43²` moves.
pub const ARENA_SIDE_LIMIT: i64 = 1 << 15;
pub const MOVE_CAP_LIMIT: i64 = 1 << 12;

/// `⌊b⌋` of a nonnegative rational bound: an integer quadrance `q` meets `q ≤ b` exactly when
/// `q ≤ ⌊b⌋` (an identity on the integers, not a rounding).
pub(super) fn floor_cap(bound: &Rat) -> Result<i64, TerrainError> {
    if bound.is_negative() {
        return Err(refuse("a quadrance bound", "it is nonnegative"));
    }
    bound
        .floor()
        .to_integer()
        .to_i64()
        .ok_or_else(|| refuse("a quadrance bound", "its floor fits a machine word"))
}

// -------------------------------------------------------------------------------------------
// the arena

/// [definition] **The declared arena** (module header): `W × H` lattice positions, square friction
/// patches of side `patch` (dividing both), the friction classes `μ` (positive, strictly
/// ascending), gravity `g`, tick `h` and spacing `ℓ` (positive rationals).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ArenaDeclaration {
    pub width: i64,
    pub height: i64,
    pub patch: i64,
    pub classes: Vec<Rat>,
    pub gravity: Rat,
    pub tick: Rat,
    pub spacing: Rat,
}

impl ArenaDeclaration {
    /// Refused unless `2 ≤ W, H ≤ 2^15`, the patch side is positive and divides both, the classes
    /// are positive and strictly ascending, and `g, h, ℓ` are positive.
    pub fn check(&self) -> Result<(), TerrainError> {
        let sides = 2..=ARENA_SIDE_LIMIT;
        if !sides.contains(&self.width) || !sides.contains(&self.height) {
            return Err(refuse(
                "an arena",
                "it spans at least two and at most 2^15 positions a side",
            ));
        }
        if self.patch < 1 || self.width % self.patch != 0 || self.height % self.patch != 0 {
            return Err(refuse(
                "an arena's friction patches",
                "their side is positive and divides the arena's width and height",
            ));
        }
        if self.classes.is_empty()
            || self.classes.iter().any(|mu| !mu.is_positive())
            || self.classes.windows(2).any(|pair| pair[0] >= pair[1])
        {
            return Err(refuse(
                "an arena's friction classes",
                "they are positive rationals, strictly ascending",
            ));
        }
        if !self.gravity.is_positive() || !self.tick.is_positive() || !self.spacing.is_positive() {
            return Err(refuse(
                "an arena's chart",
                "its gravity, tick and spacing are positive",
            ));
        }
        Ok(())
    }

    /// **The traction scale** `k = g h²/ℓ`: a friction coefficient's admitted change in lattice
    /// steps a tick, per unit coefficient.
    pub fn scale(&self) -> Rat {
        &self.gravity * &self.tick * &self.tick / &self.spacing
    }

    /// The patches a row holds and their count.
    fn patch_grid(&self) -> (i64, i64) {
        (self.width / self.patch, self.height / self.patch)
    }

    /// The number of friction patches.
    pub fn patches(&self) -> usize {
        let (columns, rows) = self.patch_grid();
        (columns * rows) as usize
    }

    /// The number of lattice positions `W·H`.
    pub fn positions(&self) -> usize {
        (self.width * self.height) as usize
    }

    /// **The traction bound** `(γ μ_c g h²/ℓ)²` of a traction coefficient `γ` on class `c`, exact.
    pub fn traction_bound(&self, traction: &Rat, class: usize) -> Option<Rat> {
        let radius = traction * self.classes.get(class)? * self.scale();
        Some(&radius * &radius)
    }

    /// The position of a lattice index `i < W·H`, row-major.
    pub fn position(&self, index: usize) -> Point {
        let index = index as i64;
        [index % self.width, index / self.width]
    }
}

/// [definition] **The arena**: its declaration and each patch's drawn friction class.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arena {
    declaration: ArenaDeclaration,
    patches: Vec<usize>,
}

/// [definition] **A mover's observed motion**: its position and its velocity.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Motion {
    pub position: Point,
    pub velocity: Point,
}

impl Motion {
    /// At rest at a position.
    pub fn rest(position: Point) -> Self {
        Self {
            position,
            velocity: [0, 0],
        }
    }
}

impl Arena {
    /// The arena of a declaration and each patch's class (row-major); refused unless the
    /// declaration checks, there is one class a patch and each names a declared class.
    pub fn new(declaration: ArenaDeclaration, patches: Vec<usize>) -> Result<Self, TerrainError> {
        declaration.check()?;
        if patches.len() != declaration.patches()
            || patches
                .iter()
                .any(|&class| class >= declaration.classes.len())
        {
            return Err(refuse(
                "an arena's friction field",
                "it names one declared class for every patch",
            ));
        }
        Ok(Self {
            declaration,
            patches,
        })
    }

    /// **The arena drawn** (module header): each patch's class uniform on the declared classes.
    pub fn draw(declaration: ArenaDeclaration, draw: &mut Draw) -> Result<Self, TerrainError> {
        declaration.check()?;
        let patches = (0..declaration.patches())
            .map(|_| draw.below(declaration.classes.len()))
            .collect();
        Self::new(declaration, patches)
    }

    pub fn declaration(&self) -> &ArenaDeclaration {
        &self.declaration
    }

    /// Each patch's friction class, row-major.
    pub fn patches(&self) -> &[usize] {
        &self.patches
    }

    /// Whether a position lies in the arena.
    pub fn inside(&self, p: Point) -> bool {
        (0..self.declaration.width).contains(&p[0]) && (0..self.declaration.height).contains(&p[1])
    }

    /// **The friction class of a position** in the arena, none outside it.
    pub fn class(&self, p: Point) -> Option<usize> {
        if !self.inside(p) {
            return None;
        }
        let (columns, _) = self.declaration.patch_grid();
        let side = self.declaration.patch;
        Some(self.patches[((p[1] / side) * columns + p[0] / side) as usize])
    }

    /// **The wall law** (module header): the kept velocity's step clamped to the arena, the
    /// components that crossed a wall zeroed.
    pub fn wall(&self, motion: &Motion) -> Motion {
        let limits = [self.declaration.width - 1, self.declaration.height - 1];
        let mut next = *motion;
        for (axis, &limit) in limits.iter().enumerate() {
            let reached = motion.position[axis] + motion.velocity[axis];
            if reached < 0 || reached > limit {
                next.position[axis] = reached.clamp(0, limit);
                next.velocity[axis] = 0;
            } else {
                next.position[axis] = reached;
            }
        }
        next
    }

    /// **The observed motion after a cell** (module header), from the motion before it alone: a
    /// move letter realizes the move `(v, v + Δv)` of its change and steps, a slip realizes the held
    /// move `(v, v)` and steps, a wall applies the wall law to the held velocity; a step that would
    /// leave the arena meets the wall law too, so the observed motion stays inside for every cell.
    /// Refused at a cell outside the alphabet.
    pub fn observe(
        &self,
        moves: &Moves,
        motion: &Motion,
        cell: usize,
    ) -> Result<Motion, TerrainError> {
        let realized = match moves.read(cell) {
            Some(Letter::Move(change)) => Move::by_change(motion.velocity, change),
            Some(Letter::Slip) | Some(Letter::Wall) => Move::held(motion.velocity),
            None => {
                return Err(refuse(
                    "a chase cell",
                    "it lies in the declared move alphabet",
                ));
            }
        };
        let velocity = realized.after;
        let kept = Motion {
            position: motion.position,
            velocity,
        };
        let stepped = add(motion.position, velocity);
        if cell != moves.wall() && self.inside(stepped) {
            return Ok(Motion {
                position: stepped,
                velocity,
            });
        }
        Ok(self.wall(&kept))
    }
}

// -------------------------------------------------------------------------------------------
// the constitution and the move alphabet

/// [definition] **A mover's constitution at the ground contact** (module header): its speed bound
/// `v` and traction coefficient `γ`, positive rationals.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct RunnerLaw {
    pub speed: Rat,
    pub traction: Rat,
}

/// [definition] **A constitution's caps on the lattice**: `⌊v²⌋` and, per class, `⌊(γ μ_c k)²⌋`;
/// an integer quadrance meets each rational bound exactly when it meets its floor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Caps {
    pub speed: i64,
    pub classes: Vec<i64>,
}

impl Caps {
    /// The top cap: the highest class's (the classes ascend), the greatest change any contact
    /// admits.
    pub fn top(&self) -> i64 {
        *self.classes.last().expect("a declaration holds a class")
    }
}

impl RunnerLaw {
    /// Refused unless both bounds are positive.
    pub fn check(&self) -> Result<(), TerrainError> {
        if !self.speed.is_positive() || !self.traction.is_positive() {
            return Err(refuse(
                "a law",
                "its speed bound and traction coefficient are positive",
            ));
        }
        Ok(())
    }

    /// **The traction law** (module header): the move `(v, v + Δv)` lies in the traction disk
    /// `⟨Δv, Δv⟩ ≤ (γ μ_c g h²/ℓ)²`, read in ℚ ([`Move::within_bound`]). The disk reads the change
    /// alone, so every opening velocity admits the same changes: the move is read in the frame of its
    /// opening velocity, from rest.
    pub fn admits(&self, declaration: &ArenaDeclaration, class: usize, change: Point) -> bool {
        declaration
            .traction_bound(&self.traction, class)
            .is_some_and(|bound| Move::by_change([0, 0], change).within_bound(&bound))
    }

    /// **The speed law**: `⟨v, v⟩ ≤ v²`, read in ℚ.
    pub fn within_speed(&self, velocity: Point) -> bool {
        Rat::from_integer(BigInt::from(quadrance(velocity))) <= &self.speed * &self.speed
    }

    /// The constitution's caps on the declared arena's lattice.
    pub fn caps(&self, declaration: &ArenaDeclaration) -> Result<Caps, TerrainError> {
        self.check()?;
        declaration.check()?;
        let classes = (0..declaration.classes.len())
            .map(|class| {
                floor_cap(
                    &declaration
                        .traction_bound(&self.traction, class)
                        .expect("a declared class"),
                )
            })
            .collect::<Result<Vec<_>, _>>()?;
        Ok(Caps {
            speed: floor_cap(&(&self.speed * &self.speed))?,
            classes,
        })
    }
}

/// [definition] **A cell's reading**: a realized move, named by its change `Δv` (its move pair is
/// `(v, v + Δv)` from the observed velocity, [`Move::by_change`]), a slip, or a wall meeting.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Letter {
    Move(Point),
    Slip,
    Wall,
}

/// [definition] **The move alphabet** (module header): the lattice moves of quadrance at most the
/// cap in canonical order (quadrance, then `Δx`, then `Δy`), then the slip and the wall letters.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Moves {
    vectors: Vec<Point>,
    cap: i64,
}

impl Moves {
    /// The moves of quadrance at most `cap ≥ 0`.
    pub fn within(cap: i64) -> Result<Self, TerrainError> {
        if !(0..=MOVE_CAP_LIMIT).contains(&cap) {
            return Err(refuse(
                "a move alphabet",
                "its cap is nonnegative and at most 2^12",
            ));
        }
        let mut radius = 0i64;
        while (radius + 1) * (radius + 1) <= cap {
            radius += 1;
        }
        let mut vectors: Vec<Point> = (-radius..=radius)
            .flat_map(|dx| (-radius..=radius).map(move |dy| [dx, dy]))
            .filter(|&change| quadrance(change) <= cap)
            .collect();
        vectors.sort_by_key(|&change| (quadrance(change), change[0], change[1]));
        Ok(Self { vectors, cap })
    }

    pub fn cap(&self) -> i64 {
        self.cap
    }

    /// The moves, in canonical order.
    pub fn vectors(&self) -> &[Point] {
        &self.vectors
    }

    /// The letter of a move, if the alphabet holds it.
    pub fn letter(&self, change: Point) -> Option<usize> {
        self.vectors.iter().position(|&v| v == change)
    }

    /// The slip letter.
    pub fn slip(&self) -> usize {
        self.vectors.len()
    }

    /// The wall letter.
    pub fn wall(&self) -> usize {
        self.vectors.len() + 1
    }

    /// The alphabet: the moves, the slip and the wall.
    pub fn alphabet(&self) -> usize {
        self.vectors.len() + 2
    }

    /// **A cell's reading**, none outside the alphabet.
    pub fn read(&self, cell: usize) -> Option<Letter> {
        match cell {
            c if c < self.vectors.len() => Some(Letter::Move(self.vectors[c])),
            c if c == self.slip() => Some(Letter::Slip),
            c if c == self.wall() => Some(Letter::Wall),
            _ => None,
        }
    }
}

// -------------------------------------------------------------------------------------------
// the runner

/// [definition] **An evasion navigator** (module header).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum Evasion {
    Flee,
    Circle { clockwise: bool },
    ZigZag { period: u64 },
}

impl Evasion {
    /// The navigator's declared integers: its kind and its parameter.
    pub fn code(&self) -> [u64; 2] {
        match self {
            Evasion::Flee => [0, 0],
            Evasion::Circle { clockwise } => [1, u64::from(*clockwise)],
            Evasion::ZigZag { period } => [2, *period],
        }
    }

    pub fn label(&self) -> String {
        match self {
            Evasion::Flee => "flee".to_string(),
            Evasion::Circle { clockwise: false } => "circle ccw".to_string(),
            Evasion::Circle { clockwise: true } => "circle cw".to_string(),
            Evasion::ZigZag { period } => format!("zig-zag P = {period}"),
        }
    }

    /// **The navigator's score of a next velocity** (module header), least best, against a chaser
    /// at a grain `g ≥ 1` (its position `X/g` carried as `X`, [`Runner::demand_at_grain`]): each
    /// score is read in the grain's units, `g²` times the plane's, so at `g = 1` it is the lattice's.
    fn score(
        &self,
        arena: &Arena,
        motion: &Motion,
        next: Point,
        chaser: Point,
        grain: i64,
        tick: u64,
    ) -> i64 {
        let x = motion.position;
        match self {
            // g²·|x + v′ − X/g|² = |g(x + v′) − X|².
            Evasion::Flee => -quadrance(sub(scale(grain, add(x, next)), chaser)),
            Evasion::Circle { clockwise } => {
                let sign = if *clockwise { -1 } else { 1 };
                let declaration = arena.declaration();
                let offset = sub(scale(2, x), [declaration.width - 1, declaration.height - 1]);
                // 2x′ − 2(x + σJ(x − c)) = 2v′ − σJ(2x − 2c).
                quadrance(sub(scale(2, next), scale(sign, quarter_turn(offset))))
            }
            Evasion::ZigZag { period } => {
                let sign = if (tick % (2 * period)) < *period {
                    1
                } else {
                    -1
                };
                // g²·|v′ − (a + σJa)|² with a = x − X/g: |g v′ − (A + σJA)|², A = g x − X.
                let away = sub(scale(grain, x), chaser);
                quadrance(sub(
                    scale(grain, next),
                    add(away, scale(sign, quarter_turn(away))),
                ))
            }
        }
    }
}

/// [definition] **A runner** (module header): its constitution, its slip hold `s ≥ 1` and its
/// evasion navigator.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Runner {
    pub law: RunnerLaw,
    pub hold: u64,
    pub evasion: Evasion,
}

/// [definition] **A runner's state**: its observed motion, the class of the ground it last pushed
/// from (both read from the cells and the ports), and the slip ticks still held (its own).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct RunnerState {
    pub motion: Motion,
    pub ground: usize,
    pub held: u64,
}

impl RunnerState {
    /// **The opening state** at rest on a position of the arena: its ground its own class.
    pub fn opening(arena: &Arena, position: Point) -> Result<Self, TerrainError> {
        let ground = arena
            .class(position)
            .ok_or_else(|| refuse("a runner's opening", "it lies in the arena"))?;
        Ok(Self {
            motion: Motion::rest(position),
            ground,
            held: 0,
        })
    }
}

impl Runner {
    /// Refused at a nonpositive bound, a hold of zero or a zig-zag of period zero.
    pub fn check(&self) -> Result<(), TerrainError> {
        self.law.check()?;
        if self.hold == 0 || matches!(self.evasion, Evasion::ZigZag { period: 0 }) {
            return Err(refuse(
                "a runner",
                "its slip holds at least one tick and a zig-zag's period is positive",
            ));
        }
        Ok(())
    }

    pub fn label(&self) -> String {
        format!(
            "runner v = {}, γ = {}, hold {}, {}",
            self.law.speed,
            self.law.traction,
            self.hold,
            self.evasion.label()
        )
    }

    /// **The demand** (module header): the navigator's best change among those whose move
    /// `(v, v + Δv)` lies in the traction disk of the ground last pushed from, within the speed
    /// bound, keeping the runner inside; ties to the first in canonical order; none when no change
    /// keeps it inside.
    pub fn demand(
        &self,
        arena: &Arena,
        moves: &Moves,
        caps: &Caps,
        state: &RunnerState,
        chaser: Point,
        tick: u64,
    ) -> Option<Point> {
        self.demand_at_grain(arena, moves, caps, state, chaser, 1, tick)
    }

    /// [definition; agent-inferred] **The demand against a chaser at a grain** (THE_REBUILD U4's
    /// move-set reading, `pursuit::MoveSet`): the chaser stands at `X/g` on the lattice
    /// `(1/g)ℤ[i]`, carried as its numerator `X` and the grain `g ≥ 1`. The navigators are laws of
    /// the plane (the flee's pair quadrance, the zig-zag's direction from the chaser, the circle's
    /// centre); read in the grain's units every score is `g²` times the plane's, an exact positive
    /// multiple, so the order and its ties are the plane's, and at `g = 1` this is [`Runner::demand`].
    #[allow(clippy::too_many_arguments)]
    pub fn demand_at_grain(
        &self,
        arena: &Arena,
        moves: &Moves,
        caps: &Caps,
        state: &RunnerState,
        chaser: Point,
        grain: i64,
        tick: u64,
    ) -> Option<Point> {
        let motion = &state.motion;
        let expected = caps.classes.get(state.ground).copied()?;
        let mut best: Option<(Point, i64)> = None;
        for &change in moves.vectors() {
            let demanded = Move::by_change(motion.velocity, change);
            // The changes ascend in quadrance: past the disk's edge, every later one is outside.
            if !demanded.within_cap(expected) {
                break;
            }
            let next = demanded.after;
            if quadrance(next) > caps.speed || !arena.inside(add(motion.position, next)) {
                continue;
            }
            let score = self.evasion.score(arena, motion, next, chaser, grain, tick);
            if best.is_none_or(|(_, least)| score < least) {
                best = Some((change, score));
            }
        }
        best.map(|(change, _)| change)
    }

    /// **The runner's cell at a tick** (module header): a held slip, the realized demand, a slip
    /// onset where the demanded move lies outside the traction disk of the cell it stands on (its
    /// realized move is then the held one), or the wall. Refused when the runner stands outside the
    /// arena or its top cap passes the alphabet's.
    pub fn cell(
        &self,
        arena: &Arena,
        moves: &Moves,
        caps: &Caps,
        state: &RunnerState,
        chaser: Point,
        tick: u64,
    ) -> Result<usize, TerrainError> {
        self.cell_at_grain(arena, moves, caps, state, chaser, 1, tick)
    }

    /// **The runner's cell against a chaser at a grain** ([`Runner::demand_at_grain`]); at `g = 1`
    /// it is [`Runner::cell`]. Refused at a grain below one.
    #[allow(clippy::too_many_arguments)]
    pub fn cell_at_grain(
        &self,
        arena: &Arena,
        moves: &Moves,
        caps: &Caps,
        state: &RunnerState,
        chaser: Point,
        grain: i64,
        tick: u64,
    ) -> Result<usize, TerrainError> {
        if grain < 1 {
            return Err(refuse("a chaser's grain", "it is at least one"));
        }
        let motion = &state.motion;
        let class = arena
            .class(motion.position)
            .ok_or_else(|| refuse("a runner's position", "it lies in the arena"))?;
        if caps.top() > moves.cap() {
            return Err(refuse(
                "a runner's move alphabet",
                "it holds every change the runner's traction admits",
            ));
        }
        let kept = || {
            if arena.inside(add(motion.position, motion.velocity)) {
                moves.slip()
            } else {
                moves.wall()
            }
        };
        if state.held > 0 {
            return Ok(kept());
        }
        Ok(match self.demand_at_grain(arena, moves, caps, state, chaser, grain, tick) {
            None => moves.wall(),
            Some(change)
                if Move::by_change(motion.velocity, change).within_cap(caps.classes[class]) =>
            {
                moves
                    .letter(change)
                    .expect("a demand within the top cap has its letter")
            }
            Some(_) => kept(),
        })
    }

    /// **The runner's state after a cell**: the observed motion ([`Arena::observe`]), the ground it
    /// pushed from (its position's class before the step) and its own slip counter (a slip letter
    /// starts a hold of `s` ticks or spends one of it; any other letter ends it).
    pub fn receive(
        &self,
        arena: &Arena,
        moves: &Moves,
        state: &RunnerState,
        cell: usize,
    ) -> Result<RunnerState, TerrainError> {
        let motion = arena.observe(moves, &state.motion, cell)?;
        let ground = arena
            .class(state.motion.position)
            .ok_or_else(|| refuse("a runner's position", "it lies in the arena"))?;
        let held = if cell == moves.slip() {
            if state.held > 0 {
                state.held - 1
            } else {
                self.hold - 1
            }
        } else {
            0
        };
        Ok(RunnerState {
            motion,
            ground,
            held,
        })
    }
}

// -------------------------------------------------------------------------------------------
// the pursuer

/// [definition] **The scripted pursuer** (module header): pure pursuit under its constitution,
/// capturing at quadrance at most `capture = ρ² ≥ 0`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Pursuer {
    pub law: RunnerLaw,
    pub capture: Rat,
}

impl Pursuer {
    /// **Capture** (module header): `⟨x_R − x_C, x_R − x_C⟩ ≤ ρ²`, read in ℚ.
    pub fn captures(&self, runner: Point, chaser: Point) -> bool {
        Rat::from_integer(BigInt::from(quadrance(sub(runner, chaser)))) <= self.capture
    }

    /// **Its traction-admitted next motions** from a motion: every move `(v, v + Δv)` in the
    /// traction disk of its cell, within its speed bound, keeping it inside, in canonical order of
    /// the change; none when no change does.
    pub fn motions(
        &self,
        arena: &Arena,
        disk: &Moves,
        caps: &Caps,
        motion: &Motion,
    ) -> Result<Vec<Motion>, TerrainError> {
        let class = arena
            .class(motion.position)
            .ok_or_else(|| refuse("a pursuer's position", "it lies in the arena"))?;
        Ok(disk
            .vectors()
            .iter()
            .map(|&change| Move::by_change(motion.velocity, change))
            .filter(|next| next.within_cap(caps.classes[class]))
            .map(|next| next.after)
            .filter(|&velocity| quadrance(velocity) <= caps.speed)
            .map(|velocity| Motion {
                position: add(motion.position, velocity),
                velocity,
            })
            .filter(|next| arena.inside(next.position))
            .collect())
    }

    /// **Its admitted next motions** from a motion: its traction-admitted motions
    /// ([`Pursuer::motions`]); the wall law's motion alone when none does.
    pub fn admitted(
        &self,
        arena: &Arena,
        disk: &Moves,
        caps: &Caps,
        motion: &Motion,
    ) -> Result<Vec<Motion>, TerrainError> {
        let next = self.motions(arena, disk, caps, motion)?;
        Ok(if next.is_empty() {
            vec![arena.wall(motion)]
        } else {
            next
        })
    }

    /// [proved-derived] **Whether it can always stop**: its speed cap is at most its least class
    /// cap. Then from every motion within its speed bound the change `−v` to rest is admitted on
    /// every cell and keeps it where it stands, so its traction-admitted motions are never empty
    /// and it never meets the wall law: every motion it emits satisfies its traction bound.
    pub fn stops(&self, declaration: &ArenaDeclaration) -> Result<bool, TerrainError> {
        let caps = self.law.caps(declaration)?;
        Ok(caps.classes.iter().all(|&cap| caps.speed <= cap))
    }

    /// **Pure pursuit**: the admitted next motion whose position is nearest the target in
    /// quadrance, ties to the first.
    pub fn step(
        &self,
        arena: &Arena,
        disk: &Moves,
        caps: &Caps,
        motion: &Motion,
        target: Point,
    ) -> Result<Motion, TerrainError> {
        let admitted = self.admitted(arena, disk, caps, motion)?;
        let mut best = admitted[0];
        for next in &admitted[1..] {
            if quadrance(sub(next.position, target)) < quadrance(sub(best.position, target)) {
                best = *next;
            }
        }
        Ok(best)
    }
}

// -------------------------------------------------------------------------------------------
// the declared candidate family

/// [definition] **The declared runner family**: every candidate `(v, γ, s, navigator)` of the
/// declared speeds, tractions, holds and navigators, indexed mixed-radix with the speed least
/// significant, then the traction, the hold and the navigator.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RunnerFamily {
    pub speeds: Vec<Rat>,
    pub tractions: Vec<Rat>,
    pub holds: Vec<u64>,
    pub evasions: Vec<Evasion>,
}

impl RunnerFamily {
    /// The number of candidates `N`.
    pub fn len(&self) -> usize {
        self.speeds.len() * self.tractions.len() * self.holds.len() * self.evasions.len()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// **Each candidate's description** `⌈log₂ N⌉` bits: the family's uniform naming.
    pub fn description(&self) -> u64 {
        ceil_log2(&BigUint::from(self.len()))
    }

    /// **Candidate `index < N`** (the family's mixed-radix order).
    pub fn candidate(&self, index: usize) -> Result<Runner, TerrainError> {
        if index >= self.len() {
            return Err(refuse(
                "a runner candidate",
                "its index lies in the declared family",
            ));
        }
        let mut rest = index;
        let mut digit = |radix: usize| {
            let d = rest % radix;
            rest /= radix;
            d
        };
        let speed = self.speeds[digit(self.speeds.len())].clone();
        let traction = self.tractions[digit(self.tractions.len())].clone();
        let hold = self.holds[digit(self.holds.len())];
        let evasion = self.evasions[digit(self.evasions.len())];
        let runner = Runner {
            law: RunnerLaw { speed, traction },
            hold,
            evasion,
        };
        runner.check()?;
        Ok(runner)
    }

    /// **The family's move alphabet on an arena**: the moves within the greatest top cap of its
    /// tractions.
    pub fn moves(&self, declaration: &ArenaDeclaration) -> Result<Moves, TerrainError> {
        if self.is_empty() {
            return Err(refuse(
                "a runner family",
                "it declares at least one candidate",
            ));
        }
        let mut cap = 0;
        for traction in &self.tractions {
            let caps = RunnerLaw {
                speed: self.speeds[0].clone(),
                traction: traction.clone(),
            }
            .caps(declaration)?;
            cap = cap.max(caps.top());
        }
        Moves::within(cap)
    }

    /// **The key space** `N · m^P · WH · (WH − 1)` of a drawn chase (module header).
    pub fn key_space(&self, declaration: &ArenaDeclaration) -> BigUint {
        let positions = BigUint::from(declaration.positions());
        BigUint::from(self.len())
            * BigUint::from(declaration.classes.len())
                .pow(u32::try_from(declaration.patches()).expect("a patch count within a word"))
            * &positions
            * (positions - 1u32)
    }
}

// -------------------------------------------------------------------------------------------
// the chase

/// [definition] **The receiver's ports on a chase**: the arena, the move alphabet, the chaser's
/// motion port (the admitted action port) and the runner's opening motion. The cells are the
/// runner's; these are what the receiver reads beside them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChasePorts {
    pub arena: Arena,
    pub moves: Moves,
    pub chaser: ChaserPort,
    pub opening: Motion,
}

/// [definition; agent-inferred] **The chaser's motion port**: the chaser's motion at each tick,
/// in tick order. In the reception phase the scripted pursuer's motions at every tick of the
/// passage and the one after it are written whole before any reading. In the action phase
/// (`holarchy::terrain::pursuit`) the chaser writes its motion at each tick as it stands there,
/// and the receiver reads the tick it has reached: a port is written by its Holon and read by the
/// receiver joined to it, so it is appended through a shared handle. A clone copies the motions
/// (a value, never a second writer); equality compares them.
#[derive(Debug, Default)]
pub struct ChaserPort(RwLock<Vec<Motion>>);

impl ChaserPort {
    /// A port holding these motions.
    pub fn new(motions: Vec<Motion>) -> Self {
        Self(RwLock::new(motions))
    }

    fn read(&self) -> std::sync::RwLockReadGuard<'_, Vec<Motion>> {
        self.0.read().unwrap_or_else(PoisonError::into_inner)
    }

    /// The chaser's motion at a tick, none past the ticks written.
    pub fn get(&self, tick: usize) -> Option<Motion> {
        self.read().get(tick).copied()
    }

    /// The ticks written.
    pub fn len(&self) -> usize {
        self.read().len()
    }

    pub fn is_empty(&self) -> bool {
        self.read().is_empty()
    }

    /// **Write the chaser's motion at the next tick.**
    pub fn push(&self, motion: Motion) {
        self.0
            .write()
            .unwrap_or_else(PoisonError::into_inner)
            .push(motion);
    }

    /// The motions written, in tick order.
    pub fn motions(&self) -> Vec<Motion> {
        self.read().clone()
    }
}

impl Clone for ChaserPort {
    fn clone(&self) -> Self {
        Self::new(self.motions())
    }
}

impl PartialEq for ChaserPort {
    fn eq(&self, other: &Self) -> bool {
        *self.read() == *other.read()
    }
}

impl Eq for ChaserPort {}

/// [definition] **The chase's exact truth receipt** (module header).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChaseTruth {
    pub seed: Option<u64>,
    pub index: usize,
    pub runner: Runner,
    pub pursuer: Pursuer,
    pub runner_start: Point,
    pub chaser_start: Point,
    pub key_space: BigUint,
    pub key_bits: u64,
    /// The runner's motion after each tick.
    pub path: Vec<Motion>,
    /// Slip onsets, slip letters (onsets and held ticks) and wall meetings.
    pub slips: usize,
    pub slip_ticks: usize,
    pub walls: usize,
    /// The tick of capture, which ends the passage; none when the passage runs its ticks.
    pub captured: Option<usize>,
}

/// [definition] **A candidate's replay over the passage**: the ticks its law's cell differs from
/// the received one, and its state after the passage.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Replay {
    pub contradictions: Vec<usize>,
    pub end: RunnerState,
}

/// [definition] **The fibre's future classes** (module header): over every admitted chaser word of
/// `horizon` ticks, the fibre's members grouped by the cells they emit, the truth's class first
/// when the truth is a member, and the first word on which the truth's class parts from another.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Futures {
    pub horizon: usize,
    pub words: usize,
    pub classes: Vec<Vec<usize>>,
    pub separating: Option<Vec<Point>>,
}

/// [definition] **A chase with its truth** (module header).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Chase {
    pub ports: Arc<ChasePorts>,
    pub cells: Vec<usize>,
    pub truth: ChaseTruth,
}

impl Chase {
    /// **The chase of a declared arena, candidate and openings** over at most `ticks` ticks (module
    /// header): each tick the runner's cell is read against the pursuer's present position, the
    /// pursuer pursues the runner's present position, and both move; the passage ends at capture.
    /// Refused unless the openings are positions of the arena outside capture, the capture radius
    /// squared is nonnegative, and the pursuer is slower and of larger traction than the runner.
    pub fn run(
        arena: Arena,
        family: &RunnerFamily,
        index: usize,
        pursuer: &Pursuer,
        openings: [Point; 2],
        ticks: usize,
    ) -> Result<Self, TerrainError> {
        let runner = family.candidate(index)?;
        let declaration = arena.declaration().clone();
        let [runner_start, chaser_start] = openings;
        if pursuer.capture.is_negative() {
            return Err(refuse(
                "a pursuer's capture",
                "its radius squared is nonnegative",
            ));
        }
        if !arena.inside(runner_start)
            || !arena.inside(chaser_start)
            || pursuer.captures(runner_start, chaser_start)
        {
            return Err(refuse(
                "a chase's openings",
                "the runner and the pursuer open in the arena, outside capture",
            ));
        }
        if pursuer.law.speed >= runner.law.speed || pursuer.law.traction <= runner.law.traction {
            return Err(refuse(
                "a chase's pursuer",
                "it is slower than the runner and of larger traction",
            ));
        }
        let moves = family.moves(&declaration)?;
        let caps = runner.law.caps(&declaration)?;
        let pursuer_caps = pursuer.law.caps(&declaration)?;
        let disk = Moves::within(pursuer_caps.top())?;
        let mut state = RunnerState::opening(&arena, runner_start)?;
        let opening = state.motion;
        let mut chaser = Motion::rest(chaser_start);
        let (mut cells, mut chasers, mut path) = (Vec::new(), Vec::new(), Vec::new());
        let (mut slips, mut slip_ticks, mut walls, mut captured) = (0, 0, 0, None);
        for tick in 0..ticks {
            if pursuer.captures(state.motion.position, chaser.position) {
                captured = Some(tick);
                break;
            }
            chasers.push(chaser);
            let cell = runner.cell(&arena, &moves, &caps, &state, chaser.position, tick as u64)?;
            if cell == moves.slip() {
                slip_ticks += 1;
                slips += usize::from(state.held == 0);
            }
            walls += usize::from(cell == moves.wall());
            chaser = pursuer.step(&arena, &disk, &pursuer_caps, &chaser, state.motion.position)?;
            state = runner.receive(&arena, &moves, &state, cell)?;
            cells.push(cell);
            path.push(state.motion);
        }
        chasers.push(chaser);
        let key_space = family.key_space(&declaration);
        Ok(Self {
            ports: Arc::new(ChasePorts {
                arena,
                moves,
                chaser: ChaserPort::new(chasers),
                opening,
            }),
            cells,
            truth: ChaseTruth {
                seed: None,
                index,
                runner,
                pursuer: pursuer.clone(),
                runner_start,
                chaser_start,
                key_bits: ceil_log2(&key_space),
                key_space,
                path,
                slips,
                slip_ticks,
                walls,
                captured,
            },
        })
    }

    /// **The chase drawn** from its seed (module header): the candidate uniform on the family, each
    /// patch's class uniform, the runner's position uniform, the pursuer's uniform on the others (a
    /// draw opening within capture is refused).
    pub fn draw(
        declaration: &ArenaDeclaration,
        family: &RunnerFamily,
        pursuer: &Pursuer,
        ticks: usize,
        seed: u64,
    ) -> Result<Self, TerrainError> {
        let (index, arena, openings) = Self::drawn(declaration, family, seed)?;
        let mut chase = Self::run(arena, family, index, pursuer, openings, ticks)?;
        chase.truth.seed = Some(seed);
        Ok(chase)
    }

    /// **A seed's drawn key** (module header): the candidate's index uniform on the family, the
    /// arena with each patch's class uniform, and the openings (the runner's position uniform, the
    /// chaser's uniform on the others). The action phase (`holarchy::terrain::pursuit`) reads the
    /// same draw, so a seed names the same runner, arena and openings in both phases.
    pub fn drawn(
        declaration: &ArenaDeclaration,
        family: &RunnerFamily,
        seed: u64,
    ) -> Result<(usize, Arena, [Point; 2]), TerrainError> {
        if family.is_empty() {
            return Err(refuse(
                "a runner family",
                "it declares at least one candidate",
            ));
        }
        let mut draw = Draw::new(seed);
        let index = draw.below(family.len());
        let arena = Arena::draw(declaration.clone(), &mut draw)?;
        let positions = declaration.positions();
        let runner = draw.below(positions);
        let mut chaser = draw.below(positions - 1);
        if chaser >= runner {
            chaser += 1;
        }
        Ok((
            index,
            arena,
            [declaration.position(runner), declaration.position(chaser)],
        ))
    }

    /// **A candidate's replay** (module header): at each tick its law's cell read from the observed
    /// motion, the pursuer's port and its own slip counter, against the received cell; its state
    /// then follows the received cell.
    pub fn replay(&self, runner: &Runner) -> Result<Replay, TerrainError> {
        let ports = &self.ports;
        let caps = runner.law.caps(ports.arena.declaration())?;
        let mut state = RunnerState::opening(&ports.arena, ports.opening.position)?;
        let chaser = ports.chaser.motions();
        if chaser.len() < self.cells.len() {
            return Err(refuse(
                "a chase's ports",
                "the chaser's port holds every tick of the passage",
            ));
        }
        let mut contradictions = Vec::new();
        for (tick, &cell) in self.cells.iter().enumerate() {
            let own = runner.cell(
                &ports.arena,
                &ports.moves,
                &caps,
                &state,
                chaser[tick].position,
                tick as u64,
            )?;
            if own != cell {
                contradictions.push(tick);
            }
            state = runner.receive(&ports.arena, &ports.moves, &state, cell)?;
        }
        Ok(Replay {
            contradictions,
            end: state,
        })
    }

    /// **The surviving fibre** (module header): the family's candidates whose law emits every
    /// received cell, ascending.
    pub fn fibre(&self, family: &RunnerFamily) -> Result<Vec<usize>, TerrainError> {
        let mut fibre = Vec::new();
        for index in 0..family.len() {
            if self
                .replay(&family.candidate(index)?)?
                .contradictions
                .is_empty()
            {
                fibre.push(index);
            }
        }
        Ok(fibre)
    }

    /// **The admitted chaser words** of `horizon` ticks from the pursuer's motion after the passage:
    /// its present position, then each admitted next position for the remaining ticks.
    fn words(&self, pursuer: &Pursuer, horizon: usize) -> Result<Vec<Vec<Point>>, TerrainError> {
        let ports = &self.ports;
        let caps = pursuer.law.caps(ports.arena.declaration())?;
        let disk = Moves::within(caps.top())?;
        let start = ports
            .chaser
            .get(self.cells.len())
            .ok_or_else(|| refuse("a chase's ports", "they hold the pursuer after the passage"))?;
        let mut words = vec![(vec![start.position], start)];
        for _ in 1..horizon {
            let mut next = Vec::new();
            for (word, motion) in words {
                for moved in pursuer.admitted(&ports.arena, &disk, &caps, &motion)? {
                    let mut longer = word.clone();
                    longer.push(moved.position);
                    next.push((longer, moved));
                }
            }
            words = next;
        }
        Ok(words.into_iter().map(|(word, _)| word).collect())
    }

    /// **The fibre's future classes** over every admitted chaser word of `horizon ≥ 1` ticks
    /// (module header): each member continues from its replayed state and emits its cells against
    /// the word; members emitting alike under every word are one class.
    pub fn futures(
        &self,
        family: &RunnerFamily,
        fibre: &[usize],
        pursuer: &Pursuer,
        horizon: usize,
    ) -> Result<Futures, TerrainError> {
        if horizon == 0 || fibre.is_empty() {
            return Err(refuse(
                "a fibre's future classes",
                "they read a nonempty fibre over at least one tick",
            ));
        }
        let ports = &self.ports;
        let words = self.words(pursuer, horizon)?;
        let opened = self.cells.len() as u64;
        let mut signatures: BTreeMap<Vec<Vec<usize>>, Vec<usize>> = BTreeMap::new();
        let mut order: Vec<Vec<Vec<usize>>> = Vec::new();
        for &index in fibre {
            let runner = family.candidate(index)?;
            let caps = runner.law.caps(ports.arena.declaration())?;
            let end = self.replay(&runner)?.end;
            let mut signature = Vec::with_capacity(words.len());
            for word in &words {
                let mut state = end;
                let mut emitted = Vec::with_capacity(horizon);
                for (k, &chaser) in word.iter().enumerate() {
                    let cell = runner.cell(
                        &ports.arena,
                        &ports.moves,
                        &caps,
                        &state,
                        chaser,
                        opened + k as u64,
                    )?;
                    state = runner.receive(&ports.arena, &ports.moves, &state, cell)?;
                    emitted.push(cell);
                }
                signature.push(emitted);
            }
            if !signatures.contains_key(&signature) {
                order.push(signature.clone());
            }
            signatures.entry(signature).or_default().push(index);
        }
        let truth = order
            .iter()
            .position(|signature| signatures[signature].contains(&self.truth.index))
            .unwrap_or(0);
        order.swap(0, truth);
        let separating = order.get(1).map(|other| {
            let at = order[0]
                .iter()
                .zip(other)
                .position(|(a, b)| a != b)
                .expect("two classes differ on some word");
            words[at].clone()
        });
        Ok(Futures {
            horizon,
            words: words.len(),
            classes: order
                .iter()
                .map(|signature| signatures[signature].clone())
                .collect(),
            separating,
        })
    }
}
