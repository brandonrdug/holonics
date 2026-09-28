//! The chase terrain's laws checked exactly on small arenas: the traction law refusing an
//! inadmissible change and the slip a demand beyond it causes, a slip held for its declared ticks,
//! the wall law keeping every mover inside, capture ending the passage, the key description, and
//! reception on hash-seeded arenas: the population's selected fibre is the surviving fibre, it holds
//! the truth, its code lies within the naming margin of the truth's own code and strictly below the
//! landmark tree's on the same cells; a plural fibre the ground cannot split is one future class
//! under every admitted pursuer word. The action phase (`pursuit`): the runner's viable tube, its
//! Pre recursion matching a brute-force enumeration of runner and chaser words on a tiny arena; every
//! motion a chaser releases (the machine and both controls) within its traction bound, a chaser
//! outside it refused; the controls' laws; and the machine's certified captures kept.

use std::collections::BTreeSet;

use num_bigint::BigUint;
use num_traits::One;

use super::chase::*;
use super::pursuit::*;
use super::sensing::*;
use super::{Draw, TerrainError};
use crate::compression::landmark::context::{
    Capacity, LandmarkDeclaration, LetterFamily, StopPrior,
};
use crate::ratio::algebraic::ExactInterval;
use crate::ratio::{Rat, rat};
use crate::receiver::population::{
    ChaseFamily, Family, MachineChaser, MachineDeclaration, Plan, Population, Posterior, Release,
    TreeFamily, selected_fibre,
};

/// The declared arena: `16 × 16` positions, patches of side 4, classes ice `1/2`, grass `1`, track
/// `3/2`, `g = 8`, `h = 1/2`, `ℓ = 1`, so `k = g h²/ℓ = 2` and a unit traction coefficient admits
/// changes of radius `1`, `2` and `3` on the three classes: every class resolves on the lattice.
pub(super) fn declaration() -> ArenaDeclaration {
    ArenaDeclaration {
        width: 16,
        height: 16,
        patch: 4,
        classes: vec![rat(1, 2), rat(1, 1), rat(3, 2)],
        gravity: rat(8, 1),
        tick: rat(1, 2),
        spacing: rat(1, 1),
    }
}

/// The declared family: speeds `2, 3`, traction coefficients `1, 3/2`, holds `1, 2`, and five
/// navigators: `2·2·2·5 = 40 = 2³·5` candidates, each named by `⌈log₂ 40⌉ = 6` bits.
pub(super) fn family() -> RunnerFamily {
    RunnerFamily {
        speeds: vec![rat(2, 1), rat(3, 1)],
        tractions: vec![rat(1, 1), rat(3, 2)],
        holds: vec![1, 2],
        evasions: vec![
            Evasion::Flee,
            Evasion::Circle { clockwise: false },
            Evasion::Circle { clockwise: true },
            Evasion::ZigZag { period: 2 },
            Evasion::ZigZag { period: 3 },
        ],
    }
}

/// The scripted pursuer: speed `3/2` below both runner speeds, traction `2` above both, capturing
/// within one lattice step, diagonals included (`ρ² = 2`).
pub(super) fn pursuer() -> Pursuer {
    Pursuer {
        law: RunnerLaw {
            speed: rat(3, 2),
            traction: rat(2, 1),
        },
        capture: rat(2, 1),
    }
}

/// The escape exponent `j`: `η = 2^(−12)` (the family module's reason).
pub(super) const ESCAPE: u32 = 12;

/// The arena with every patch of one class.
pub(super) fn uniform(class: usize) -> Arena {
    let declaration = declaration();
    let patches = vec![class; declaration.patches()];
    Arena::new(declaration, patches).unwrap()
}

/// The arena of track on its left half (`x < 8`) and ice on its right.
fn track_then_ice() -> Arena {
    let declaration = declaration();
    let patches = (0..declaration.patches())
        .map(|p| if p % 4 < 2 { 2 } else { 0 })
        .collect();
    Arena::new(declaration, patches).unwrap()
}

/// A runner of speed 3, unit traction, the declared hold, fleeing.
fn fleeing(hold: u64) -> Runner {
    Runner {
        law: RunnerLaw {
            speed: rat(3, 1),
            traction: rat(1, 1),
        },
        hold,
        evasion: Evasion::Flee,
    }
}

/// The traction law is exact in ℚ: a unit coefficient admits `⟨Δv, Δv⟩ ≤ 1` on ice (the four axis
/// steps, not a diagonal), `≤ 4` on grass, `≤ 9` on track; `γ = 3/2` admits `≤ 9/4` (the diagonal
/// too), `≤ 9` and `≤ 81/4`. The caps are the bounds' floors and agree with the law on every move.
/// A demand made as on the track behind the runner slips on the ice under it, keeping the velocity;
/// the same demand is realized on track, and a runner that last pushed from ice demands within it.
#[test]
fn the_traction_bound_refuses_an_inadmissible_change() {
    let declaration = declaration();
    let unit = fleeing(1).law;
    let firm = RunnerLaw {
        speed: rat(3, 1),
        traction: rat(3, 2),
    };
    assert_eq!(declaration.scale(), rat(2, 1));
    assert_eq!(
        declaration.traction_bound(&unit.traction, 0),
        Some(rat(1, 1))
    );
    assert_eq!(
        declaration.traction_bound(&firm.traction, 2),
        Some(rat(81, 4))
    );
    assert!(unit.admits(&declaration, 0, [1, 0]));
    assert!(!unit.admits(&declaration, 0, [1, 1]));
    assert!(unit.admits(&declaration, 1, [2, 0]));
    assert!(!unit.admits(&declaration, 1, [2, 1]));
    assert!(unit.admits(&declaration, 2, [3, 0]));
    assert!(!unit.admits(&declaration, 2, [2, 3]));
    assert!(firm.admits(&declaration, 0, [1, 1]));
    assert!(!firm.admits(&declaration, 0, [2, 0]));
    assert!(firm.admits(&declaration, 2, [4, 2]));
    assert!(!firm.admits(&declaration, 2, [4, 3]));
    let caps = unit.caps(&declaration).unwrap();
    assert_eq!((caps.speed, caps.classes.clone()), (9, vec![1, 4, 9]));
    assert_eq!(firm.caps(&declaration).unwrap().classes, vec![2, 9, 20]);
    let moves = family().moves(&declaration).unwrap();
    assert_eq!(
        (moves.cap(), moves.vectors().len(), moves.alphabet()),
        (20, 69, 71)
    );
    for law in [&unit, &firm] {
        let caps = law.caps(&declaration).unwrap();
        for &change in moves.vectors() {
            for class in 0..3 {
                assert_eq!(
                    law.admits(&declaration, class, change),
                    quadrance(change) <= caps.classes[class]
                );
            }
            assert_eq!(law.within_speed(change), quadrance(change) <= caps.speed);
        }
    }
    assert!(matches!(
        Moves::within(MOVE_CAP_LIMIT + 1),
        Err(TerrainError::Declaration { .. })
    ));
    let runner = fleeing(1);
    let motion = Motion {
        position: [8, 8],
        velocity: [1, 0],
    };
    // It last pushed from track (class 2), and stands on ice.
    let state = RunnerState {
        motion,
        ground: 2,
        held: 0,
    };
    let ice = uniform(0);
    let demand = runner
        .demand(&ice, &moves, &caps, &state, [0, 8], 0)
        .unwrap();
    assert_eq!(demand, [2, 0]);
    assert!(!runner.law.admits(&declaration, 0, demand));
    let cell = runner.cell(&ice, &moves, &caps, &state, [0, 8], 0).unwrap();
    assert_eq!(cell, moves.slip());
    let next = runner.receive(&ice, &moves, &state, cell).unwrap();
    assert_eq!(
        next.motion,
        Motion {
            position: [9, 8],
            velocity: [1, 0]
        }
    );
    assert_eq!(next.ground, 0);
    let track = uniform(2);
    let cell = runner
        .cell(&track, &moves, &caps, &state, [0, 8], 0)
        .unwrap();
    assert_eq!(moves.read(cell), Some(Letter::Move(demand)));
    let reading_ice = RunnerState { ground: 0, ..state };
    let cell = runner
        .cell(&ice, &moves, &caps, &reading_ice, [0, 8], 0)
        .unwrap();
    assert_eq!(moves.read(cell), Some(Letter::Move([1, 0])));
}

/// A slip holds for its declared ticks: a runner come off the track onto ice slips at its first
/// demand; with hold 2 it keeps its velocity one more tick, with hold 1 its next demand, made as on
/// the ice it now reads, is realized. Each held tick steps by the kept velocity.
#[test]
fn slip_holds_for_its_declared_ticks() {
    let declaration = declaration();
    let arena = track_then_ice();
    let moves = family().moves(&declaration).unwrap();
    let opening = RunnerState {
        motion: Motion {
            position: [8, 8],
            velocity: [1, 0],
        },
        ground: 2,
        held: 0,
    };
    let passage = |hold: u64| -> Vec<(usize, Motion)> {
        let runner = fleeing(hold);
        let caps = runner.law.caps(&declaration).unwrap();
        let mut state = opening;
        (0..3)
            .map(|tick| {
                let cell = runner
                    .cell(&arena, &moves, &caps, &state, [0, 8], tick)
                    .unwrap();
                state = runner.receive(&arena, &moves, &state, cell).unwrap();
                (cell, state.motion)
            })
            .collect()
    };
    let held = passage(2);
    assert_eq!(held[0].0, moves.slip());
    assert_eq!(held[1].0, moves.slip(), "the hold keeps the slip");
    assert_eq!(held[0].1.position, [9, 8]);
    assert_eq!(
        held[1].1,
        Motion {
            position: [10, 8],
            velocity: [1, 0]
        }
    );
    assert!(
        held[2].0 < moves.vectors().len(),
        "the hold spent, the demand is realized"
    );
    let once = passage(1);
    assert_eq!(once[0].0, moves.slip());
    assert_eq!(moves.read(once[1].0), Some(Letter::Move([1, 0])));
    assert_eq!(
        once[1].1,
        Motion {
            position: [11, 8],
            velocity: [2, 0]
        }
    );
}

/// The wall law keeps every mover inside: a runner at the wall faster than its traction on grass can
/// brake meets the wall, its crossing velocity zeroed and its position clamped; over drawn arenas
/// every candidate's own motions against the pursuer's port and the pursuer's motions stay in the
/// arena within their speed bounds; and a passage ends at capture.
#[test]
fn walls_keep_the_runner_inside() {
    let declaration = declaration();
    let arena = uniform(1);
    let moves = family().moves(&declaration).unwrap();
    let runner = fleeing(1);
    let caps = runner.law.caps(&declaration).unwrap();
    let state = RunnerState {
        motion: Motion {
            position: [15, 8],
            velocity: [3, 1],
        },
        ground: 1,
        held: 0,
    };
    assert_eq!(
        runner.demand(&arena, &moves, &caps, &state, [0, 8], 0),
        None,
        "no change of radius 2 brakes 3 steps before the wall"
    );
    let cell = runner
        .cell(&arena, &moves, &caps, &state, [0, 8], 0)
        .unwrap();
    assert_eq!(cell, moves.wall());
    let next = runner.receive(&arena, &moves, &state, cell).unwrap();
    assert_eq!(
        next.motion,
        Motion {
            position: [15, 9],
            velocity: [0, 1]
        }
    );
    assert_eq!(
        arena.observe(&moves, &state.motion, moves.slip()).unwrap(),
        next.motion,
        "a kept step that leaves the arena meets the wall law too"
    );
    let family = family();
    let pursuer = pursuer();
    let pursuer_speed = pursuer.law.caps(&declaration).unwrap().speed;
    for seed in [1u64, 2, 3] {
        let chase = Chase::draw(&declaration, &family, &pursuer, 64, seed).unwrap();
        let arena = &chase.ports.arena;
        assert!(chase.truth.path.iter().all(|m| arena.inside(m.position)));
        assert!(
            chase
                .ports
                .chaser
                .motions()
                .iter()
                .all(|m| arena.inside(m.position) && quadrance(m.velocity) <= pursuer_speed)
        );
        match chase.truth.captured {
            Some(tick) => {
                assert_eq!(chase.cells.len(), tick);
                let caught = chase.truth.path.last().map_or(chase.ports.opening, |m| *m);
                assert!(pursuer.captures(
                    caught.position,
                    chase.ports.chaser.get(tick).unwrap().position
                ));
            }
            None => assert_eq!(chase.cells.len(), 64),
        }
        for index in 0..family.len() {
            let runner = family.candidate(index).unwrap();
            let caps = runner.law.caps(&declaration).unwrap();
            let mut state = RunnerState::opening(arena, chase.ports.opening.position).unwrap();
            for (tick, chaser) in chase.ports.chaser.motions().iter().enumerate() {
                let cell = runner
                    .cell(
                        arena,
                        &chase.ports.moves,
                        &caps,
                        &state,
                        chaser.position,
                        tick as u64,
                    )
                    .unwrap();
                state = runner
                    .receive(arena, &chase.ports.moves, &state, cell)
                    .unwrap();
                assert!(arena.inside(state.motion.position));
                assert!(quadrance(state.motion.velocity) <= caps.speed);
            }
        }
    }
}

/// The truth receipt: the drawn candidate is the family's index, the key description is
/// `⌈log₂(40 · 3^16 · 256 · 255)⌉ = 47` bits, the pursuer's port holds one motion a tick and the
/// one after, and the refusals are typed.
#[test]
fn the_truth_names_its_key() {
    let declaration = declaration();
    let family = family();
    let chase = Chase::draw(&declaration, &family, &pursuer(), 32, 7).unwrap();
    let space = BigUint::from(40u32) * BigUint::from(3u32).pow(16) * BigUint::from(256u32 * 255);
    assert_eq!(chase.truth.key_space, space);
    assert_eq!(chase.truth.key_bits, 47);
    assert!(BigUint::one() << 47 >= space && BigUint::one() << 46 < space);
    assert_eq!(
        chase.truth.runner,
        family.candidate(chase.truth.index).unwrap()
    );
    assert_eq!(chase.ports.chaser.len(), chase.cells.len() + 1);
    let mut draw = Draw::new(7);
    assert_eq!(draw.below(40), chase.truth.index);
    let slow = Pursuer {
        law: RunnerLaw {
            speed: rat(3, 1),
            traction: rat(2, 1),
        },
        capture: rat(2, 1),
    };
    assert!(matches!(
        Chase::draw(&declaration, &family, &slow, 8, 7),
        Err(TerrainError::Declaration { .. })
    ));
    assert!(matches!(
        Chase::run(uniform(2), &family, 0, &pursuer(), [[4, 4], [5, 5]], 8),
        Err(TerrainError::Declaration { .. })
    ));
    let bad = ArenaDeclaration {
        patch: 3,
        ..declaration
    };
    assert!(bad.check().is_err());
}

fn tree(alphabet: usize, depth: usize, population: usize) -> LandmarkDeclaration {
    LandmarkDeclaration {
        alphabet,
        depth,
        forced: 0,
        population: population as u64,
        grain: 16,
        family: LetterFamily::cells(),
        prior: StopPrior::half(),
        capacity: Capacity::Unbounded,
    }
}

/// The landmark tree's least code alone over a ladder of depths, reading the same cells.
fn tree_code(cells: &[usize], alphabet: usize) -> ExactInterval {
    [1usize, 2, 4]
        .iter()
        .map(|&depth| {
            let mut family = TreeFamily::new(tree(alphabet, depth, cells.len()), 0).unwrap();
            for &cell in cells {
                family.receive(cell).unwrap();
            }
            family.likelihood().code().unwrap().unwrap()
        })
        .min_by(|a, b| a.lower.cmp(&b.lower))
        .unwrap()
}

/// Reception on hash-seeded arenas (F6's reception acceptance): the surviving fibre holds the
/// truth; the population's selected fibre (its greatest posterior, read exactly) is the surviving
/// fibre, and the family it selects, when one is decided, lies in it; the fibre's joint posterior is
/// decided above one half; the population's code lies within the naming margin `⌈log₂ N⌉` of the
/// truth family's own code and strictly below the landmark tree's least code on the same cells. The
/// seeds are the harness's: a circle runner that slips, a zig-zag runner and a flee runner.
#[test]
fn reception_selects_the_surviving_fibre() {
    let declaration = declaration();
    let family = family();
    let margin = Rat::from_integer(family.description().into());
    for seed in [20_260_928u64, 20_260_931, 20_260_937] {
        let chase = Chase::draw(&declaration, &family, &pursuer(), 128, seed).unwrap();
        let fibre = chase.fibre(&family).unwrap();
        assert!(fibre.contains(&chase.truth.index), "seed {seed:#x}");
        let mut population =
            Population::new(ChaseFamily::declare(&chase, &family, ESCAPE).unwrap()).unwrap();
        population.receive_passage(&chase.cells).unwrap();
        let receipt = population.receipt().unwrap();
        assert_eq!(selected_fibre(&population), fibre, "seed {seed:#x}");
        if let Some(selected) = receipt.selected {
            assert!(fibre.contains(&selected));
        }
        assert_eq!(receipt.selected.is_some(), fibre.len() == 1);
        let Posterior::Bits(joint) = population.posterior_of(&fibre).unwrap() else {
            panic!("the fibre lives");
        };
        assert!(joint.upper < Rat::one(), "seed {seed:#x}: {joint:?}");
        let truth = receipt.families[chase.truth.index].code.clone().unwrap();
        assert!(
            &receipt.code.upper - &truth.lower <= margin,
            "seed {seed:#x}: {:?} against {truth:?}",
            receipt.code
        );
        let tree = tree_code(&chase.cells, chase.ports.moves.alphabet());
        assert!(
            receipt.code.upper < tree.lower,
            "seed {seed:#x}: {:?} against the tree's {tree:?}",
            receipt.code
        );
        let futures = chase.futures(&family, &fibre, &pursuer(), 3).unwrap();
        assert!(futures.classes[0].contains(&chase.truth.index));
        assert_eq!(
            futures.classes.iter().map(Vec::len).sum::<usize>(),
            fibre.len()
        );
    }
}

/// A plural fibre the ground cannot split: on an arena of track alone the runner never meets lower
/// ground, so no slip is demanded and the two holds emit alike on the passage; the population
/// selects both, neither alone above one half, and they are one future class under every admitted
/// pursuer word, since no action can put the runner on ice.
#[test]
fn a_plural_fibre_is_one_future_class_where_no_action_separates_it() {
    let family = family();
    let chase = Chase::run(uniform(2), &family, 0, &pursuer(), [[4, 4], [12, 12]], 48).unwrap();
    assert_eq!(chase.truth.slips, 0);
    let fibre = chase.fibre(&family).unwrap();
    // Hold 2 with the truth's speed, traction and navigator: the hold's digit weighs 2·2.
    let other_hold = 4;
    assert!(
        fibre.contains(&0) && fibre.contains(&other_hold),
        "{fibre:?}"
    );
    let mut population =
        Population::new(ChaseFamily::declare(&chase, &family, ESCAPE).unwrap()).unwrap();
    population.receive_passage(&chase.cells).unwrap();
    assert_eq!(selected_fibre(&population), fibre);
    assert_eq!(population.receipt().unwrap().selected, None);
    let futures = chase.futures(&family, &fibre, &pursuer(), 3).unwrap();
    assert!(futures.words > 1);
    let truth_class = &futures.classes[0];
    assert!(truth_class.contains(&0) && truth_class.contains(&other_hold));
}

/// Two speed bounds the passage leaves together, a probe separates (the record's §14.10): on the
/// harness's seed `20260935` the pursuer captures a zig-zag runner at tick 9, before the passage
/// shows its speed; the fibre keeps speeds 2 and 3 and both holds, and over the admitted pursuer
/// words it parts by speed into two future classes with a separating word: the exact family is
/// required only where such a probe is emitted.
#[test]
fn a_probe_separates_the_speed_bounds_the_passage_leaves_together() {
    let family = family();
    let chase = Chase::draw(&declaration(), &family, &pursuer(), 256, 20_260_935).unwrap();
    assert_eq!(chase.truth.captured, Some(9));
    assert_eq!(chase.truth.index, 37);
    let fibre = chase.fibre(&family).unwrap();
    assert_eq!(fibre, vec![32, 33, 36, 37]);
    let futures = chase.futures(&family, &fibre, &pursuer(), 5).unwrap();
    assert_eq!(futures.classes, vec![vec![33, 37], vec![32, 36]]);
    assert!(futures.separating.is_some());
}

// -------------------------------------------------------------------------------------------
// the action phase

/// A tiny arena: `6 × 6` positions in patches of side 2, the declared classes and chart.
fn tiny() -> Arena {
    let declaration = ArenaDeclaration {
        width: 6,
        height: 6,
        patch: 2,
        ..declaration()
    };
    Arena::new(declaration, vec![2, 1, 0, 1, 0, 2, 0, 2, 1]).unwrap()
}

/// **The runner's successors, re-derived from the traction law in ℚ** (independent of the tube's
/// caps): the kept motion while forced; otherwise every change the constitution admits on the cell
/// it stands on, within its speed bound, keeping it inside; the wall law's motion when none.
fn successors(arena: &Arena, law: &RunnerLaw, motion: &Motion, forced: bool) -> Vec<Motion> {
    let step = |velocity: Point| {
        [
            motion.position[0] + velocity[0],
            motion.position[1] + velocity[1],
        ]
    };
    if forced {
        let kept = step(motion.velocity);
        return vec![if arena.inside(kept) {
            Motion {
                position: kept,
                velocity: motion.velocity,
            }
        } else {
            arena.wall(motion)
        }];
    }
    let class = arena.class(motion.position).unwrap();
    let wide = Moves::within(64).unwrap();
    let next: Vec<Motion> = wide
        .vectors()
        .iter()
        .filter(|&&change| law.admits(arena.declaration(), class, change))
        .map(|&change| {
            [
                motion.velocity[0] + change[0],
                motion.velocity[1] + change[1],
            ]
        })
        .filter(|&velocity| law.within_speed(velocity) && arena.inside(step(velocity)))
        .map(|velocity| Motion {
            position: step(velocity),
            velocity,
        })
        .collect();
    if next.is_empty() {
        vec![arena.wall(motion)]
    } else {
        next
    }
}

/// **The chaser's positions after every word of `k` ticks**, `k = 0, …, n`, by enumeration.
fn chaser_positions(
    arena: &Arena,
    pursuer: &Pursuer,
    chaser: Motion,
    n: usize,
) -> Vec<BTreeSet<Point>> {
    let caps = pursuer.law.caps(arena.declaration()).unwrap();
    let disk = Moves::within(caps.top()).unwrap();
    let mut words = vec![chaser];
    let mut positions = vec![BTreeSet::from([chaser.position])];
    for _ in 0..n {
        let mut next = Vec::new();
        for motion in &words {
            next.extend(pursuer.admitted(arena, &disk, &caps, motion).unwrap());
        }
        positions.push(next.iter().map(|m| m.position).collect());
        words = next;
    }
    positions
}

/// A brute-force tube: the reach and the kernel at each tick.
type BruteTube = (Vec<BTreeSet<Motion>>, Vec<BTreeSet<Motion>>);

/// **The viable tube by brute force**: every runner word of `n` ticks from the present, kept while
/// no chaser word of the same ticks captures it; the kernel at tick `k` is every motion at `k` on a
/// kept word of the full `n` ticks, the reach every motion at `k` on a kept word of `k` ticks.
fn brute_tube(
    arena: &Arena,
    law: &RunnerLaw,
    runner: Motion,
    forced: u64,
    pursuer: &Pursuer,
    chaser: Motion,
    n: usize,
) -> BruteTube {
    let positions = chaser_positions(arena, pursuer, chaser, n);
    let covered = |k: usize, x: Point| positions[k].iter().any(|&p| pursuer.captures(x, p));
    let mut reach = vec![BTreeSet::new(); n + 1];
    let mut kernel = vec![BTreeSet::new(); n + 1];
    let mut words: Vec<Vec<Motion>> = if covered(0, runner.position) {
        Vec::new()
    } else {
        vec![vec![runner]]
    };
    for word in &words {
        reach[0].insert(word[0]);
    }
    for k in 0..n {
        let mut longer = Vec::new();
        for word in &words {
            for next in successors(arena, law, &word[k], (k as u64) < forced) {
                if !covered(k + 1, next.position) {
                    let mut extended = word.clone();
                    extended.push(next);
                    reach[k + 1].insert(next);
                    longer.push(extended);
                }
            }
        }
        words = longer;
    }
    for word in &words {
        for (k, motion) in word.iter().enumerate() {
            kernel[k].insert(*motion);
        }
    }
    (reach, kernel)
}

/// **The viable tube's Pre recursion matches a brute-force enumeration** on the tiny arena: for two
/// constitutions, a slip still held and runners opening near corners, the forward viable reach and
/// the kernel `K_k` at every tick of a three-tick horizon are the enumeration's sets, and the tube's
/// sizes are theirs. A runner near the chaser is cornered (its kernel is empty while its reach is
/// not); the runner in the far corner is not.
#[test]
fn the_tube_recursion_matches_brute_force_enumeration() {
    let arena = tiny();
    let pursuer = pursuer();
    let caps = pursuer.law.caps(arena.declaration()).unwrap();
    let disk = Moves::within(caps.top()).unwrap();
    let slow = RunnerLaw {
        speed: rat(2, 1),
        traction: rat(1, 1),
    };
    let firm = RunnerLaw {
        speed: rat(3, 1),
        traction: rat(3, 2),
    };
    let moving = |position: Point, velocity: Point| Motion { position, velocity };
    let cases = [
        (&slow, moving([1, 1], [1, 0]), 0, Motion::rest([3, 3])),
        (&firm, moving([4, 2], [-2, 1]), 1, moving([2, 4], [1, 0])),
        (&firm, Motion::rest([0, 5]), 0, Motion::rest([5, 0])),
        (&slow, Motion::rest([5, 5]), 0, Motion::rest([3, 3])),
    ];
    let mut sizes = Vec::new();
    for (law, runner, forced, chaser) in cases {
        let runner_caps = law.caps(arena.declaration()).unwrap();
        let reach = CaptureReach::of(&arena, &pursuer, &caps, &disk, chaser, 3).unwrap();
        let layers = viable_layers(&arena, &runner_caps, runner, forced, &reach).unwrap();
        let (brute_reach, brute_kernel) =
            brute_tube(&arena, law, runner, forced, &pursuer, chaser, 3);
        for k in 0..=3 {
            let reach_set: BTreeSet<Motion> = layers.reach[k].iter().copied().collect();
            let kernel_set: BTreeSet<Motion> = layers.kernel[k].iter().copied().collect();
            assert_eq!(reach_set.len(), layers.reach[k].len(), "no repeats at {k}");
            assert_eq!(
                reach_set, brute_reach[k],
                "the reach at tick {k}: {runner:?}"
            );
            assert_eq!(
                kernel_set, brute_kernel[k],
                "the kernel at tick {k}: {runner:?}"
            );
        }
        let tube = viable_tube(&arena, &runner_caps, runner, forced, &reach).unwrap();
        assert_eq!(
            tube.kernel,
            (1..=3).map(|k| brute_kernel[k].len()).collect::<Vec<_>>()
        );
        assert_eq!(tube.inside, !brute_kernel[0].is_empty());
        sizes.push((tube.size(), tube.reach.iter().sum::<usize>()));
    }
    // (|K₁| + |K₂| + |K₃|, |F₁| + |F₂| + |F₃|): the runner two steps from the chaser is cornered
    // (its reach does not last the horizon), the slipping runner is caught by every word's first
    // tick, the runner in the far corner keeps 89 motions on viable paths.
    assert_eq!(sizes, vec![(0, 5), (0, 0), (89, 90), (0, 0)]);
}

/// **Every motion a chaser releases satisfies its traction bound**, read in ℚ against the
/// constitution on the cell it stood on, within its speed bound and inside the arena, for the machine
/// and both controls over hash-seeded passages; the declared chaser can always stop; the machine's
/// certified captures are kept (capture comes within the ticks the basin certified).
#[test]
fn every_chaser_motion_satisfies_its_traction_bound() {
    let declaration = declaration();
    let family = family();
    let pursuer = pursuer();
    assert!(pursuer.stops(&declaration).unwrap());
    let action = ActionDeclaration {
        pursuer: pursuer.clone(),
        ticks: 40,
        horizon: 2,
        switches: Switches::OFF,
    };
    let check = |passage: &ActionPassage| {
        let arena = &passage.ports.arena;
        let motions = passage.ports.chaser.motions();
        assert_eq!(motions.len(), passage.cells.len() + 1);
        for pair in motions.windows(2) {
            let (from, to) = (pair[0], pair[1]);
            let change = [
                to.velocity[0] - from.velocity[0],
                to.velocity[1] - from.velocity[1],
            ];
            let class = arena.class(from.position).unwrap();
            assert!(
                pursuer.law.admits(&declaration, class, change),
                "{from:?} → {to:?}"
            );
            assert!(pursuer.law.within_speed(to.velocity));
            assert_eq!(
                to.position,
                [
                    from.position[0] + to.velocity[0],
                    from.position[1] + to.velocity[1]
                ]
            );
            assert!(arena.inside(to.position));
        }
        assert_eq!(passage.tubes.len(), passage.cells.len());
    };
    for seed in [20_261_001u64, 20_261_004, 20_261_013] {
        let mut machine = MachineChaser::new(MachineDeclaration {
            family: family.clone(),
            escape: ESCAPE,
            horizon: 2,
            basin: 6,
            price: 0,
        })
        .unwrap();
        let passage = act_drawn(&declaration, &family, &action, seed, &mut machine).unwrap();
        check(&passage);
        let receipt = machine.receipt();
        assert_eq!(receipt.releases.len(), passage.cells.len());
        for (tick, bound) in receipt.certified.iter().enumerate() {
            if let Some(ticks) = bound {
                assert_eq!(receipt.releases[tick].kind(), Release::Certified);
                assert!(
                    passage.captured.is_some_and(|at| at <= tick + ticks),
                    "seed {seed}"
                );
            }
        }
        check(&act_drawn(&declaration, &family, &action, seed, &mut PurePursuit).unwrap());
        check(&act_drawn(&declaration, &family, &action, seed, &mut ConstantBearing).unwrap());
        let mut expected = MachineChaser::planning(
            MachineDeclaration {
                family: family.clone(),
                escape: ESCAPE,
                horizon: 2,
                basin: 6,
                price: 0,
            },
            Plan::Expected,
        )
        .unwrap();
        check(&act_drawn(&declaration, &family, &action, seed, &mut expected).unwrap());
    }
    let weak = Pursuer {
        law: RunnerLaw {
            speed: rat(3, 2),
            traction: rat(1, 2),
        },
        capture: rat(2, 1),
    };
    assert!(
        !weak.stops(&declaration).unwrap(),
        "on ice it cannot brake from a diagonal"
    );
}

/// **Every released bound is kept by the plan itself** (`receiver::population::chaser`, the
/// pledge), under each plan, on the 16 choosing seeds of the declared arena and on 16 fixtures of an
/// `8 × 8` arena of the same law, at the basin horizon `m = 6`: at every tick the machine releases,
/// capture comes within the bound it released; the deadlines `t + B_t` never move later; once a
/// release stands every later tick is released; and no pledge is broken (the truth lies in the
/// declared family). Each bound lies within the horizon (the chaser refuses a pledged expected
/// bound below the commit's certificate).
#[test]
fn every_released_bound_is_kept_by_the_plan_itself() {
    use rayon::prelude::*;
    let family = family();
    let action = ActionDeclaration {
        pursuer: pursuer(),
        ticks: 64,
        horizon: 2,
        switches: Switches::OFF,
    };
    let basin = 6;
    let small = ArenaDeclaration {
        width: 8,
        height: 8,
        ..declaration()
    };
    let chased: Vec<(ArenaDeclaration, u64)> = (0..16u64)
        .map(|s| (declaration(), 20_261_001 + s))
        .chain((0..16u64).map(|s| (small.clone(), s)))
        .filter(|(arena, seed)| {
            let (_, _, openings) = Chase::drawn(arena, &family, *seed).unwrap();
            !action.pursuer.captures(openings[0], openings[1])
        })
        .collect();
    assert_eq!(
        chased.len(),
        27,
        "the 16 choosing seeds and 11 of the 16 fixtures open outside capture"
    );
    let plans = [Plan::Robust, Plan::CertifiedExpected, Plan::Expected];
    let jobs: Vec<(usize, &(ArenaDeclaration, u64))> = (0..plans.len())
        .flat_map(|p| chased.iter().map(move |case| (p, case)))
        .collect();
    // Each passage is read on its own: the bounds it released, per plan.
    let released: Vec<(usize, usize)> = jobs
        .par_iter()
        .map(|&(p, (arena, seed))| {
            let plan = plans[p];
            let mut machine = MachineChaser::planning(
                MachineDeclaration {
                    family: family.clone(),
                    escape: ESCAPE,
                    horizon: 2,
                    basin,
                    price: 0,
                },
                plan,
            )
            .unwrap();
            let passage = act_drawn(arena, &family, &action, *seed, &mut machine).unwrap();
            let captured = passage
                .captured
                .unwrap_or_else(|| panic!("seed {seed}, plan {plan:?}: captured within the cap"));
            let receipt = machine.receipt();
            assert_eq!(receipt.broken, 0, "seed {seed}, plan {plan:?}");
            let (mut deadline, mut count): (Option<usize>, usize) = (None, 0);
            for (tick, bound) in receipt.certified.iter().enumerate() {
                match *bound {
                    Some(ticks) => {
                        count += 1;
                        assert_eq!(receipt.releases[tick].kind(), Release::Certified);
                        assert!((1..=basin).contains(&ticks), "seed {seed}, plan {plan:?}");
                        let at = tick + ticks;
                        assert!(captured <= at, "seed {seed}, plan {plan:?}, tick {tick}");
                        assert!(
                            deadline.is_none_or(|d| at <= d),
                            "seed {seed}, plan {plan:?}, tick {tick}"
                        );
                        deadline = Some(at);
                    }
                    None => assert!(
                        deadline.is_none(),
                        "seed {seed}, plan {plan:?}, tick {tick}"
                    ),
                }
            }
            assert_eq!(
                machine.pledge().map(|d| d as usize),
                deadline,
                "seed {seed}, plan {plan:?}"
            );
            (p, count)
        })
        .collect();
    for p in 0..plans.len() {
        let count: usize = released.iter().filter(|r| r.0 == p).map(|r| r.1).sum();
        assert!(count > 0, "{:?}", plans[p]);
    }
}

/// **The expected capture reads every member at its weight** (`pursuit::ExpectedCapture`): on one
/// member it is that member's least capture (the capture basin on it alone), its own worst case,
/// or one uncaptured member past the horizon; on the opening's whole fibre it never captures more
/// members than their own leasts allow and never sums fewer ticks than their own leasts, and it
/// captures every member exactly when the capture basin certifies the fibre, its own worst case then
/// between the certificate and the horizon; on a pair of members (one constitution and navigator,
/// two slip holds) that the capture basin certifies within `b` ticks, it captures both, within `2b`
/// ticks in sum and no fewer than their own leasts, its worst case between `b` and the horizon.
#[test]
fn the_expected_capture_reads_every_member_at_its_weight() {
    let declaration = declaration();
    let family = family();
    let pursuer = pursuer();
    let caps = pursuer.law.caps(&declaration).unwrap();
    let disk = Moves::within(caps.top()).unwrap();
    let moves = family.moves(&declaration).unwrap();
    let depth = 5;
    let mut certified = 0;
    for seed in [20_261_001u64, 20_261_007, 20_261_014] {
        let (_, arena, openings) = Chase::drawn(&declaration, &family, seed).unwrap();
        let basin = Basin {
            arena: &arena,
            moves: &moves,
            pursuer: &pursuer,
            caps: &caps,
            disk: &disk,
        };
        let chaser = Motion::rest(openings[1]);
        let fibre = Candidate::opening(&family, &arena, openings[0]).unwrap();
        let (mut memo, mut expected_memo) = (BasinMemo::default(), ExpectedMemo::default());
        let mut own = Vec::new();
        for member in &fibre {
            let one = std::slice::from_ref(member);
            let least = basin
                .capture_ticks(&mut memo, chaser, 0, one, depth)
                .unwrap();
            let reading = basin
                .expected_ticks(&mut expected_memo, chaser, 0, one, depth)
                .unwrap();
            let alone = match least {
                Some(ticks) => ExpectedCapture {
                    uncaptured: 0,
                    ticks,
                    worst: ticks,
                },
                None => ExpectedCapture {
                    uncaptured: 1,
                    ticks: 0,
                    worst: 0,
                },
            };
            assert_eq!(reading, alone, "seed {seed}, member {}", member.index);
            own.push(least);
        }
        let whole = basin
            .expected_ticks(&mut expected_memo, chaser, 0, &fibre, depth)
            .unwrap();
        let beyond = own.iter().filter(|least| least.is_none()).count();
        assert!(whole.uncaptured >= beyond, "seed {seed}");
        if whole.uncaptured == beyond {
            let floor: usize = own.iter().flatten().sum();
            assert!(whole.ticks >= floor, "seed {seed}");
        }
        match basin
            .capture_ticks(&mut memo, chaser, 0, &fibre, depth)
            .unwrap()
        {
            Some(b) => {
                assert_eq!(whole.uncaptured, 0, "seed {seed}");
                assert!(b <= whole.worst && whole.worst <= depth, "seed {seed}");
            }
            None => assert!(whole.uncaptured > 0, "seed {seed}"),
        }
        // The hold is the third digit of the family's mixed radix (weight 2·2 = 4).
        for low in (0..fibre.len()).filter(|&i| (i / 4) % 2 == 0) {
            let pair = [fibre[low].clone(), fibre[low + 4].clone()];
            let reading = basin
                .expected_ticks(&mut expected_memo, chaser, 0, &pair, depth)
                .unwrap();
            if let Some(b) = basin
                .capture_ticks(&mut memo, chaser, 0, &pair, depth)
                .unwrap()
            {
                certified += 1;
                assert_eq!(reading.uncaptured, 0, "seed {seed}, pair {low}");
                assert!(reading.ticks <= 2 * b, "seed {seed}, pair {low}");
                assert!(
                    b <= reading.worst && reading.worst <= depth,
                    "seed {seed}, pair {low}"
                );
                let floor = own[low].unwrap() + own[low + 4].unwrap();
                assert!(reading.ticks >= floor, "seed {seed}, pair {low}");
            }
        }
    }
    assert!(certified > 0, "some pair is certified within the depth");
}

/// **The chaser's move set as a declared variant** (`pursuit::MoveSet`): on the lattice the chaser
/// has no pure boost from any velocity, and the half lattice has one; the half lattice holds the
/// doubled lattice motions; the runner reads a chaser at a grain by the plane's law (its cell
/// against `2X` at grain 2 is its cell against `X`); the truth-only least on the lattice is the
/// capture basin's on the truth alone, and a finer set's least is at most the coarser's.
#[test]
fn the_move_set_reads_capture_as_a_function_of_the_elementary_moves() {
    let declaration = declaration();
    let family = family();
    let pursuer = pursuer();
    let half = MoveSet {
        grain: 2,
        boosts: true,
        top: None,
    };
    let half_capped = MoveSet {
        top: Some(2),
        ..half
    };
    let unboosted = MoveSet {
        boosts: false,
        ..half
    };
    let grass = uniform(1);
    let boosts = |set: MoveSet, motion: Motion| {
        set.admitted(&pursuer, &grass, &motion)
            .unwrap()
            .iter()
            .filter(|next| {
                crate::geometry::motion::Move::new(motion.velocity, next.velocity).kind()
                    == crate::geometry::motion::MoveKind::Boost
            })
            .count()
    };
    for velocity in [[0, 0], [1, 0], [1, 1], [0, -1], [-1, 1]] {
        let motion = Motion {
            position: [8, 8],
            velocity,
        };
        assert_eq!(boosts(MoveSet::LATTICE, motion), 0, "{velocity:?}");
        let doubled = |m: &Motion| Motion {
            position: [2 * m.position[0], 2 * m.position[1]],
            velocity: [2 * m.velocity[0], 2 * m.velocity[1]],
        };
        let fine = half.admitted(&pursuer, &grass, &doubled(&motion)).unwrap();
        for coarse in MoveSet::LATTICE
            .admitted(&pursuer, &grass, &motion)
            .unwrap()
        {
            assert!(
                fine.contains(&doubled(&coarse)),
                "{velocity:?} → {coarse:?}"
            );
        }
    }
    let axis = Motion {
        position: [16, 16],
        velocity: [1, 0],
    };
    assert_eq!(boosts(half, axis), 2, "1/2 to 1 and to 3/2 along the axis");
    assert_eq!(boosts(unboosted, axis), 0);
    assert_eq!(boosts(half_capped, axis), 1, "1/2 to 1 below the top √2");
    let moves = family.moves(&declaration).unwrap();
    let caps = RunnerLaw {
        speed: rat(3, 1),
        traction: rat(1, 1),
    }
    .caps(&declaration)
    .unwrap();
    for runner in [
        fleeing(1),
        Runner {
            evasion: Evasion::ZigZag { period: 2 },
            ..fleeing(1)
        },
    ] {
        let state = RunnerState {
            motion: Motion {
                position: [5, 6],
                velocity: [1, -1],
            },
            ground: 1,
            held: 0,
        };
        for (chaser, tick) in [([2, 9], 0), ([9, 3], 1), ([5, 8], 3)] {
            let doubled = [2 * chaser[0], 2 * chaser[1]];
            assert_eq!(
                runner
                    .cell_at_grain(&grass, &moves, &caps, &state, doubled, 2, tick)
                    .unwrap(),
                runner
                    .cell(&grass, &moves, &caps, &state, chaser, tick)
                    .unwrap(),
                "{:?} against {chaser:?}",
                runner.evasion
            );
        }
    }
    let chaser_caps = pursuer.law.caps(&declaration).unwrap();
    let disk = Moves::within(chaser_caps.top()).unwrap();
    for seed in [20_261_001u64, 20_260_932] {
        let (index, arena, openings) = Chase::drawn(&declaration, &family, seed).unwrap();
        let runner = family.candidate(index).unwrap();
        let truth: Vec<Candidate> = Candidate::opening(&family, &arena, openings[0])
            .unwrap()
            .into_iter()
            .filter(|candidate| candidate.index == index)
            .collect();
        let basin = Basin {
            arena: &arena,
            moves: &moves,
            pursuer: &pursuer,
            caps: &chaser_caps,
            disk: &disk,
        };
        let limit = 8;
        let lattice = least_capture(
            &arena,
            &moves,
            &runner,
            openings,
            &pursuer,
            MoveSet::LATTICE,
            limit,
        )
        .unwrap();
        let reading = basin
            .capture_ticks(
                &mut BasinMemo::default(),
                Motion::rest(openings[1]),
                0,
                &truth,
                limit,
            )
            .unwrap();
        assert_eq!(lattice, reading, "seed {seed}");
        let lattice = lattice.expect("captured within the limit");
        // Each half set holds the doubled lattice (which has no pure boost), and the half lattice
        // holds both: every finer least is read within the lattice's.
        let [capped, unboosted, whole] = [half_capped, unboosted, half].map(|set| {
            least_capture(&arena, &moves, &runner, openings, &pursuer, set, lattice)
                .unwrap()
                .expect("a finer set captures within the lattice's least")
        });
        assert!(whole <= capped.min(unboosted), "seed {seed}");
    }
}

/// A chaser outside its traction bound is refused by name.
#[test]
fn a_chaser_outside_its_traction_bound_is_refused() {
    struct Leaper;
    impl Chaser for Leaper {
        type Error = TerrainError;
        fn label(&self) -> String {
            "leaper".to_string()
        }
        fn decide(&mut self, view: &ChaseView<'_>) -> Result<Motion, TerrainError> {
            Ok(Motion {
                position: [view.chaser.position[0] + 3, view.chaser.position[1]],
                velocity: [3, 0],
            })
        }
    }
    let action = ActionDeclaration {
        pursuer: pursuer(),
        ticks: 8,
        horizon: 2,
        switches: Switches::OFF,
    };
    let refused = act(
        uniform(2),
        &family(),
        0,
        [[12, 12], [2, 2]],
        &action,
        None,
        &mut Leaper,
    );
    assert!(matches!(refused, Err(TerrainError::Declaration { .. })));
}

/// **The controls' laws**: against a runner at `(8, 8)` moving `(0, 2)` across the line of sight
/// from a chaser at rest at `(4, 8)`, pure pursuit steps to `(5, 8)`, nearest the runner's present
/// position; constant bearing takes velocity `(1, 1)`: approaching (`⟨r, ṙ⟩ = −4`), the least
/// `|det(r, ṙ)| = 4`, the most closing, `⟨r + ṙ, r + ṙ⟩ = 10`. Against a runner at rest, resting
/// nulls the rotation but does not approach, and constant bearing closes along the line of sight.
#[test]
fn the_controls_head_at_the_runner_and_null_the_bearing_rate() {
    let ports = std::sync::Arc::new(ChasePorts {
        arena: uniform(2),
        moves: family().moves(&declaration()).unwrap(),
        chaser: ChaserPort::default(),
        opening: Motion::rest([8, 8]),
        lag: 0,
    });
    let pursuer = pursuer();
    let view = ChaseView {
        ports: &ports,
        pursuer: &pursuer,
        runner: Motion {
            position: [8, 8],
            velocity: [0, 2],
        },
        chaser: Motion::rest([4, 8]),
        tick: 0,
    };
    let pure = PurePursuit.decide(&view).unwrap();
    assert_eq!(
        pure,
        Motion {
            position: [5, 8],
            velocity: [1, 0]
        }
    );
    let bearing = ConstantBearing.decide(&view).unwrap();
    assert_eq!(
        bearing,
        Motion {
            position: [5, 9],
            velocity: [1, 1]
        }
    );
    assert_eq!(
        ConstantBearing::key(&view.runner, &view.chaser, &bearing),
        (false, 4, 10)
    );
    assert_eq!(det([4, 0], [0, 1]), 4);
    let resting = ChaseView {
        runner: Motion::rest([8, 8]),
        ..view
    };
    assert_eq!(
        ConstantBearing.decide(&resting).unwrap(),
        Motion {
            position: [5, 8],
            velocity: [1, 0]
        }
    );
}
