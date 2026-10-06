//! **The move pair `(v, v′)`: a mover's velocity before and after a tick, carried undivided, with
//! its change, its kind, its traction disk, its power and its signed turn** (THE_REBUILD U4; the
//! objects' [Swing](../../../../docs/ELEMENTARY_OBJECTS.md#the-swing); the motion record
//! `2026-09-28_THE_SWING_IS_A_MOVE_ABOUT_A_GRIP_…`, §3 and §7; Lean `Geometry/Motion`).
//!
//! [definition; agent-inferred] **The carrier: the Gaussian integers `ℤ[i]`** ([`Point`]), the
//! lattice of the field `ℚ(i)` ([`GaussianRat`](crate::ratio::GaussianRat)) that a lattice mover's
//! positions and velocities occupy (steps, and steps a tick). Its operations are the field's
//! restricted to the lattice, and the tests check each against `GaussianRat`: [`add`], [`sub`],
//! [`scale`] by an integer, the quadrance [`quadrance`] `|p|² = p̄p` (`norm_sq`), the quarter-turn
//! [`quarter_turn`] `ip` (`J(a, b) = (−b, a)`, `J² = −1`), and the Hermitian pairing `āb`, whose
//! real face is [`dot`] `⟨a, b⟩` and whose imaginary face is [`det`] `det(a, b)`. They stay machine
//! words, not `GaussianRat`'s big rationals, because the chase's viable tube and capture basin
//! read them for every runner motion of every decision; within [`LATTICE_REACH`] no difference,
//! quadrance or pairing leaves a word, so the arithmetic is exact.
//!
//! [proved-derived; formal-checked] **The move pair.** A move is its opening velocity `v` and its
//! next velocity `v′`, carried together ([`Move`]) and never as the ratio `k = v′/v`: an opening
//! velocity is zero, a stop gives `k = 0`, and a held slip `k = 1`, so the ratio's chart fails
//! exactly where a chase needs its cases (the record's §7). Where `v ≠ 0` the pair reads through `k`
//! by these identities, and every reading below is decided without dividing:
//!
//! ```text
//! v̄·(v′ − v) = |v|²(k − 1)             Re: power_is_boost_rate, Im: normal_effort_is_turn_rate (w = k − 1)
//! |v′ − v|² = |k − 1|²·|v|²             traction_move_ratio, traction_disk
//! |v′|² − |v|² = 2⟨v, Δv⟩ + |Δv|²      Physics/ReleasedMotion.releasedVelocity_kinetic_work_increment (m = 1)
//! ```
//!
//! - **The change** `Δv = v′ − v` ([`Move::change`]), the impulse of a unit mass.
//! - **The power** `Re(v̄·Δv) = ⟨v, Δv⟩` and **the signed turn** `Im(v̄·Δv) = det(v, Δv) = det(v, v′)`
//!   ([`Move::power`], [`Move::turn`]): the effort along the motion boosts and the effort across it
//!   turns (Lean `Geometry/Motion.power_is_boost_rate`, `normal_effort_is_turn_rate`); the turn is
//!   positive counterclockwise.
//! - **The kind** ([`Move::kind`], [`MoveKind`]), exact on the integers, with its reading on `k`
//!   where `v ≠ 0` (the record's §3.4, the complex chart: a turn if `|k| = 1`, a scalar dilation if
//!   `k > 0`, both otherwise, free fall at `k = 1`):
//!
//! | Kind | The pair | The ratio `k = v′/v` |
//! |---|---|---|
//! | [`MoveKind::Rest`] | `v = v′ = 0` | none |
//! | [`MoveKind::Start`] | `v = 0 ≠ v′` | none: no ratio and no pivot |
//! | [`MoveKind::Stop`] | `v ≠ 0 = v′` | `k = 0`, not a move of the plane |
//! | [`MoveKind::FreeFall`] | `v′ = v ≠ 0`: inertia alone | `k = 1` |
//! | [`MoveKind::Turn`] | `2⟨v, Δv⟩ + ⟨Δv, Δv⟩ = 0`, `Δv ≠ 0` | `k̄k = 1`, `k ≠ 1` (the half-turn `k = −1` among them) |
//! | [`MoveKind::Boost`] | `det(v, Δv) = 0`, `⟨v, v′⟩ > 0`, not a turn | `k > 0` real, `k ≠ 1` |
//! | [`MoveKind::TurnAndBoost`] | otherwise | otherwise (a negative real `k ≠ −1` is a half-turn with a boost) |
//!
//! - **The traction disk** `|v′ − v|² ≤ r²` ([`Move::within_bound`], read in ℚ; [`Move::within_cap`]
//!   on the lattice, where an integer quadrance meets a rational bound `r² ≥ 0` exactly when it meets
//!   `⌊r²⌋`, an identity, not a rounding). It is a disk about `v` in the velocity plane and, where
//!   `v ≠ 0`, the disk `|k − 1|²|v|² ≤ r²` about `1` in the ratio's plane, which shrinks as the speed
//!   grows (Lean `traction_disk`). It reads the change alone, so a change of inertial frame
//!   `(v, v′) ↦ (v + u, v′ + u)` moves no admission.
//!
//! [definition; agent-inferred] **The pivot is not built.** A move with `v ≠ 0 ≠ v′ ≠ v` carries the
//! spiral similarity turning the step `v` onto the step `v′`, about the pivot `x + vv′/(v − v′)`
//! with `x` the position between the two steps (Lean `complex_move_about_pivot` at `k = v′/v`); no
//! consumer reads it here, and the kind and the traction disk need no division, so it waits for its
//! consumer.
//!
//! | Lean `Geometry/Motion` (unless named) | Rust |
//! |---|---|
//! | `power_is_boost_rate`, `normal_effort_is_turn_rate`, `rates_from_effort` | [`Move::power`], [`Move::turn`], [`dot`], [`det`] |
//! | `traction_move_ratio`, `traction_disk` | [`Move::within_bound`], [`Move::within_cap`] |
//! | `turn_distance_from_one`, `complex_fall_has_no_pivot`; the record's §3.4 (the complex chart's kinds) | [`Move::kind`], [`MoveKind`] |
//! | `Physics/ReleasedMotion.releasedVelocity_kinetic_work_increment` | [`MoveKind::Turn`]'s test |
//!
//! [definition] The computational object is the helical pair interaction: a mover's move pair is the
//! contact's relative motion across one tick, and a chase reads two movers (the runner and the
//! chaser) through it. Of the winding guide's six general objects this owner touches the **pair**
//! (the move's change, power and signed turn: the relative motion that the traction contact admits
//! or slips) and **faces and placement** (the move's kind read exactly at the lattice); the helix,
//! the cell holonomy, the tube and the tower thread stay attached through its consumers
//! (`holarchy::terrain::{chase, pursuit}`).

use num_bigint::BigInt;

use crate::ratio::Rat;

/// [definition] **A point of the Gaussian integer lattice** `x + iy ∈ ℤ[i]`, as `[x, y]`: a lattice
/// position, displacement or velocity.
pub type Point = [i64; 2];

/// [definition; agent-inferred] **The lattice's declared reach**: every component of a point this
/// owner reads lies below `2^30` in magnitude. A difference then lies below `2^31` a component, its
/// quadrance below `2·2^62 = 2^63`, and every pairing below `2^62`, so no reading leaves a machine
/// word. The chase's arena (`holarchy::terrain::chase::ARENA_SIDE_LIMIT`, `2^15`) lies far inside.
pub const LATTICE_REACH: i64 = 1 << 30;

/// Whether a point lies within [`LATTICE_REACH`].
fn within_reach(p: Point) -> bool {
    p.iter().all(|c| c.abs() < LATTICE_REACH)
}

/// `a + b` in `ℤ[i]`.
pub fn add(a: Point, b: Point) -> Point {
    [a[0] + b[0], a[1] + b[1]]
}

/// `a − b` in `ℤ[i]`.
pub fn sub(a: Point, b: Point) -> Point {
    [a[0] - b[0], a[1] - b[1]]
}

/// `k·p`, an integer multiple.
pub fn scale(k: i64, p: Point) -> Point {
    [k * p[0], k * p[1]]
}

/// **The quadrance** `|p|² = p̄p = ⟨p, p⟩` (Lean's `Complex.normSq`).
pub fn quadrance(p: Point) -> i64 {
    p[0] * p[0] + p[1] * p[1]
}

/// **The oriented quarter-turn** `ip`: `J(a, b) = (−b, a)`, `J² = −1`, the square root of the
/// half-turn.
pub fn quarter_turn(p: Point) -> Point {
    [-p[1], p[0]]
}

/// **The real face of the pairing** `Re(āb) = ⟨a, b⟩`: `b`'s component along `a`, times `|a|`.
pub fn dot(a: Point, b: Point) -> i64 {
    a[0] * b[0] + a[1] * b[1]
}

/// **The imaginary face of the pairing** `Im(āb) = det(a, b) = a_x b_y − a_y b_x`: twice the
/// oriented area, `b`'s component across `a`, times `|a|`; positive counterclockwise.
pub fn det(a: Point, b: Point) -> i64 {
    a[0] * b[1] - a[1] * b[0]
}

/// [definition] **A move** (module header): the opening velocity `v = before` and the next velocity
/// `v′ = after`, carried undivided.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Move {
    pub before: Point,
    pub after: Point,
}

/// [definition] **A move's kind** (module header's table).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum MoveKind {
    /// `v = v′ = 0`.
    Rest,
    /// `v = 0 ≠ v′`: a start from rest.
    Start,
    /// `v ≠ 0 = v′`: a stop to rest.
    Stop,
    /// `v′ = v ≠ 0`: inertia alone.
    FreeFall,
    /// `|v′| = |v|`, `v′ ≠ v`, both nonzero: a pure turn.
    Turn,
    /// `v′ = s·v`, `s > 0`, `s ≠ 1`: a pure boost.
    Boost,
    /// Every other move of two nonzero velocities: a turn and a boost.
    TurnAndBoost,
}

impl MoveKind {
    /// The kinds, in their declared order.
    pub const ALL: [MoveKind; 7] = [
        MoveKind::Rest,
        MoveKind::Start,
        MoveKind::Stop,
        MoveKind::FreeFall,
        MoveKind::Turn,
        MoveKind::Boost,
        MoveKind::TurnAndBoost,
    ];

    pub fn label(&self) -> &'static str {
        match self {
            MoveKind::Rest => "rest",
            MoveKind::Start => "start",
            MoveKind::Stop => "stop",
            MoveKind::FreeFall => "free fall",
            MoveKind::Turn => "turn",
            MoveKind::Boost => "boost",
            MoveKind::TurnAndBoost => "turn and boost",
        }
    }
}

impl Move {
    /// The move `(v, v′)`; both velocities lie within [`LATTICE_REACH`].
    pub fn new(before: Point, after: Point) -> Self {
        debug_assert!(
            within_reach(before) && within_reach(after),
            "a move within the lattice's declared reach"
        );
        Self { before, after }
    }

    /// **The move of a change** `(v, v + Δv)`.
    pub fn by_change(before: Point, change: Point) -> Self {
        Self::new(before, add(before, change))
    }

    /// **The held move** `(v, v)`: inertia alone, the move a held slip realizes (free fall, or rest
    /// when `v = 0`).
    pub fn held(velocity: Point) -> Self {
        Self::new(velocity, velocity)
    }

    /// **The change** `Δv = v′ − v`.
    pub fn change(&self) -> Point {
        sub(self.after, self.before)
    }

    /// **The power** `Re(v̄·Δv) = ⟨v, Δv⟩` at the opening velocity (Lean `power_is_boost_rate`):
    /// positive where the move pushes along the motion, negative where it brakes, zero from rest.
    /// The move's whole work per unit mass is `⟨v, Δv⟩ + ½⟨Δv, Δv⟩`
    /// (`Physics/ReleasedMotion.releasedVelocity_kinetic_work_increment`).
    pub fn power(&self) -> i64 {
        dot(self.before, self.change())
    }

    /// **The signed turn** `Im(v̄·Δv) = det(v, Δv) = det(v, v′)` (Lean `normal_effort_is_turn_rate`):
    /// positive counterclockwise, zero exactly when `v′` lies on the line of `v`.
    pub fn turn(&self) -> i64 {
        det(self.before, self.change())
    }

    /// **The traction disk on the lattice**: `|v′ − v|² ≤ cap`, where `cap = ⌊r²⌋` of a rational
    /// bound `r² ≥ 0` (an integer quadrance meets `r²` exactly when it meets its floor).
    pub fn within_cap(&self, cap: i64) -> bool {
        quadrance(self.change()) <= cap
    }

    /// **The traction disk in ℚ**: `|v′ − v|² ≤ r²` (Lean `traction_disk`).
    pub fn within_bound(&self, bound: &Rat) -> bool {
        Rat::from_integer(BigInt::from(quadrance(self.change()))) <= *bound
    }

    /// **The move's kind** (module header's table), decided on the integers without division.
    pub fn kind(&self) -> MoveKind {
        let (v, w) = (self.before, self.after);
        let zero = [0, 0];
        match (v == zero, w == zero) {
            (true, true) => MoveKind::Rest,
            (true, false) => MoveKind::Start,
            (false, true) => MoveKind::Stop,
            (false, false) if v == w => MoveKind::FreeFall,
            (false, false) => {
                let power = self.power();
                // |v′|² − |v|² = 2⟨v, Δv⟩ + |Δv|²: the speed held.
                if 2 * power + quadrance(self.change()) == 0 {
                    MoveKind::Turn
                // v′ on the line of v, on its side: ⟨v, v′⟩ = ⟨v, v⟩ + ⟨v, Δv⟩ > 0.
                } else if self.turn() == 0 && quadrance(v) + power > 0 {
                    MoveKind::Boost
                } else {
                    MoveKind::TurnAndBoost
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use num_traits::Signed;

    use super::*;
    use crate::ratio::{GaussianRat, integer, rat};

    /// The embedding `ℤ[i] → ℚ(i)`.
    fn gaussian(p: Point) -> GaussianRat {
        GaussianRat::from_i64(p[0], p[1])
    }

    /// The smallest square of lattice velocities, `[−2, 2]²`.
    fn square() -> Vec<Point> {
        (-2..=2)
            .flat_map(|x| (-2..=2).map(move |y| [x, y]))
            .collect()
    }

    /// The lattice operations are `ℚ(i)`'s restricted to `ℤ[i]`: sum, difference, integer multiple,
    /// quadrance `p̄p`, quarter-turn `ip` and the pairing `āb = ⟨a, b⟩ + i·det(a, b)`.
    #[test]
    fn the_lattice_operations_are_the_gaussian_fields() {
        for &a in &square() {
            let (ga, i) = (gaussian(a), GaussianRat::i());
            assert_eq!(gaussian([quadrance(a), 0]), ga.conj().mul(&ga));
            assert_eq!(gaussian(quarter_turn(a)), i.mul(&ga));
            assert_eq!(quarter_turn(quarter_turn(a)), scale(-1, a));
            assert_eq!(gaussian(scale(3, a)), ga.scale(&integer(3)));
            for &b in &square() {
                let gb = gaussian(b);
                assert_eq!(gaussian(add(a, b)), ga.add(&gb));
                assert_eq!(gaussian(sub(a, b)), ga.sub(&gb));
                assert_eq!(gaussian([dot(a, b), det(a, b)]), ga.conj().mul(&gb));
            }
        }
    }

    /// The change is `v′ − v`, a move of a change returns it, and the held move changes nothing.
    #[test]
    fn a_move_carries_its_change() {
        let m = Move::new([1, 2], [-1, 3]);
        assert_eq!(m.change(), [-2, 1]);
        assert_eq!(Move::by_change([1, 2], [-2, 1]), m);
        assert_eq!(Move::held([1, 2]).change(), [0, 0]);
        assert_eq!(Move::held([1, 2]), Move::new([1, 2], [1, 2]));
    }

    /// Each kind on its smallest fixture: rest, a start and a stop (no division at the zero
    /// velocity), free fall, a quarter-turn and the half-turn (turns), a doubling (a boost), and a
    /// negative doubling and a quarter-turn with a push (turn and boost).
    #[test]
    fn each_kind_on_its_smallest_fixture() {
        let cases = [
            ([0, 0], [0, 0], MoveKind::Rest),
            ([0, 0], [1, 0], MoveKind::Start),
            ([1, 0], [0, 0], MoveKind::Stop),
            ([1, 0], [1, 0], MoveKind::FreeFall),
            ([1, 0], [0, 1], MoveKind::Turn),
            ([1, 0], [-1, 0], MoveKind::Turn),
            ([2, 1], [1, -2], MoveKind::Turn),
            ([1, 1], [2, 2], MoveKind::Boost),
            ([2, 0], [1, 0], MoveKind::Boost),
            ([1, 0], [-2, 0], MoveKind::TurnAndBoost),
            ([1, 0], [0, 2], MoveKind::TurnAndBoost),
        ];
        for (v, w, kind) in cases {
            assert_eq!(Move::new(v, w).kind(), kind, "({v:?}, {w:?})");
        }
        assert_eq!(
            Move::new([3, 1], quarter_turn([3, 1])).kind(),
            MoveKind::Turn
        );
    }

    /// Lean `traction_move_ratio`, `turn_distance_from_one` and the complex chart's kinds (the
    /// record's §3.4): where `v ≠ 0`, with `k = v′/v` in `ℚ(i)`, the kind read on the integers is
    /// the kind read on `k` (free fall at `k = 1`, a stop at `k = 0`, a turn at `|k|² = 1`, a boost
    /// at `k` real and positive), `|v′ − v|² = |k − 1|²|v|²`, a turn has `|k − 1|² = 2 − 2 Re k`;
    /// at `v = 0` the kind is rest or a start and no ratio is formed. Every pair of `[−2, 2]²`.
    #[test]
    fn the_kind_is_the_move_ratios_kind() {
        let one = GaussianRat::one();
        for &v in &square() {
            for &w in &square() {
                let m = Move::new(v, w);
                let kind = m.kind();
                if v == [0, 0] {
                    assert!(matches!(kind, MoveKind::Rest | MoveKind::Start));
                    assert_eq!(kind == MoveKind::Rest, w == [0, 0]);
                    continue;
                }
                let (gv, gw) = (gaussian(v), gaussian(w));
                let k = gw.div(&gv).unwrap();
                let from_one = k.sub(&one);
                assert_eq!(
                    gaussian(m.change()).norm_sq(),
                    from_one.norm_sq() * gv.norm_sq()
                );
                let expected = if k.is_zero() {
                    MoveKind::Stop
                } else if k == one {
                    MoveKind::FreeFall
                } else if k.norm_sq() == integer(1) {
                    assert_eq!(from_one.norm_sq(), integer(2) - integer(2) * &k.re);
                    MoveKind::Turn
                } else if k.is_real() && k.re.is_positive() {
                    MoveKind::Boost
                } else {
                    MoveKind::TurnAndBoost
                };
                assert_eq!(kind, expected, "({v:?}, {w:?})");
            }
        }
    }

    /// Lean `power_is_boost_rate`, `normal_effort_is_turn_rate` at `w = k − 1` (`Δv = v·w`): the
    /// power and the signed turn are `v̄·Δv`'s faces, `|v|² Re(k − 1)` and `|v|² Im k`; and Lean
    /// `releasedVelocity_kinetic_work_increment` at unit mass, `|v′|² − |v|² = 2⟨v, Δv⟩ + |Δv|²`.
    /// A quarter-turn counterclockwise turns positively and does no work.
    #[test]
    fn the_power_and_the_signed_turn_are_the_pairings_faces() {
        for &v in &square() {
            for &w in &square() {
                let m = Move::new(v, w);
                let (gv, gd) = (gaussian(v), gaussian(m.change()));
                assert_eq!(gaussian([m.power(), m.turn()]), gv.conj().mul(&gd));
                assert_eq!(m.turn(), det(v, w));
                assert_eq!(
                    quadrance(w) - quadrance(v),
                    2 * m.power() + quadrance(m.change())
                );
                if v != [0, 0] {
                    let k = gaussian(w).div(&gv).unwrap();
                    let norm = gv.norm_sq();
                    assert_eq!(integer(m.power()), &norm * (&k.re - integer(1)));
                    assert_eq!(integer(m.turn()), &norm * &k.im);
                }
            }
        }
        let quarter = Move::new([2, 0], [0, 2]);
        assert!(quarter.turn() > 0);
        assert_eq!(Move::new([2, 0], [0, -2]).turn(), -quarter.turn());
        assert_eq!(quadrance(quarter.after) - quadrance(quarter.before), 0);
        assert!(Move::new([1, 0], [2, 0]).power() > 0);
        assert!(Move::new([2, 0], [1, 0]).power() < 0);
    }

    /// Lean `traction_disk`: the disk read in ℚ and on the lattice at the bound's floor agree on
    /// every move of `[−2, 2]²` for the bounds `0, 1, 9/4, 81/4`; the quarter-turn of a unit
    /// velocity has `|Δv|² = 2`, inside `9/4` and outside `1`; the disk is unchanged by a change of
    /// inertial frame `(v, v′) ↦ (v + u, v′ + u)`.
    #[test]
    fn the_traction_disk_is_exact_and_frame_independent() {
        let bounds = [rat(0, 1), rat(1, 1), rat(9, 4), rat(81, 4)];
        for bound in &bounds {
            let cap = bound.floor().to_integer().try_into().unwrap();
            for &v in &square() {
                for &w in &square() {
                    let m = Move::new(v, w);
                    assert_eq!(m.within_bound(bound), m.within_cap(cap));
                    for u in [[1, 0], [-2, 3]] {
                        let framed = Move::new(add(v, u), add(w, u));
                        assert_eq!(framed.within_bound(bound), m.within_bound(bound));
                    }
                }
            }
        }
        let quarter = Move::new([1, 0], [0, 1]);
        assert!(quarter.within_bound(&rat(9, 4)));
        assert!(!quarter.within_bound(&rat(1, 1)));
        assert!(Move::held([2, 1]).within_cap(0));
    }
}
