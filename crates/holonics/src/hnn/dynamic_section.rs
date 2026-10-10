//! **The dynamic section: the signed crossing of a ring's own state through its section rays, with
//! the lift carried** (second rung of the acoustic line; the
//! [record](../../../../research/records/2026-10-09_A_MATCHED_WAVE_ENTERS_A_LOADED_RING_AND_ITS_STATE_CROSSES_ITS_OWN_SECTION.md);
//! #148, #73, #386).
//!
//! [definition; agent-inferred, October 9] A ring's mode is a resonator at its port
//! ([`crate::hnn::ring`]); its phase point is `z = (w, u)` in the plane of its velocity-like state
//! `w` and its displacement `u`, so that free motion turns counterclockwise. The plane carries the
//! four **quarter-turn rays** (the positive `u = 0` axis `w > 0`, then each quarter turn on). A ray
//! belongs to the class it starts, so the **class** of a point is its quadrant,
//!
//! ```text
//! class 0:  w > 0,  u ≥ 0        class 1:  w ≤ 0,  u > 0
//! class 2:  w < 0,  u ≤ 0        class 3:  w ≥ 0,  u < 0          (the origin has no class)
//! ```
//!
//! and the **lift** `ℓ` carries the class with the winding, helix = circle + carry
//! ([`WINDING_CARRY_AND_PLACEMENT`](../../../../docs/WINDING_CARRY_AND_PLACEMENT.md) §1):
//! `ℓ mod 4` is the class and `⌊ℓ/4⌋` the whole winding, the carry `ℤ/4` is not `ℤ/2 × ℤ/2`. Between
//! consecutive states `p → q` the straight chord turns the point about the origin by an angle in
//! `(−π, π)`, and the lift advances by the number of rays it passes, signed:
//!
//! ```text
//! cross(p, q) > 0 :  Δℓ = (cls q − cls p) mod 4     ∈ {0, 1, 2}
//! cross(p, q) < 0 :  Δℓ = −((cls p − cls q) mod 4)  ∈ {0, −1, −2}
//! cross(p, q) = 0 :  Δℓ = 0 when dot(p, q) > 0;  a chord through the origin (dot < 0) is refused
//! ℓ_(k+1) = ℓ_k + Δℓ(z_k, z_(k+1))
//! ```
//!
//! The **symbol** of a tick is `(cls z_k, Δℓ_k)`. A **section arrival** is a tick at which the
//! whole winding `⌊ℓ/4⌋` changes (the ring's displacement crossing zero upward at `w > 0`); its sign
//! is the signed crossing `⌊(ℓ+Δℓ)/4⌋ − ⌊ℓ/4⌋ ∈ {−1, 0, 1}`, which is also the flux of the aeon's
//! ring section ([`crate::aeon::ClockLift::ring_section`], [`crate::aeon::epochs`]) over the lift's
//! micro-steps. The lift is read as the aeon's own reading type: [`SectionReader::reading`] is
//! `ℓ/4` turns, whole windings and open phase ([`crate::aeon::Reading`]). The reader keeps the
//! observed arrival placement, phase, lift and residual; it keeps no rate. A mean rate `W/τ` over
//! a cycle is a cycle face (`aeon::TwoClocks`), and the arrival word of a ring need not be a
//! constant-rate (balanced) word: the unbalanced word is a reading the face does not hold
//! (Lean `Aeon/Clock/CarryWord.carry_balanced` is the balanced law).
//!
//! [proved-derived] **Polarity is the half-turn.** The state of `−x` is minus the state of `x` for a
//! linear ring, `cls(−z) = cls(z) + 2 (mod 4)` and `Δℓ(−p, −q) = Δℓ(p, q)`, so every symbol goes
//! to `(cls + 2, Δℓ)` and the lifts differ by the constant `2` ([`SectionReader::half_turn`]): the
//! polarity of a wave is the dyad's `U`, an involution without fixed points on the classes.
//!
//! [definition] **What it is not.** It is not `holon::parametron::ring_crossings`, the odometer
//! count of a ring's rotor section at integer ticks (a declared rate), and it is not
//! [`crate::hnn::ring::sheets`], the half-plane side of the pump axis, which is blind to the
//! half-turn by construction. The reader sees the ring's actual state, whose sub-tick position of
//! a crossing is the unresolved fibre below the tick. It is modality-free: it takes any point of a
//! plane (a ring's `(w, u)`, a pendulum's, a joint's) and no codec.
//!
//! [definition; hypotheses] Each tick turns the state by less than half a turn (the straight chord
//! is the shorter way round; an exact half-turn is refused, a larger turn aliases and is not
//! detected); the quarter-turn grain is the only finite-order rational rotation of the plane (the
//! pump's steps are the same four, `ring::PumpStep`), so the rays are exact and read by signs.
//! The state is the origin only at rest: a reader starts on a settled, nonzero state.
//!
//! The computational object is the helical pair interaction. Of the winding guide's six general
//! objects this owner touches the **helix** (class plus carry), **faces and placement** (the
//! arrival is the placement of the section crossing) and **cell holonomy** (the phase `ℓ mod 4`
//! carried across epochs). The pair, the tube and the tower thread stay attached: the lock address
//! of a ring against another is the pair contact's, read from this owner's arrival word by the
//! owed lock reader, and the port the state lives at is the tube's boundary (`hnn::wave`).
//!
//! [proved-derived] **The tick's carry is the owner's, stated once** ([`land`]). The crossing of a tick
//! is the difference of whole windings of the lift, and the signed carry law gives it from the phases
//! alone: with `ℓ/4` and `Δℓ/4` as aeon readings, `windings(ℓ/4 + Δℓ/4) = windings(ℓ/4) +
//! windings(Δℓ/4) + carry(ℓ/4, Δℓ/4)` (Lean `Aeon/Clock/Winding.windings_add`), so
//!
//! ```text
//! crossing_k = ⌊(ℓ_k + Δℓ_k)/4⌋ − ⌊ℓ_k/4⌋ = windings(Δℓ_k/4) + carry(cls_k/4, Δℓ_k/4)    ∈ {−1, 0, 1}
//! cls_(k+1)  = 4 · openPhase(ℓ_k/4 + Δℓ_k/4)
//! ```
//!
//! A departure back across the section is the negative `windings(Δℓ/4)` less the carry; the carry
//! depends on the class `ℓ mod 4` and not on the winding. [`land`] calls [`Reading::add`] (which calls
//! `geometry::winding::carry`) and is the only statement of this law: [`SectionReader::advance`]
//! emits its symbol from it and `section_lock::SectionWord::new` admits a word against it. The chord
//! `Δℓ` itself is [`chord`]'s, and the lift's own step `ℓ + Δℓ` is the integer addition of a lift.
//!
//! | Law | Lean | Rust |
//! |---|---|---|
//! | the lift is class plus carry, `winding(x + y) = winding x + winding y + carry`: the tick's crossing and landing class from the signed carry law | `Geometry/PhaseCarry.winding_add`; `Aeon/Clock/Winding.windings_add`, `carry_le_one` | [`land`] calls [`Reading::add`] (owner `aeon::reading`, over `geometry::winding::carry`); consumed by [`SectionReader::advance`], read by [`SectionReader::reading`] |
//! | the signed crossing of the aeon's ring section is the difference of whole windings | `Aeon/Clock/Epoch.signed_count_is_flux` | [`SectionSymbol::crossing`] read by `aeon::epochs` |
//! | the chord's advance, the polarity `ℓ(−z) = ℓ(z) + 2` | owed (#62) | [`chord`], [`SectionReader::half_turn`] |

use num_bigint::BigInt;
use num_traits::Zero;
use std::cmp::Ordering;
use thiserror::Error;

use crate::aeon::Reading;
use crate::ratio::Rat;

/// The declared grain: the four quarter-turn rays (module header).
pub const RAYS: u8 = 4;

/// [definition] **Why a point or a chord has no symbol.** Typed; a symbol is never invented.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum SectionRefusal {
    /// The point is the origin, which lies on every ray and has no class (a ring at rest).
    #[error("the state is the origin: it lies on every ray and has no class")]
    AtOrigin,
    /// The chord passes through the origin: the swept angle is exactly a half turn, with no sense.
    #[error("the chord passes through the origin: it sweeps exactly half a turn, in no sense")]
    ThroughOrigin,
    /// Unreachable for a straight chord between two classed points; returned rather than assumed.
    #[error("the chord from class {from} to class {to} turns the class by more than a half turn")]
    Inconsistent { from: u8, to: u8 },
    /// Unreachable: the crossing or the landing class of the owner's carry leaves the symbol's carrier
    /// (`i8`, `u8`). The carry is one turn or none (`carry_le_one`) and `Δℓ` is a quarter-turn count,
    /// so the crossing is at most one more than the quarter turns of `Δℓ` and the landing class is
    /// below four; returned rather than assumed.
    #[error("the tick from class {class} by {advance} rays leaves the carrier of a section symbol")]
    Carrier { class: u8, advance: i8 },
}

/// [definition] **The quadrant class of a point** `(w, u)`: each ray belongs to the class it starts
/// (module header); `None` at the origin.
pub fn quadrant(point: &[Rat; 2]) -> Option<u8> {
    let zero = Rat::zero();
    match (point[0].cmp(&zero), point[1].cmp(&zero)) {
        (Ordering::Greater, Ordering::Greater | Ordering::Equal) => Some(0),
        (Ordering::Less | Ordering::Equal, Ordering::Greater) => Some(1),
        (Ordering::Less, Ordering::Less | Ordering::Equal) => Some(2),
        (Ordering::Greater | Ordering::Equal, Ordering::Less) => Some(3),
        (Ordering::Equal, Ordering::Equal) => None,
    }
}

/// [definition] **The advance of the lift along a straight chord** `p → q`, `Δℓ ∈ {−2, …, 2}`
/// (module header). Refused at the origin and through it.
pub fn chord(p: &[Rat; 2], q: &[Rat; 2]) -> Result<i8, SectionRefusal> {
    let (from, to) = match (quadrant(p), quadrant(q)) {
        (Some(from), Some(to)) => (from, to),
        _ => return Err(SectionRefusal::AtOrigin),
    };
    let cross = &p[0] * &q[1] - &p[1] * &q[0];
    let turn = |behind: u8, ahead: u8| (ahead + RAYS - behind) % RAYS;
    match cross.cmp(&Rat::zero()) {
        Ordering::Greater => match turn(from, to) {
            advance @ 0..=2 => Ok(advance as i8),
            _ => Err(SectionRefusal::Inconsistent { from, to }),
        },
        Ordering::Less => match turn(to, from) {
            advance @ 0..=2 => Ok(-(advance as i8)),
            _ => Err(SectionRefusal::Inconsistent { from, to }),
        },
        Ordering::Equal => {
            let along = &p[0] * &q[0] + &p[1] * &q[1];
            if along > Rat::zero() {
                // The same direction is the same class: no ray is passed.
                Ok(0)
            } else {
                Err(SectionRefusal::ThroughOrigin)
            }
        }
    }
}

/// [proved-derived] **The landing of one tick, by the owner's signed carry law** (module header): the
/// tick leaves `class` and advances the lift by `advance` rays. It returns the signed crossing
/// `⌊(class + advance)/4⌋ − ⌊class/4⌋` (`+1` an arrival at the section, `−1` a departure back across
/// it) and the class it lands on, `(class + advance) mod 4`.
///
/// Both are read from the aeon's reading of the lift, `Reading::of_turns(class/4)` carried by
/// `Reading::add` with `Reading::of_turns(advance/4)`: the crossing is the added whole windings
/// (`windings(advance/4)`, negative for a backward tick, plus the carry of the open phases) and the
/// landing class is four times the sum's open phase. No hand comparison of `class + advance` with
/// `0` and `4` stands beside the owner (Lean `Aeon/Clock/Winding.windings_add`, `openPhase_add`).
///
/// Cost: three exact rational readings and one carry, independent of the lift's winding.
pub fn land(class: u8, advance: i8) -> Result<(i8, u8), SectionRefusal> {
    let turns = |rays: i64| Reading::of_turns(&Rat::new(BigInt::from(rays), BigInt::from(RAYS)));
    let behind = turns(i64::from(class));
    let ahead = behind.add(&turns(i64::from(advance)));
    let carrier = || SectionRefusal::Carrier { class, advance };
    let crossing = i8::try_from(ahead.windings() - behind.windings()).map_err(|_| carrier())?;
    let landed = u8::try_from((ahead.phase() * Rat::from_integer(BigInt::from(RAYS))).to_integer())
        .map_err(|_| carrier())?;
    Ok((crossing, landed))
}

/// [definition] **One tick's symbol**: the class the tick leaves, the signed advance of the lift,
/// and the signed crossing of the aeon's ring section (the change of the whole winding).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SectionSymbol {
    /// The class of the state the tick starts from.
    pub class: u8,
    /// `Δℓ`, the signed number of rays the tick passes.
    pub advance: i8,
    /// `⌊(ℓ + Δℓ)/4⌋ − ⌊ℓ/4⌋`: `+1` an arrival at the section, `−1` a departure back across it.
    pub crossing: i8,
}

/// [definition] **The reader of a dynamic section**: the last state and the lift, the quotient the
/// next tick needs (retention: no tape of the states it has read). Atomic: a refused tick leaves
/// it as it was.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SectionReader {
    point: [Rat; 2],
    class: u8,
    lift: BigInt,
}

impl SectionReader {
    /// A reader started on a classed state, its lift at the class (winding zero).
    pub fn at(point: [Rat; 2]) -> Result<Self, SectionRefusal> {
        let class = quadrant(&point).ok_or(SectionRefusal::AtOrigin)?;
        Ok(Self {
            point,
            class,
            lift: BigInt::from(class),
        })
    }

    /// The state the reader stands on, `(w, u)`.
    pub fn point(&self) -> &[Rat; 2] {
        &self.point
    }

    /// The class of the state, `ℓ mod 4`.
    pub fn class(&self) -> u8 {
        self.class
    }

    /// The lift `ℓ`, the class with its winding.
    pub fn lift(&self) -> &BigInt {
        &self.lift
    }

    /// **The lift as the aeon's reading**: `ℓ/4` turns, whole windings `⌊ℓ/4⌋` and open phase
    /// `(ℓ mod 4)/4` ([`Reading::of_turns`]).
    pub fn reading(&self) -> Reading {
        Reading::of_turns(&Rat::new(self.lift.clone(), BigInt::from(RAYS)))
    }

    /// **Advance to the next state**: the symbol of the tick `point → next`, the lift carried. The
    /// crossing and the landing class are [`land`]'s, the owner's signed carry law; the lift itself
    /// adds the chord's advance.
    pub fn advance(&mut self, next: [Rat; 2]) -> Result<SectionSymbol, SectionRefusal> {
        let advance = chord(&self.point, &next)?;
        let (crossing, landed) = land(self.class, advance)?;
        let symbol = SectionSymbol {
            class: self.class,
            advance,
            crossing,
        };
        self.class = landed;
        self.lift += BigInt::from(advance);
        self.point = next;
        Ok(symbol)
    }

    /// **The polarity partner**: the reader on the state `−z` with the lift `ℓ + 2`, the dyad's `U`
    /// (module header). Advanced through the negated states it keeps the lift `2` above this one's
    /// and reads the same advances.
    pub fn half_turn(&self) -> Self {
        Self {
            point: [-&self.point[0], -&self.point[1]],
            class: (self.class + 2) % RAYS,
            lift: &self.lift + BigInt::from(2),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ratio::{integer, rat};

    fn z(w: i64, u: i64) -> [Rat; 2] {
        [integer(w), integer(u)]
    }

    #[test]
    fn each_ray_belongs_to_the_class_it_starts() {
        assert_eq!(quadrant(&z(1, 0)), Some(0));
        assert_eq!(quadrant(&z(1, 1)), Some(0));
        assert_eq!(quadrant(&z(0, 1)), Some(1));
        assert_eq!(quadrant(&z(-1, 1)), Some(1));
        assert_eq!(quadrant(&z(-1, 0)), Some(2));
        assert_eq!(quadrant(&z(-1, -1)), Some(2));
        assert_eq!(quadrant(&z(0, -1)), Some(3));
        assert_eq!(quadrant(&z(1, -1)), Some(3));
        assert_eq!(quadrant(&z(0, 0)), None);
    }

    #[test]
    fn a_chord_passes_its_rays_in_the_sense_of_its_cross_product() {
        // counterclockwise: class 0 to 1 (one ray), 0 to 2 (two rays); clockwise the negatives
        assert_eq!(chord(&z(2, 1), &z(-1, 2)), Ok(1));
        assert_eq!(chord(&z(2, 1), &z(-3, -1)), Ok(2));
        assert_eq!(chord(&z(-1, 2), &z(2, 1)), Ok(-1));
        assert_eq!(chord(&z(-3, -1), &z(2, 1)), Ok(-2));
        // the same direction passes none
        assert_eq!(chord(&z(1, 1), &z(3, 3)), Ok(0));
        // within one class, either sense
        assert_eq!(chord(&z(3, 1), &z(1, 3)), Ok(0));
        assert_eq!(chord(&z(1, 3), &z(3, 1)), Ok(0));
        // a closing step across the section ray: class 3 to 0 is an arrival
        assert_eq!(chord(&z(1, -1), &z(1, 1)), Ok(1));
    }

    #[test]
    fn the_origin_and_a_chord_through_it_have_no_symbol() {
        assert_eq!(chord(&z(0, 0), &z(1, 1)), Err(SectionRefusal::AtOrigin));
        assert_eq!(chord(&z(1, 1), &z(0, 0)), Err(SectionRefusal::AtOrigin));
        assert_eq!(
            chord(&z(1, 1), &z(-2, -2)),
            Err(SectionRefusal::ThroughOrigin)
        );
        assert_eq!(SectionReader::at(z(0, 0)), Err(SectionRefusal::AtOrigin));
    }

    #[test]
    fn a_refused_tick_leaves_the_reader_as_it_was() {
        let mut reader = SectionReader::at(z(1, 1)).unwrap();
        let before = reader.clone();
        assert_eq!(
            reader.advance(z(-1, -1)),
            Err(SectionRefusal::ThroughOrigin)
        );
        assert_eq!(reader.advance(z(0, 0)), Err(SectionRefusal::AtOrigin));
        assert_eq!(reader, before);
    }

    #[test]
    fn the_lift_carries_a_whole_turn_as_one_winding() {
        // four quarter turns about the origin: the lift passes four rays, one arrival
        let mut reader = SectionReader::at(z(1, 1)).unwrap();
        let mut crossings = 0;
        for point in [z(-1, 1), z(-1, -1), z(1, -1), z(1, 1)] {
            crossings += reader.advance(point).unwrap().crossing;
        }
        assert_eq!(*reader.lift(), BigInt::from(4));
        assert_eq!(crossings, 1);
        let reading = reader.reading();
        assert_eq!(*reading.windings(), BigInt::from(1));
        assert!(reading.phase().is_zero());
        // and back: the departure is a negative crossing, the winding returns
        for point in [z(1, -1), z(-1, -1), z(-1, 1), z(1, 1)] {
            crossings += reader.advance(point).unwrap().crossing;
        }
        assert_eq!(*reader.lift(), BigInt::from(0));
        assert_eq!(crossings, 0);
        assert_eq!(reader.reading().turns(), rat(0, 1));
    }

    /// The hand law, kept here only as an independent oracle for the owner's landing:
    /// `⌊(class + advance)/4⌋ − ⌊class/4⌋` and `(class + advance) mod 4`.
    fn by_hand(class: u8, advance: i8) -> (i8, u8) {
        let (class, advance, rays) = (i32::from(class), i32::from(advance), i32::from(RAYS));
        let crossing = (class + advance).div_euclid(rays) - class.div_euclid(rays);
        (
            i8::try_from(crossing).unwrap(),
            u8::try_from((class + advance).rem_euclid(rays)).unwrap(),
        )
    }

    #[test]
    fn the_landing_is_the_owners_signed_carry_law() {
        // the arrivals and the departures across the section, and the landings that cross nothing
        assert_eq!(land(3, 1), Ok((1, 0)));
        assert_eq!(land(2, 2), Ok((1, 0)));
        assert_eq!(land(0, -1), Ok((-1, 3)));
        assert_eq!(land(1, -2), Ok((-1, 3)));
        assert_eq!(land(3, -1), Ok((0, 2)));
        assert_eq!(land(0, 2), Ok((0, 2)));
        assert_eq!(land(1, 0), Ok((0, 1)));
        // the corners of the whole carrier: every advance an `i8` holds, from the classes a section
        // word may carry and from classes it may not (the crossing is then relative to the class's
        // own winding), never a refusal and never a difference from the hand law
        for class in [0u8, 1, 2, 3, 4, 7, 255] {
            for advance in i8::MIN..=i8::MAX {
                assert_eq!(
                    land(class, advance),
                    Ok(by_hand(class, advance)),
                    "class {class}, advance {advance}"
                );
            }
        }
    }

    #[test]
    fn the_crossing_is_the_difference_of_the_lifts_whole_windings_at_every_winding() {
        // the carry depends on the phase `ℓ mod 4` and not on the winding: the same crossing and
        // landing at ℓ and at ℓ + 4n, read as the difference of the aeon's readings of ℓ/4
        for lift in -9i64..=9 {
            let class = u8::try_from(lift.rem_euclid(4)).unwrap();
            for advance in -2i8..=2 {
                let before = Reading::of_turns(&rat(lift, 4));
                let after = Reading::of_turns(&rat(lift + i64::from(advance), 4));
                let (crossing, landed) = land(class, advance).unwrap();
                assert_eq!(
                    BigInt::from(crossing),
                    after.windings() - before.windings(),
                    "lift {lift}, advance {advance}"
                );
                assert_eq!(rat(i64::from(landed), 4), *after.phase());
            }
        }
    }

    #[test]
    fn the_reader_emits_the_landing_at_every_tick_and_its_reading_keeps_the_windings() {
        // a walk with arrivals, a departure back across the section and quiet ticks
        let walk = [
            z(1, 1),
            z(-1, 1),
            z(-1, -1),
            z(1, -1),
            z(1, 1),
            z(1, -1),
            z(-1, -1),
            z(-1, 1),
            z(-2, 1),
            z(1, 1),
            z(-1, 1),
            z(-1, -1),
            z(1, -1),
            z(1, 1),
        ];
        let mut reader = SectionReader::at(walk[0].clone()).unwrap();
        let (mut arrivals, mut departures) = (0i64, 0i64);
        for point in &walk[1..] {
            let before = reader.reading();
            let class = reader.class();
            let symbol = reader.advance(point.clone()).unwrap();
            let (crossing, landed) = land(class, symbol.advance).unwrap();
            assert_eq!((symbol.class, symbol.crossing), (class, crossing));
            assert_eq!(reader.class(), landed);
            let after = reader.reading();
            assert_eq!(
                after.windings() - before.windings(),
                BigInt::from(symbol.crossing)
            );
            assert_eq!(*after.phase(), rat(i64::from(landed), 4));
            arrivals += i64::from(symbol.crossing > 0);
            departures += i64::from(symbol.crossing < 0);
        }
        // two arrivals and one departure back across the section: the lift ends at 4, one winding
        assert_eq!((arrivals, departures), (2, 1));
        assert_eq!(*reader.lift(), BigInt::from(4));
        assert_eq!(
            *reader.reading().windings(),
            BigInt::from(arrivals - departures)
        );
    }

    #[test]
    fn the_half_turn_partner_reads_the_same_advances_two_above() {
        let walk = [z(1, 1), z(-2, 1), z(-1, -3), z(2, -1), z(1, 2)];
        let mut reader = SectionReader::at(walk[0].clone()).unwrap();
        let mut partner = reader.half_turn();
        assert_eq!(*partner.lift(), reader.lift() + BigInt::from(2));
        for point in &walk[1..] {
            let negated = [-&point[0], -&point[1]];
            let (a, b) = (
                reader.advance(point.clone()).unwrap(),
                partner.advance(negated).unwrap(),
            );
            assert_eq!(a.advance, b.advance);
            assert_eq!(b.class, (a.class + 2) % RAYS);
            assert_eq!(*partner.lift(), reader.lift() + BigInt::from(2));
        }
    }
}
