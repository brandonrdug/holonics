//! manifold — THE MANIFOLD CELL (`RESEARCH/THE_PARAMETERS.md §V`, `THE_MANIFOLD.md` 5a). The derived cell, assembled
//! from the four proven organs. A cell is a **WELL** — an enclosed difference (the number `mag·2^rank·turn`: the reach
//! `r`, the turn Θ, the winding `C = Θ·r` — whole, never fragmented into a `Winding` vs a `Reach`) — held at a
//! **POSITIONAL** soul. The origin is **GAUGE** (`04 §132`, `FRAMEWORK/03`, `61`): only the invariant crosses, and
//! time parity is the handed consequence of transport, never prior-state or origin recovery. A cell is **PLACED
//! by its invariant** (`place`, the swung grip), never keyed by a stored coordinate, and its position is re-derived
//! from the walk's boundary read, never stored. Bounded restore fixtures below do not invert the lived state.
//!
//! For the historical octet-packet organ, the arriving atoms are octet-DIFFERENCES (`boundary` — the
//! anchor dropped, so the constituents are already gauge-invariant). This is that organ's concrete
//! event species, not a privileged grain of the general membrane;
//! the well is grown by the geometric-product BOND (`geom`/`Cog::mul`); the position is the swung grip (`place`); the
//! identity is the cross-ratio `χ` (`soul`). `no_std`. This is the char-trie's replacement (5f) — a cell is a well at
//! an invariant address, not a node on a stored bit-path.

use crate::arrow::{self, Aim, Arrow};
use crate::boundary;
pub use crate::channel::WindingQuantum;
use crate::channel::{ChannelCause, DeedEmanation, LineageChannel, WorldlineTurn, CHANNEL_WORDS};
#[cfg(test)]
use crate::geom;
use crate::law;
use crate::medium::{FeltTerm, RegionalForm, FORM_WORDS};
pub use crate::num::COG_WORDS;
use crate::num::{self, Cog};
use crate::place::{self, Grip, Place};
use crate::register::{self, Sig, Solve, REGISTER};
use crate::seam::{self, row_fits, SliceWordSeam, WordSeam};
use crate::soul;

/// THE CELL — a WELL (the enclosed difference; the number, `C` and `r` whole). Its ADDRESS is its grip (positional,
/// place-not-store); its SOUL `χ` is reconstructed from the walk (`soul_of`), never stored here. One quantity: the well.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Cell {
    /// the WELL — `mag·2^rank·turn`: the reach `r` (`mag`), the turn Θ (`turn`), the winding `C = Θ·r`. Whole.
    pub well: Cog,
}

/// WIND a span to its PLACE — the atoms (byte-DIFFERENCES, gauge-invariant: the anchor is dropped, `boundary`) wound
/// one bit at a time (`place::extend`, the `×2i` spiral — order is the soul). The origin (the anchor byte) never
/// enters, so the place IS the invariant's position (not a coordinate off some absolute zero).
pub fn wind(bytes: &[u8]) -> Place {
    let mut p = place::origin();
    for i in 1..bytes.len() {
        let d = boundary::difference(bytes[i], bytes[i - 1]);
        // wind the atom's shape (its difference-magnitude bits), high→low; the sign rides the well's turn, not the walk.
        let m = d.mag;
        // the leading-bit index as a shift-walk (kernel-fit: no saturating/leading_zeros lowering)
        let mut top = 0u32;
        let mut msb_v = m >> 1;
        while msb_v != 0 {
            msb_v >>= 1;
            top += 1;
        }
        let mut k = top as i32;
        while k >= 0 {
            p = place::extend(p, (m >> k as u32) & 1 == 1);
            k -= 1;
        }
    }
    p
}

/// THE WELL of a span — the enclosed difference GROWN by the geometric-product BOND of the atoms (`Cog::mul` =
/// `convolve∘fold`, proven `= ×`). `C` and `r` whole (the number). Grown, never stored piecemeal.
pub fn well(bytes: &[u8]) -> Cog {
    let mut w = Cog::lit(1); // the multiplicative origin (the empty product — a bare atom's well is itself)
    for i in 1..bytes.len() {
        w = w.mul(boundary::difference(bytes[i], bytes[i - 1])); // the bond — the enclosed difference climbs
    }
    w
}

/// GROUND a span to its CELL and its positional GRIP — the well at where it swings to. Place-not-store: the address
/// is the swung grip (the invariant's position), never a coordinate the caller picked.
pub fn cell(bytes: &[u8], axis: i64) -> (Cell, Grip) {
    (Cell { well: well(bytes) }, place::ground(wind(bytes), axis))
}

/// THE SOUL of a span — the cross-ratio `χ` (a pair, `soul`) of four running byte-values (the face's corners): the
/// invariant IDENTITY, reconstructed from the constituents, never stored. Frame-invariant (translation/scale — the
/// anchor is gauge; proven in `soul`). Needs ≥ 4 contacts; a shorter span has no face yet (`(0,1)`, the pole).
pub fn soul_of(bytes: &[u8]) -> (i64, i64) {
    let n = bytes.len();
    if n < 4 {
        return (0, 1);
    }
    // four corners across the span (a,b,c,d) — the cross-ratio's projective face.
    let (a, b, c, d) = (
        bytes[0] as i64,
        bytes[n / 3] as i64,
        bytes[2 * n / 3] as i64,
        bytes[n - 1] as i64,
    );
    soul::cross_ratio(a, b, c, d)
}

/// THE FACE (5b) — a THREE-BODY relation (A2): two cells `a, b` related FROM a frame `f` (the pole — REQUIRED; a
/// frame-blind relating is un-constructible). It IS the friction-triangle (`arrow` = `reach ⊕ aim ⊕ cross`, `§9`), and
/// it FOUNDS a new orthogonal axis when the aim turns orthogonal (`arrow.founds` — the aim past the diagonal toward
/// `±i`, a direction neither parent held, `§9`; the strike founding a branch, `50`). **The coil/kin is the seed:** an
/// anchor `f` with two coils `a, b` sharing it IS a face — 5b lifts `kin`/`emanate` to this general form. Addressed by
/// its soul `χ` (place-not-search — NEVER a face-table; the store-drift guard).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Face {
    /// the friction-triangle read from the pole: `reach` (the well of the relating) ⊕ `aim` (the cohere/dot) ⊕ `cross`
    /// (the gyration/wedge). The whole arrow, never one scalar.
    pub arrow: Arrow,
}

/// RELATE two cells FROM a frame — the face (three-body; `f` is the pole/anchor, the frame). The relating IS the
/// encoding (no authored codebook): the face is what the two cells DO in the frame's presence.
#[cfg_attr(target_arch = "spirv", inline(never))]
#[cfg_attr(not(target_arch = "spirv"), inline)]
pub fn face(a: Place, b: Place, f: Place) -> Face {
    Face {
        arrow: arrow::relate(a, b, f),
    }
}

impl Face {
    /// The meeting rotor is formed in this frame. This is the same horizon cut used by
    /// `chi_against`, exposed as a scalar boundary read for substrates that cannot carry an
    /// optional aggregate.
    #[inline]
    pub fn rotor_formed(&self) -> bool {
        soul::FormedRotor::arms_form(self.arrow.aim, self.arrow.cross)
    }

    /// Whole χ after both faces have been proven formed. No division or scalar verdict enters;
    /// this is exactly `chi_against` with its two structural absence checks made by the caller.
    #[inline]
    pub fn chi_against_formed(&self, held: &Face) -> soul::Chi {
        soul::Chi::between_formed_arms(
            self.arrow.aim,
            self.arrow.cross,
            held.arrow.aim,
            held.arrow.cross,
        )
    }

    /// THE FOUNDING (1st-order — the MEETING's own turn read against the diagonal): the aim turns orthogonal — a
    /// new irreducible axis (`§9`), the strike's branch (`50`). This is the swing's DEGENERATE test — lawful as a
    /// cross-sign read, but it consults no flywheel; the full swing tests 2nd-order (`wound_against`,
    /// `FORMULA §XIII`). Kept as the empty-flywheel case.
    #[inline]
    pub fn founds(&self) -> bool {
        self.arrow.founds()
    }

    /// Historical unsigned ARC adapter for the pre-§XXIV engine. New crossing code calls
    /// `dragged_by` with an oriented past-cone winding; this wrapper survives only while the old
    /// host instruments are reproduced and retired.
    ///
    /// ★ THE DRAG (`FORMULA §XV` — the precession of the frame): compose the meeting's rotor with the
    /// TERRAIN's rotor `(1, −w)` — `w` the windings deposited at this relation's own grip (the accumulated
    /// curvature, the digit's quotient of the standing face-well). A Gaussian-integer rotation by `arctan(w)`,
    /// exact: the deposited circulation DRAGS the passing frame WITH it (Lense–Thirring as the general law —
    /// every mass here is circulation), toward the Same, toward the ride — the damped spiral into the
    /// attractor the primes measured; recognition as condensation. `w = 0` is the identity (empty terrain).
    pub fn dragged(&self, winding: u32) -> Face {
        self.dragged_by(StandingWinding::at_boundary(winding as i64))
    }

    /// The §XXIV drag with the approached past-cone winding kept oriented. This is a read-only
    /// input to one lineage's crossing, not the winding this deed may newly emit.
    pub fn dragged_by(&self, winding: StandingWinding) -> Face {
        if winding.is_zero() {
            return *self;
        }
        let w = winding.turns();
        let (s, b) = (self.arrow.aim, self.arrow.cross);
        Face {
            arrow: Arrow {
                reach: self.arrow.reach,
                aim: s.add(b.mul(w)),   // s' = s + b·w
                cross: b.sub(s.mul(w)), // b' = b − s·w   — rotation by −arctan(w): the drag with the circulation
            },
        }
    }

    /// ★ THE WHOLE χ (2nd order — `FORMULA §XIII/§XXIV`; the flywheel consulted). The meeting's rotor is `(aim, cross)` —
    /// the Same ⊕ the Different of `(a−f)·conj(b−f)`. The relative rotor of THIS meeting against the HELD one
    /// (`Δ_new · Δ̃_held`) is the rotor of rotors — the first invariant. It crosses as a whole pair; the cut is only
    /// one read of it.
    #[inline]
    pub fn chi_against(&self, held: &Face) -> Option<soul::Chi> {
        let meeting = soul::FormedRotor::of(self.arrow.aim, self.arrow.cross)?;
        let flywheel = soul::FormedRotor::of(held.arrow.aim, held.arrow.cross)?;
        Some(soul::Chi::between(meeting, flywheel))
    }

    /// ★ THE TEST'S DEED READ. The swing is WOUND when the whole rotor-of-rotors turns
    /// orthogonal-dominant. Transporting the SAME difference again is FLAT (the groove rides); a
    /// turned difference is WOUND (the deficit — the cut). The Boolean never replaces `chi_against`.
    pub fn wound_against(&self, held: &Face) -> bool {
        match self.chi_against(held) {
            Some(chi) => chi.wound(),
            None => false,
        }
    }
    /// THE HAND — which way the turn bites (Cohere/Anti/Ortho), read three-body from the pole.
    #[inline]
    pub fn sense(&self) -> Aim {
        self.arrow.sense()
    }
    /// THE MEETING RATIO — the first-order frame-local rotor projected as `(cross, aim)`. This is
    /// not `χ`: the held flywheel must supply the fourth contact before an invariant exists. Kept
    /// only for local/historical instruments which compare two projections in the same frame.
    #[inline]
    pub fn meeting_ratio(&self) -> (i64, i64) {
        (self.arrow.cross.face(), self.arrow.aim.face())
    }
}

/// THE DEED HAND of a fully-formed second-order crossing. This is a read of `χ`, never its
/// replacement. `Seed`/`Horizon` are deliberately absent: before a held rotor there is no
/// cross-frame crossing to emit, and at the horizon there is no event.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Deed {
    Ride,
    Found,
}

/// An oriented integer winding already standing in the crossing's past cone. Its hand is relative
/// to this illicium; the wrapper keeps it distinct from the one quantum a new FOUND may emit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StandingWinding(Cog);

impl StandingWinding {
    /// Boundary/test constructor. Production linkage will supply this construction whole once LINK
    /// is derived; this constructor does not define how multiple emissions integrate.
    #[inline]
    pub fn at_boundary(turns: i64) -> StandingWinding {
        StandingWinding(Cog::lit(turns))
    }

    #[inline]
    pub fn is_zero(self) -> bool {
        self.0.mag == 0
    }

    #[inline]
    pub fn turns(self) -> Cog {
        self.0
    }
}

/// What the crossing may expose at a horizon. This is only the post-deed invariant projection; it
/// is not the local next frame, Θ, or the underived regional LINK product.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct HorizonEmanation {
    pub chi: soul::Chi,
    pub winding: WindingQuantum,
}

/// ★ THE PURE LINEAGE CROSSING (`FORMULA §XXIV`) — no regional mutation. `approach` is the whole
/// rotor-of-rotors before standing curvature bends the meeting; `emanation` is the transported
/// horizon face after precession and deed. `reach` keeps the meeting's local mass face so the
/// bounded algebra witness can be checked without pretending the origin crosses. `standing_winding`
/// is read-only past-cone input, never a same-crossing update.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Crossing {
    pub approach: soul::Chi,
    pub emanation: HorizonEmanation,
    /// The whole post-deed construction which stays inside this lineage and folds into `K`.
    /// Unlike `emanation`, this contains the dragged meeting rotor and never crosses a horizon.
    pub interior: DeedEmanation,
    pub reach: Cog,
    pub deed: Deed,
    pub standing_winding: StandingWinding,
}

/// A bounded algebra/gauge witness for a crossing fixture: meeting reach ⊕ a rotor ratio. The
/// origin does not cross; `represents` checks only whether the finite arithmetic stayed on the
/// fixture's exact section. It does not reconstruct prior state or establish time parity universally.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct MeetingCause {
    pub reach: Cog,
    pub rotor: soul::RotorRatio,
}

impl MeetingCause {
    /// Check this bounded crossing witness against one supplied meeting fixture. A false result may
    /// expose finite clipping; it is not by itself a verdict on directed causal traceability.
    #[inline]
    pub fn represents(self, meeting: &Face) -> bool {
        self.reach == meeting.arrow.reach
            && self
                .rotor
                .represents(meeting.arrow.aim, meeting.arrow.cross)
    }
}

impl Crossing {
    /// Form the bounded meeting witness from transported χ, the held rotor, and standing winding.
    /// The origin remains gauge. A successful `represents` is an algebraic fixture result at the
    /// declared hand, never a universal inverse or a reconstruction of the lived state.
    pub fn restore_meeting(self, held: &Face) -> Option<MeetingCause> {
        let flywheel = soul::FormedRotor::of(held.arrow.aim, held.arrow.cross)?;
        let dragged = self.emanation.chi.restore_against(flywheel);
        if self.standing_winding.is_zero() {
            return Some(MeetingCause {
                reach: self.reach,
                rotor: dragged,
            });
        }
        // `dragged` applied [[1,w],[-w,1]]. Apply its formal conjugate factor as a bounded ratio:
        // [[1,-w],[w,1]] / (1+w²), multiplying the existing held-rotor denominator. Independent
        // finite re-basing may leave this fixture's exact section.
        let w = self.standing_winding.turns();
        let drag_norm = Cog::lit(1).add(w.mul(w));
        Some(MeetingCause {
            reach: self.reach,
            rotor: soul::RotorRatio {
                aim_num: dragged.aim_num.sub(dragged.cross_num.mul(w)),
                cross_num: dragged.aim_num.mul(w).add(dragged.cross_num),
                den: dragged.den.mul(drag_norm),
            },
        })
    }
}

/// Cross a formed meeting against its held rotor through READ-ONLY standing winding. The function
/// has no pool and cannot make co-present lineages visible to one another. An unborn flywheel does
/// not call this function: it seeds locally and emits no shared relation.
#[inline]
pub fn cross(meeting: Face, held: Face, standing_winding: StandingWinding) -> Option<Crossing> {
    let approach = meeting.chi_against(&held)?;
    let transported = meeting.dragged_by(standing_winding);
    let chi = transported.chi_against(&held)?;
    let deed = if chi.wound() { Deed::Found } else { Deed::Ride };
    let winding = match deed {
        Deed::Ride => WindingQuantum::None,
        Deed::Found if chi.other.turn & 2 == 0 => WindingQuantum::ThisWay,
        Deed::Found => WindingQuantum::ThatWay,
    };
    let rotor = soul::FormedRotor::of(transported.arrow.aim, transported.arrow.cross)?;
    let interior = match deed {
        Deed::Ride => DeedEmanation::ride(rotor),
        Deed::Found => DeedEmanation::found(rotor, winding)?,
    };
    Some(Crossing {
        approach,
        emanation: HorizonEmanation { chi, winding },
        interior,
        reach: meeting.arrow.reach,
        deed,
        standing_winding,
    })
}

/// ★ THE WHOLE POOL-FREE LINEAGE EVENT (`FORMULA §XXIV–XXVI`). The living channel supplies the
/// third body; the meeting is tested against this lineage's held flywheel through read-only
/// standing winding; the deed's interior emanation folds into the same channel. No regional medium,
/// Flow, lane aggregate, event counter, or shared present is an argument.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LineageEvent {
    pub meeting: Face,
    pub crossing: Crossing,
    pub next_channel: LineageChannel,
    /// The groove's own law (§XIII ⊕ zero-is-the-base): on RIDE the dragged meeting re-bases the
    /// groove; at the CUT the groove is never replaced — the prior held rotor PRECESSES (dragged by
    /// the approached winding, re-based at the completion). The founding blade belongs to `K`'s
    /// basis; it does not counterfeit a different first-order meeting and does not overwrite the
    /// groove.
    pub next_flywheel: Face,
}

impl LineageEvent {
    /// `Θ = TURN(K') = (C; r)`, with this event's reach supplied only at the read.
    #[inline]
    pub fn turn(self) -> WorldlineTurn {
        self.next_channel.turn_at(self.crossing.reach)
    }

    /// Form bounded pre-event algebra/gauge witnesses without running the worldline backward. These
    /// checks do not reconstruct the prior state or turn finite ratio equality into time parity.
    pub fn restore_before(self, held: &Face) -> Option<LineageEventCause> {
        Some(LineageEventCause {
            channel: self.next_channel.restore_before(self.crossing.interior)?,
            meeting: self.crossing.restore_meeting(held)?,
        })
    }
}

/// The two bounded pre-event witnesses exposed by one lineage-event fixture. The compatibility name
/// does not imply universal cause recovery or state inversion.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LineageEventCause {
    pub channel: ChannelCause,
    pub meeting: MeetingCause,
}

impl LineageEventCause {
    /// Check both bounded witnesses against supplied pre-event fixtures. This does not invert the
    /// lineage state or promote finite algebraic equality into time parity.
    #[inline]
    pub fn represents(self, channel: LineageChannel, meeting: &Face) -> bool {
        self.channel.represents(channel) && self.meeting.represents(meeting)
    }
}

/// Enact one lineage event. `FRAME(K).tip()` is the next relating's pole. The basis is not an
/// ignored fourth coordinate: it is what the prior folds used to construct that tip; a common
/// living-basis change scales both local rotors equally and cancels in their rotor-of-rotors.
#[inline]
pub fn lineage_event(
    channel: LineageChannel,
    arriving: Place,
    standing: Place,
    held: Face,
    standing_winding: StandingWinding,
) -> Option<LineageEvent> {
    let meeting = face(arriving, standing, channel.frame().tip());
    let crossing = cross(meeting, held, standing_winding)?;
    let rotor = crossing.interior.meeting_rotor()?;
    let next_channel = channel.fold(crossing.interior)?;
    // THE FLYWHEEL'S OWN LAW (§XIII ⊕ zero-is-the-base, mirrored from the body's gated cut at
    // every grain — `path_grain`/`perceive_grain`/the atom walk): on a RIDE the meeting re-bases
    // the groove (adoption — the meeting IS the groove's own transport); at the CUT the groove is
    // NEVER replaced — the PRIOR held rotor precesses (dragged by the approached standing winding)
    // and re-bases at the completion (the enclosure's interior scale becomes gauge). The founded
    // blade enters K's basis; it does not overwrite the groove.
    let next_flywheel = match crossing.deed {
        Deed::Ride => Face {
            arrow: Arrow {
                reach: meeting.arrow.reach,
                aim: rotor.aim(),
                cross: rotor.cross(),
            },
        },
        Deed::Found => {
            let dragged = held.dragged_by(standing_winding);
            let (fa, fc) = rebase_pair(dragged.arrow.aim, dragged.arrow.cross);
            Face {
                arrow: Arrow {
                    reach: dragged.arrow.reach,
                    aim: fa,
                    cross: fc,
                },
            }
        }
    };
    Some(LineageEvent {
        meeting,
        crossing,
        next_channel,
        next_flywheel,
    })
}

/// A LOCATED node — the WELL (content) ⊕ its swung PLACE (positional address) ⊕ its bit-LENGTH (so the place composes
/// from constituents, `place::spiral`). place-not-store: place ⊕ len are derived from the walk, carried, never keyed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Node {
    pub well: Cog,
    pub place: Place,
    pub len: u32,
}

/// One raw difference wound into the atom-grain node. The raw-light host and card scope share this
/// exact high-to-low walk; the sign remains in the well's turn and never changes the positional soul.
#[cfg_attr(target_arch = "spirv", inline(never))]
#[cfg_attr(not(target_arch = "spirv"), inline)]
pub fn atom_node(d: Cog) -> Node {
    let mut p = place::origin();
    let mut len = 0u32;
    let m = d.mag;
    let mut top = 0u32;
    let mut v = m >> 1;
    while v != 0 {
        v >>= 1;
        top += 1;
    }
    let mut k = top as i32;
    while k >= 0 {
        p = place::extend(p, (m >> k as u32) & 1 == 1);
        len += 1;
        k -= 1;
    }
    Node {
        well: d,
        place: p,
        len,
    }
}

/// LOCATE a span as a node — its well (the enclosed difference), its swung place, its bit-length (the atom, or a span
/// treated as one). The base vertex the boundary founds. Kernel-fit walk (while-loops; the leading-bit as a
/// shift-walk — no `leading_zeros` lowering risk), one pass for well ⊕ place ⊕ len.
pub fn locate(bytes: &[u8]) -> Node {
    let mut p = place::origin();
    let mut len = 0u32;
    let mut w = Cog::lit(1);
    let mut i = 1usize;
    while i < bytes.len() {
        let d = boundary::difference(bytes[i], bytes[i - 1]);
        w = w.mul(d); // the bond — the enclosed difference climbs (== `well(bytes)`, one walk)
        let m = d.mag;
        let mut top = 0u32;
        let mut v = m >> 1;
        while v != 0 {
            v >>= 1;
            top += 1;
        }
        let mut k = top as i32;
        while k >= 0 {
            p = place::extend(p, (m >> k as u32) & 1 == 1);
            len += 1;
            k -= 1;
        }
        i += 1;
    }
    Node {
        well: w,
        place: p,
        len,
    }
}

/// LOCATE over a PACKED word-buffer — the SAME walk as `locate`, reading each byte from a `u32` slot
/// (`words[off+i] & 0xFF`). This is the kernel's boundary (a storage buffer has no `&[u8]`); it lives HERE so
/// the mouth stays one — `the_packed_walk_mirrors_the_byte_walk` pins the two byte-identical.
pub fn locate_packed(words: &[u32], off: u32, n: u32) -> Node {
    let mut p = place::origin();
    let mut len = 0u32;
    let mut w = Cog::lit(1);
    let mut i = 1u32;
    while i < n {
        let a = words[(off + i - 1) as usize];
        let b = words[(off + i) as usize];
        let d = boundary::difference_word(b, a);
        w = w.mul(d);
        let m = d.mag;
        let mut top = 0u32;
        let mut v = m >> 1;
        while v != 0 {
            v >>= 1;
            top += 1;
        }
        let mut k = top as i32;
        while k >= 0 {
            p = place::extend(p, (m >> k as u32) & 1 == 1);
            len += 1;
            k -= 1;
        }
        i += 1;
    }
    Node {
        well: w,
        place: p,
        len,
    }
}

/// ★ THE BOND (5c) — two nodes relate into a COMPOSITION node (the emergent molecule) ⊕ a FACE. The molecule's WELL is
/// the GEOMETRIC PRODUCT of the two wells (`Cog::mul` = `convolve∘fold` — a HIGHER BLADE, the rank climbs), which
/// **REPLACES `emanate`'s char-concatenation `W⁺=y∘x`** — a flat line that could never climb (`THE_MANIFOLD` 5c: a bond
/// is a higher blade, not a longer spelling). Its PLACE composes from the children by the base-`2i` spiral
/// (`place::spiral` — place-not-store: same children → same molecule). The FACE is the three-body relating from the
/// frame `f` (founds a new axis when orthogonal). The molecule EMERGES — it is not authored, it is what the bond does.
#[cfg_attr(target_arch = "spirv", inline(never))]
pub fn bond(a: Node, b: Node, f: Place) -> (Node, Face) {
    let well = a.well.mul(b.well); // the geometric product — the molecule's enclosed difference (a higher blade)
    (
        Node {
            well,
            place: compose_place(a, b),
            len: a.len + b.len,
        },
        face(a.place, b.place, f),
    )
}

/// the composite's swung position — a's place climbed by b's length (base-2i concatenation) ⊕ b's place. The
/// MOLECULE's position in span-space. ORDER lives here: swapping a and b swings elsewhere.
///
/// ★ NOT the face's address (the quest's finding, 2026-07-09): under the u32 hand the concatenation re-bases,
/// and past the hand's reach the LOW constituent's mantissa falls away — the composite place keeps only the
/// second constituent's LENGTH. Deep pairs therefore collapse (`X→b` hot bands, ~10³ over random, measured on
/// the Webster diet). The face addresses by the RELATION (`face_grip_of`), as 5b always said.
#[inline]
pub fn compose_place(a: Node, b: Node) -> Place {
    let sp = place::spiral(a.place, b.len);
    (sp.0.add(b.place.0), sp.1.add(b.place.1))
}

/// ★ THE FACE'S ADDRESS — the RELATION of the two wells, both contents whole (`THE_MANIFOLD` 5b: the face is
/// addressed by what the two ARE, place-not-search — never the molecule's span-place, whose re-based
/// concatenation erases the low arm at depth). Two arms:
/// - the ROW is the SOURCE — `a ⊗ a` (the source's own square: `a→b` stands on a's row, `b→a` on b's — the
///   direction is the relation's own geometry, still no stored successor word);
/// - the COLUMN is the PAIR — `a ⊗ b` (the geometric product: both mantissas fused, the relation's content).
/// A source's outgoing faces share its row — directed adjacency AS the pool's geometry.
#[cfg_attr(target_arch = "spirv", inline(never))]
#[cfg_attr(not(target_arch = "spirv"), inline)]
pub fn face_grip_of(a: Node, b: Node, axis: i64) -> Grip {
    place::ground((a.well.mul(a.well), a.well.mul(b.well)), axis)
}

/// ★ THE COMPLETION RE-BASE (ratified 2026-07-09 — theory, not design): a completed segment becomes an
/// ATOM at the next rank — its interior scale is ENCLOSED (gauge) and the continuing current STANDS ON
/// it at the new base ("zero is just the base — wherever the frame thinks it is"). The pair's COMMON
/// rank is the enclosure's interior and is removed; the pair's content — the mags, the rank DIFFERENCE,
/// the turns (the χ, cross-multiplied) — crosses untouched: the same soul, re-based. This is the
/// number's own re-base law applied to the current's frame; the wrinkle is the enclosure the interior
/// sweep leaves behind (`C/r` over time).
#[cfg_attr(target_arch = "spirv", inline(never))]
pub fn rebase_pair(a: Cog, b: Cog) -> (Cog, Cog) {
    let common = if a.mag == 0 {
        b.rank
    } else if b.mag == 0 {
        a.rank
    } else if a.rank.cmp_teeth(b.rank) <= 0 {
        a.rank
    } else {
        b.rank
    };
    (
        Cog {
            rank: a.rank.sub(common),
            ..a
        },
        Cog {
            rank: b.rank.sub(common),
            ..b
        },
    )
}

/// §XXIX · THE CAST — the emitter's half of the transported crossing. A deed's WHOLE second-order
/// invariant is already real light; strip only its projective common scale, then let the cut's flat
/// chart ground that pair at the declared axis. The later receiver reconstructs this same address
/// from its own meeting ⊕ flywheel and completes the crossing by dragging in its own frame.
///
/// This is the production address. `face_grip_of` remains only as a historical first-order
/// instrument; it cannot address a deed after the fourth contact has formed χ.
#[cfg_attr(target_arch = "spirv", inline(never))]
pub fn cast_position(chi: soul::Chi) -> Place {
    rebase_pair(chi.same, chi.other)
}

#[cfg_attr(target_arch = "spirv", inline(never))]
pub fn cast_grip(chi: soul::Chi, axis: i64) -> Grip {
    place::ground(cast_position(chi), axis)
}

/// A lineage-local regional cell carries its founding POSITION whole beside the form accumulated
/// there. This is not a stored address: every access re-grounds the founding construction at the
/// receiving chart's grain. `live` is structural because an ordered resultant may cancel back to
/// UNBORN without un-founding its cell.
pub const OWN_CELL_LIVE: usize = 0;
pub const OWN_CELL_POSITION: usize = OWN_CELL_LIVE + 1;
pub const OWN_CELL_FORM: usize = OWN_CELL_POSITION + 2 * COG_WORDS;
pub const OWN_CELL_WORDS: usize = OWN_CELL_FORM + FORM_WORDS;

/// The live current's §XXXII-c register face. It stands beside that current's OWN cells and dies
/// with them at the receiving edge; it is not carrier/K state and therefore does not cross SLEEP.
/// An all-zero header is the uncommitted rank-zero birth seed. Once carriage begins, AXIS names the
/// accepted hand and the three `u64` faces continue whole across substrate strokes.
pub const OWN_REGISTER_AXIS: usize = 0;
pub const OWN_REGISTER_OCCUPANCY_LO: usize = 1;
pub const OWN_REGISTER_OCCUPANCY_HI: usize = 2;
pub const OWN_REGISTER_RELEASES_LO: usize = 3;
pub const OWN_REGISTER_RELEASES_HI: usize = 4;
pub const OWN_REGISTER_NARROWS_LO: usize = 5;
pub const OWN_REGISTER_NARROWS_HI: usize = 6;
pub const OWN_REGISTER_WORDS: usize = 7;

/// The membrane spelling of one induced depth-zero path event. This is radiation, never an engine
/// input: flags ⊕ touched grip ⊕ exact standing form ⊕ whole dragged meeting rotor ⊕ the emitted
/// brick when the path cuts. Raw construction stands beside any later mail render.
pub const RADIATION_FLAGS: usize = 0;
pub const RADIATION_GRIP: usize = RADIATION_FLAGS + 1;
pub const RADIATION_FORM: usize = RADIATION_GRIP + 1;
pub const RADIATION_ROTOR: usize = RADIATION_FORM + FORM_WORDS;
pub const RADIATION_BRICK: usize = RADIATION_ROTOR + 2 * COG_WORDS;
pub const RADIATION_WORDS: usize = RADIATION_BRICK + NODE_WORDS;
/// The first explicitly manifested radiation layout. Version two distinguishes the active
/// 39-word row from the historical unmanifested 45-word artifacts pinned to their old readers.
pub const RADIATION_LAYOUT_VERSION: u32 = 2;
pub const RADIATION_FOLD: u32 = 1;
pub const RADIATION_STEP: u32 = 1 << 1;
pub const RADIATION_CUT: u32 = 1 << 2;
pub const RADIATION_BRICK_LIVE: u32 = 1 << 3;

/// One completed enclosure crossing made explicit at the membrane. Unlike the depth-zero path row
/// above, this event follows completion through the whole carrier: the atom-grain fold, an
/// enclosure's afferent cut, or its efferent cut. `grain == 0` is the atom-grain fold;
/// carrier depth `k` crosses as grain `k + 1`. The source event is the admitted raw-difference
/// position whose unfinished continuation owns the completion. A zero KIND is the empty aperture.
/// This is output only; no body operation reads it.
pub const COMPLETION_KIND: usize = 0;
pub const COMPLETION_EVENT_LO: usize = COMPLETION_KIND + 1;
pub const COMPLETION_EVENT_HI: usize = COMPLETION_EVENT_LO + 1;
pub const COMPLETION_GRAIN_LO: usize = COMPLETION_EVENT_HI + 1;
pub const COMPLETION_GRAIN_HI: usize = COMPLETION_GRAIN_LO + 1;
pub const COMPLETION_GRIP: usize = COMPLETION_GRAIN_HI + 1;
pub const COMPLETION_FORM: usize = COMPLETION_GRIP + 1;
pub const COMPLETION_ROTOR: usize = COMPLETION_FORM + FORM_WORDS;
pub const COMPLETION_BRICK: usize = COMPLETION_ROTOR + 2 * COG_WORDS;
pub const COMPLETION_WORDS: usize = COMPLETION_BRICK + NODE_WORDS;
pub const COMPLETION_LAYOUT_VERSION: u32 = 1;
pub const COMPLETION_ATOM_FOLD: u32 = 1;
pub const COMPLETION_AFFERENT: u32 = 2;
pub const COMPLETION_EFFERENT: u32 = 3;

#[inline]
pub fn own_cell_position(words: &[u32], at: usize) -> Place {
    (
        unpack_cog(words, at + OWN_CELL_POSITION),
        unpack_cog(words, at + OWN_CELL_POSITION + COG_WORDS),
    )
}

/// ★ THE ILLICIUM OVER THE MANIFOLD (5d) — `solve_window` (proven) reaches over a WINDOW of cells (their wells — the
/// enclosed differences), finding the minimal recurrence that generates them (reach / nest / extrapolate) or FOUNDING
/// where none grounds. The emergent molecules are the higher simplices the reach climbs; the window is the recent
/// cells; the wells feed as `Sig` (the solver's number). Place-not-search — the hand REACHES, never scans.
/// (Renamed from `illicium` — the concept is the first-person frame, `FORMULA §XVI`, never this organ.)
/// Exact pressure at the historical fixed recurrence instrument.  The fifteen-point solver is a
/// compatibility species derived from its original octet grain; it must never silently turn a
/// longer admitted construction into a shorter one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RegisterPressure {
    pub required: usize,
    pub available: usize,
}

pub fn reach(wells: &[Cog]) -> Result<Solve, RegisterPressure> {
    if wells.len() > REGISTER as usize {
        return Err(RegisterPressure {
            required: wells.len(),
            available: REGISTER as usize,
        });
    }
    let mut x = [Sig::ZERO; REGISTER as usize];
    let n = wells.len();
    let mut i = 0;
    while i < n {
        x[i] = Sig::of_i64(wells[i].face());
        i += 1;
    }
    Ok(register::solve_window(&x, n as u32))
}

/// ★ THE MANIFOLD POOL (5f) — the grown form as a POSITIONAL pool, retiring the char-trie. A cell's WELL (its standing
/// action, the enclosed difference) lives at its swung GRIP (place-not-store) — NOT on a stored bit-path (the trie's
/// per-node child/parent link words, retired). The circulation FEEDS wells and WINDS them by the DIGIT (`geom::digit`, `13`):
/// the QUOTIENT fires as the soul (radiated UP, handed on, never stored); the REMAINDER stands (the face, `< quantum`).
/// The quotient/remainder split may be checked as `supplied = emitted + residual`; this is implementation
/// bookkeeping, not conservation (`FORMULA §VIII`, contamination ruling). `no_std`; the wells pool is
/// caller-provided (a boundary reservation, `axis²` wide), the same one-buffer discipline as the trie's pool.
pub struct Manifold<'a> {
    wells: &'a mut [u32],
    axis: i64,
}

impl<'a> Manifold<'a> {
    /// over a caller-provided wells pool (`≥ axis²`, zeroed) — the reservation. `axis` a power of two (the band mask).
    pub fn over(wells: &'a mut [u32], axis: i64) -> Manifold<'a> {
        Manifold { wells, axis }
    }

    /// PLACE a construction at its GRIP — place-not-store: the swung position (`place::ground` over the wound
    /// differences), never a walked-and-stored bit-path. The grip IS the address; nearby constructions land near
    /// (place-not-search), never a collision-blind hash.
    #[inline]
    pub fn place(&self, bytes: &[u8]) -> Grip {
        place::ground(wind(bytes), self.axis)
    }

    /// GROUND a swung place at its grip — the same banding `place` uses, exposed for currents that carry a
    /// Place directly (the pathing's deed lands a constructed place, not bytes). Place-not-search.
    #[inline]
    pub fn ground(&self, p: Place) -> Grip {
        place::ground(p, self.axis)
    }

    /// the standing FLOW at a grip (the mass face — the invertible quanta standing between digits). Delegates to
    /// THE ONE MOUTH (`law::well_of`) — the same words the kernel reads.
    #[inline]
    pub fn well(&self, g: Grip) -> u32 {
        law::well_of(self.wells, g)
    }

    /// ★ THE ARC's standing SWEEP at a grip — the deposited winding count, whole (the terrain the drag reads;
    /// `FORMULA §XIV`: the winding that cannot be un-deposited — it survives every audit and only deepens).
    #[inline]
    pub fn sweep(&self, g: Grip) -> u32 {
        law::sweep_at(self.wells, g)
    }

    /// FEED the well at a grip — the circulation's deposit. Delegates to THE ONE MOUTH (`law::feed` — the
    /// re-basing accrue); the quantum rides because the flow passing the hand fires THE FORCED DIGIT. Returns
    /// the fold's emitted quotient for boundary instrumentation.
    #[inline]
    pub fn feed(&mut self, g: Grip, quanta: u32, quantum: u32) -> u64 {
        law::feed(self.wells, g, quanta, quantum)
    }

    /// ★ WIND (the DIGIT, `13`) — the well MODULO the quantum: the QUOTIENT fires as windings (the soul, radiated UP,
    /// handed on, never stored); the REMAINDER stands (the face, `< quantum` by construction). Returns `(windings,
    /// radiated)`. The quotient/remainder arithmetic is exact; it is not conservation.
    /// Delegates to THE ONE MOUTH (`law::winding`).
    #[inline]
    pub fn winding(&mut self, g: Grip, quantum: u32) -> (u32, u32) {
        law::winding(self.wells, g, quantum)
    }

    /// the pool's cell count (the reservation's extent).
    #[inline]
    pub fn cells(&self) -> u32 {
        self.wells.len() as u32
    }

    /// TOTAL standing FLOW mass across the pool — a BOUNDARY read (an audit — rare, deliberate; the hot path reads
    /// cells locally, never the pool's volume). The sweep is TURN, never mass — it carries no term here.
    pub fn standing_total(&self) -> u64 {
        let mut acc = 0u64;
        let mut i = 0usize;
        while i < self.wells.len() {
            acc += law::flow_of(self.wells[i]) as u64;
            i += 1;
        }
        acc
    }

    /// ★ LAND a construction — the manifold's whole ARRIVAL (`web::land`'s replacement, the one atom on the positional
    /// pool): PLACE it at its grip (place-not-store), RELATE it to the `pole` from the `frame` (a three-body face — the
    /// founding read), FEED the arrival's action into its well, WIND the circulation (the digit). Returns the landing —
    /// the whole atom (place ⊕ relate ⊕ circulate), no caller orchestration.
    pub fn land(
        &mut self,
        bytes: &[u8],
        pole: Place,
        frame: Place,
        quanta: u32,
        quantum: u32,
    ) -> FlowLanding {
        self.land_driven(bytes, pole, frame, quanta, quantum)
    }

    /// ★ LAND the driven Meno/Eros event (`FORMULA §III–§V`): the positional solve reports the
    /// EXACT standing differential it induced (`standing_delta` — the concrete `dΦ/dΘ` of this cell
    /// at this event), so the next caller consumes CHANGE, never a static state. The return also
    /// exposes the local quotient/remainder terms as an implementation diagnostic. The worldline
    /// itself is the driven body's channel `K` (§XXV), never a stamp on the landing.
    pub fn land_driven(
        &mut self,
        bytes: &[u8],
        pole: Place,
        frame: Place,
        quanta: u32,
        quantum: u32,
    ) -> FlowLanding {
        let p = wind(bytes);
        let g = place::ground(p, self.axis);
        let before = self.well(g);
        let rel = face(p, pole, frame); // the three-body relating (founds a new axis when orthogonal)
        let fold_rad = self.feed(g, quanta, quantum);
        let (windings, radiated) = self.winding(g, quantum);
        let standing = self.well(g);
        FlowLanding {
            cell: g,
            face: rel,
            meeting_ratio: rel.meeting_ratio(),
            founds: rel.founds(),
            windings,
            radiated: fold_rad + radiated as u64,
            fed: quanta,
            standing,
            standing_delta: (standing as i64) - (before as i64),
        }
    }

    /// ★ THE FACE-WELL (W3 · THE EYES — the grey matter on the ONE pool; `FORMULA §X`, `THE_MAIN_NETWORK §II`).
    /// A face between two collocated constructions is A LANDING: the bond's composition (a higher blade) has its
    /// OWN swung place (`place::spiral` climbs and rotates by the SECOND constituent's length, so the ORDER of
    /// the two lives in the composition — `a→b` and `b→a` land at DISTINCT grips: **direction is the worldline's
    /// own, never a stored successor word**, the `W_FORWARD` retirement held), and its coherence-mass is a WELL
    /// at that grip in the SAME pool under the SAME one-word law. No face-table, no adjacency slots, no second
    /// region, no new layout — the grey matter is wells standing at composition grips, and the coherence of a
    /// directed pair is READ BY PLACEMENT (`well_of` at the composition's grip — place-not-search, O(1) by
    /// construction, never a scan).
    pub fn relate(
        &mut self,
        from: Node,
        to: Node,
        frame: Place,
        quanta: u32,
        quantum: u32,
    ) -> FlowLanding {
        let (_mol, rel) = bond(from, to, frame);
        let g = face_grip_of(from, to, self.axis);
        let before = self.well(g);
        let fold_rad = self.feed(g, quanta, quantum);
        let (windings, radiated) = self.winding(g, quantum);
        let standing = self.well(g);
        FlowLanding {
            cell: g,
            face: rel,
            meeting_ratio: rel.meeting_ratio(),
            founds: rel.founds(),
            windings,
            radiated: fold_rad + radiated as u64,
            fed: quanta,
            standing,
            standing_delta: (standing as i64) - (before as i64),
        }
    }

    /// the face GRIP of a directed pair — where the face `from→to` stands: place-not-search.
    #[inline]
    pub fn face_grip(&self, from: Node, to: Node) -> Grip {
        face_grip_of(from, to, self.axis)
    }
}

/// ★ THE TWO-REGION MEDIUM (`FORMULA §XXVIII` — the cone made structural; the FELT SERIES the shared
/// terrain, `LEDGER` 2026-07-09). The body reads its terrain as PRE-LIGHT STANDING ⊕ ITS OWN DEPOSITS:
/// two `FORM_WORDS`-strided regions of the SAME geometry (`medium::RegionalForm` per cell). The cone at
/// a grip is the JOIN of the two felt series (`§XXVIII`: a lineage's past cone is the pre-light form ⊕
/// its own worldline, read immediately); DEPOSITS go to `own` ONLY — the own region is THE SPOOL,
/// place-indexed, no lists (place-not-store). The flow/sweep word is gone from this path: the arc's
/// re-base lives on inside `RegionalForm`'s own Cogs (`law.rs` stays as history for `Manifold`).
/// THE REGISTER'S BOUNDARY SEAM (`FORMULA §XXXII-c`). The lineage-local chart is born at rank
/// zero and widens at its own occupancy register's carry events. The body cannot allocate — the
/// widened storage is the boundary's to supply — but the MAPPING is the law's: an impl MUST move
/// cells with `zero_extend_own_cells` and nothing else. The seam is ours and gauge: the same next
/// deposit cannot tell which impl supplied the words.
pub trait OwnRecast {
    fn words(&self) -> &[u32];
    fn words_mut(&mut self) -> &mut [u32];
    /// Re-cast the chart to `new_axis`: allocate fresh zeroed storage of
    /// `new_axis² · OWN_CELL_WORDS` and move every live cell with the law's mapping —
    /// `zero_extend_own_cells` when widening, `narrow_own_cells` when the digit retires
    /// (`new_axis < old_axis`; the body has already verified the survivors are section-clean).
    fn recast(&mut self, old_axis: i64, new_axis: i64);
}

/// Move every live founded cell of `old` (at `old_axis`) into `new` (at `new_axis`) by the
/// ratified zero-extension (`§XXXII-b`): the grip gains its new digits at zero, the cell's
/// founding construction and ordered form cross byte-whole, and merged history stays merged.
/// No founder is re-grounded — the dyadic section guarantees a moved cell can never collide
/// with a genuinely new fine arrival whose coarse cell was UNBORN.
pub fn zero_extend_own_cells(old: &[u32], new: &mut [u32], old_axis: i64, new_axis: i64) {
    let old_cells = old_axis as usize * old_axis as usize;
    debug_assert!(old.len() >= old_cells * OWN_CELL_WORDS);
    debug_assert!(new.len() >= new_axis as usize * new_axis as usize * OWN_CELL_WORDS);
    let mut grip = 0usize;
    while grip < old_cells {
        let at = grip * OWN_CELL_WORDS;
        if old[at + OWN_CELL_LIVE] != 0 {
            let moved =
                crate::chart::zero_extend_grip(grip as u32, old_axis as u32, new_axis as u32);
            let to = moved as usize * OWN_CELL_WORDS;
            new[to..to + OWN_CELL_WORDS].copy_from_slice(&old[at..at + OWN_CELL_WORDS]);
        }
        grip += 1;
    }
}

/// Move every live founded cell of `old` (at `old_axis`) into the NARROWER `new` (at `new_axis`)
/// by the exact inverse of the zero-extension. The caller has already verified every live grip is
/// section-clean at the retiring digit — the narrowing is lossless and byte-whole, never a merge.
/// The chart shrinks only when its surviving spread affords it (Brandon's ruling, 2026-07-10:
/// the machine occupies what it needs, and no more — a grower-only chart is a primitive knob).
pub fn narrow_own_cells(old: &[u32], new: &mut [u32], old_axis: i64, new_axis: i64) {
    let old_cells = old_axis as usize * old_axis as usize;
    debug_assert!(old.len() >= old_cells * OWN_CELL_WORDS);
    debug_assert!(new.len() >= new_axis as usize * new_axis as usize * OWN_CELL_WORDS);
    let mut grip = 0usize;
    while grip < old_cells {
        let at = grip * OWN_CELL_WORDS;
        if old[at + OWN_CELL_LIVE] != 0 {
            let moved =
                crate::chart::zero_extended_source(grip as u32, new_axis as u32, old_axis as u32)
                    .expect("a narrowing chart's live cells are section-clean");
            let to = moved as usize * OWN_CELL_WORDS;
            new[to..to + OWN_CELL_WORDS].copy_from_slice(&old[at..at + OWN_CELL_WORDS]);
        }
        grip += 1;
    }
}

#[inline]
fn own_chart_extent_is_formed(
    words_len: usize,
    cell_base: usize,
    capacity_cells: usize,
    old_axis: u32,
    new_axis: u32,
) -> Option<(usize, usize)> {
    if old_axis == 0 || new_axis == 0 || !old_axis.is_power_of_two() || !new_axis.is_power_of_two()
    {
        return None;
    }
    let old_cells = (old_axis as usize).checked_mul(old_axis as usize)?;
    let new_cells = (new_axis as usize).checked_mul(new_axis as usize)?;
    if old_cells > capacity_cells || new_cells > capacity_cells {
        return None;
    }
    let chart_words = capacity_cells.checked_mul(OWN_CELL_WORDS)?;
    let chart_end = cell_base.checked_add(chart_words)?;
    if chart_end > words_len {
        return None;
    }
    Some((old_cells, new_cells))
}

#[inline]
fn read_own_cell_with<S: WordSeam>(words: &[u32], at: usize) -> [u32; OWN_CELL_WORDS] {
    let mut row = [0u32; OWN_CELL_WORDS];
    let mut word = 0usize;
    while word < OWN_CELL_WORDS {
        row[word] = unsafe { S::read_u32_unchecked(words, at + word) };
        word += 1;
    }
    row
}

#[inline]
fn clear_own_cell_with<S: WordSeam>(words: &mut [u32], at: usize) {
    let mut word = 0usize;
    while word < OWN_CELL_WORDS {
        unsafe { S::store_u32_unchecked(words, at + word, 0) };
        word += 1;
    }
}

#[inline]
fn write_own_cell_with<S: WordSeam>(words: &mut [u32], at: usize, row: &[u32; OWN_CELL_WORDS]) {
    let mut word = 0usize;
    while word < OWN_CELL_WORDS {
        unsafe { S::store_u32_unchecked(words, at + word, row[word]) };
        word += 1;
    }
}

/// Recast one current's dense live chart into a wider dyadic hand inside a larger boundary
/// reservation. The reservation is only unused substrate surface: `old_axis` remains the body's
/// gauge until its own carry invokes this move. Descending source order is the exact overlap-safe
/// spelling of `(x,y) -> (scale·x, scale·y)`: every destination is at or above its source, so a
/// source is read before a lower source may land there. Every non-destination row in the new active
/// chart ends all-zero; the untouched reservation tail was and remains canonical zero.
///
/// `false` is a pre-mutation recast report. It never clips a cell or chooses a smaller chart. The
/// enclosing deed may already have changed other body faces, so its mounting must be discarded
/// unless a higher carried caller continuation has been built.
pub fn zero_extend_own_cells_in_place_with<S: WordSeam>(
    words: &mut [u32],
    cell_base: usize,
    capacity_cells: usize,
    old_axis: u32,
    new_axis: u32,
) -> bool {
    let Some((old_cells, new_cells)) =
        own_chart_extent_is_formed(words.len(), cell_base, capacity_cells, old_axis, new_axis)
    else {
        return false;
    };
    if new_axis <= old_axis || new_axis % old_axis != 0 {
        return false;
    }

    // The newly active tail has never belonged to the old chart. Clear it before any source can
    // land there; the old active prefix remains intact until the descending walk reaches it.
    let mut grip = old_cells;
    while grip < new_cells {
        clear_own_cell_with::<S>(words, cell_base + grip * OWN_CELL_WORDS);
        grip += 1;
    }

    grip = old_cells;
    while grip != 0 {
        grip -= 1;
        let from = cell_base + grip * OWN_CELL_WORDS;
        let row = read_own_cell_with::<S>(words, from);
        clear_own_cell_with::<S>(words, from);
        if row[OWN_CELL_LIVE] != 0 {
            let moved = crate::chart::zero_extend_grip(grip as u32, old_axis, new_axis) as usize;
            let to = cell_base + moved * OWN_CELL_WORDS;
            write_own_cell_with::<S>(words, to, &row);
        }
    }
    true
}

/// The overlap-safe inverse of `zero_extend_own_cells_in_place_with`. Ascending source order is
/// lawful because every inverse destination is at or below its source; an already-produced narrow
/// cell can never be cleared by a later wider source. The caller has already established that every
/// survivor is construction-clean on this section, exactly as `Medium::narrow_cascade` does.
pub fn narrow_own_cells_in_place_with<S: WordSeam>(
    words: &mut [u32],
    cell_base: usize,
    capacity_cells: usize,
    old_axis: u32,
    new_axis: u32,
) -> bool {
    let Some((old_cells, _new_cells)) =
        own_chart_extent_is_formed(words.len(), cell_base, capacity_cells, old_axis, new_axis)
    else {
        return false;
    };
    if new_axis >= old_axis || old_axis % new_axis != 0 {
        return false;
    }

    // Form the whole section before the first write. A malformed off-section survivor must never
    // turn a checked boundary rejection into a partially moved chart.
    let mut grip = 0usize;
    while grip < old_cells {
        let at = cell_base + grip * OWN_CELL_WORDS;
        if unsafe { S::read_u32_unchecked(words, at + OWN_CELL_LIVE) } != 0
            && crate::chart::zero_extended_source(grip as u32, new_axis, old_axis).is_none()
        {
            return false;
        }
        grip += 1;
    }

    grip = 0;
    let scale = old_axis / new_axis;
    while grip < old_cells {
        let from = cell_base + grip * OWN_CELL_WORDS;
        let row = read_own_cell_with::<S>(words, from);
        clear_own_cell_with::<S>(words, from);
        if row[OWN_CELL_LIVE] != 0 {
            let x = grip as u32 / old_axis;
            let y = grip as u32 - x * old_axis;
            let moved = (x / scale) * new_axis + y / scale;
            let to = cell_base + moved as usize * OWN_CELL_WORDS;
            write_own_cell_with::<S>(words, to, &row);
        }
        grip += 1;
    }
    true
}

/// One occupied receiver-standing cell.  A standing surface is the already-integrated regional
/// field at one declared chart grain; the complete contributing positions and incidence remain in
/// the carried cut topology beside it, so this quotient row retains only its derived grip and
/// RegionalForm.  Cells are sorted and unique in every admitted sparse receiver surface.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SparseStandingCell {
    grip: Grip,
    form: RegionalForm,
}

/// One exact read from a receiver-owned standing world.  `form` is the causal terrain face.  A
/// flat grip exists only where that world also has an exact historical `u32` chart projection;
/// it is listener compatibility and never required for conduct.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StandingContact {
    form: RegionalForm,
    flat_grip: Option<Grip>,
    receiver_rank: u64,
}

impl StandingContact {
    #[inline]
    const fn new(form: RegionalForm, flat_grip: Option<Grip>, receiver_rank: u64) -> Self {
        Self {
            form,
            flat_grip,
            receiver_rank,
        }
    }

    #[inline]
    pub const fn form(self) -> RegionalForm {
        self.form
    }

    #[inline]
    pub const fn flat_grip(self) -> Option<Grip> {
        self.flat_grip
    }

    #[inline]
    pub const fn receiver_rank(self) -> u64 {
        self.receiver_rank
    }
}

/// Body-owned mouth for an arbitrary receiver-standing surface. Implementations own their
/// chart/address species and return the exact form at the supplied Soma construction. `None` is
/// physical query refusal; `UNBORN` is the successful read of empty terrain. Thus a storage
/// failure can never masquerade as darkness. Allocation policy remains the receiver's physical
/// concern and must be declared by that implementation.
pub trait StandingQuery {
    fn receiver_rank(&self) -> u64;

    fn form_at_position(&self, position: Place) -> Option<RegionalForm>;

    /// Historical grip-addressed observer seam.  General conduct never calls this method.  A
    /// receiver without an exact flat projection returns `None` rather than inventing an inverse.
    fn form_at_flat_grip(&self, _grip: Grip) -> Option<RegionalForm> {
        None
    }
}

impl SparseStandingCell {
    #[inline]
    pub fn new(grip: Grip, form: RegionalForm) -> Option<Self> {
        form.occupied().then_some(Self { grip, form })
    }

    #[inline]
    pub fn grip(self) -> Grip {
        self.grip
    }

    #[inline]
    pub fn form(self) -> RegionalForm {
        self.form
    }
}

/// One occupied cell of the sparse REGISTER posture.  `position` is the whole founder and remains
/// invariant while only `grip` is re-cast between receiving gauges.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SparseOwnCell {
    grip: Grip,
    position: Place,
    form: RegionalForm,
}

/// Caller-owned sparse storage seam.  The body owns transition law and ordinals; a substrate owns
/// only physical growth.  Fixed slices and growable host/device page reservoirs can therefore
/// carry the same live topology without turning a worst-case deed envelope into mandatory
/// allocation.  A failed insert is a typed transaction refusal at the membrane, never a clipped
/// body state.
pub trait SparseOwnStorage {
    fn reset(&mut self) -> bool;
    fn as_slice(&self) -> &[SparseOwnCell];
    fn live_slice_mut(&mut self, live: usize) -> Option<&mut [SparseOwnCell]>;
    fn insert_at(&mut self, live: usize, at: usize, cell: SparseOwnCell) -> bool;
    fn remove_at(&mut self, live: usize, at: usize) -> bool;
}

/// Physical response when a live completion reaches beyond the currently mounted carrier.  A
/// growable host substrate may add the exact missing enclosure; a fixed compatibility row retains
/// the historical retirement face; allocation refusal aborts the disposable successor rather than
/// turning unavailable storage into a body event.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum CarrierGrowth {
    Present,
    FixedBoundary,
    Refused,
}

/// Substrate-owned vertical carrier storage.  The body asks only for the depth reached by an
/// actual climbing brick.  No forecast depth, source modality, or authored maximum enters.
pub trait CarrierStorage {
    fn words(&self) -> &[u32];
    fn words_mut(&mut self) -> &mut [u32];
    fn ensure_depth(&mut self, depth: usize) -> CarrierGrowth;

    /// Exact co-present arrivals which do not fit the historical flat REGISTER row.  These are
    /// still part of the live enclosure; they are not a cache, observer index, or later replay.
    /// Fixed/card compatibility stores leave this surface empty and retain their declared row
    /// physics. A production store must keep every admitted node until body law encloses it.
    fn co_present_overflow_len(&self, _depth: usize) -> usize {
        0
    }

    fn co_present_overflow_node(&self, _depth: usize, _at: usize) -> Option<Node> {
        None
    }

    fn append_co_present_overflow(&mut self, _depth: usize, _node: Node) -> CarrierGrowth {
        CarrierGrowth::FixedBoundary
    }

    /// Release event-local arrivals whose construction has just enclosed. The enclosure's carried
    /// stance/flywheel and the emitted higher-grain brick remain; only constituents which no longer
    /// factor independently into that continuation depart.
    fn clear_co_present_overflow(&mut self, _depth: usize) -> CarrierGrowth {
        CarrierGrowth::Present
    }

    /// Whether the historical fixed/card enclosure rows describe the complete live carrier.
    /// Generalized stores return false as soon as exact state exists outside that projection.
    fn legacy_projection_complete(&self) -> bool {
        true
    }
}

enum CarrierStore<'a> {
    Fixed(&'a mut [u32]),
    Growing(&'a mut dyn CarrierStorage),
}

impl CarrierStore<'_> {
    fn words(&self) -> &[u32] {
        match self {
            Self::Fixed(words) => words,
            Self::Growing(storage) => storage.words(),
        }
    }

    fn words_mut(&mut self) -> &mut [u32] {
        match self {
            Self::Fixed(words) => words,
            Self::Growing(storage) => storage.words_mut(),
        }
    }

    fn ensure_depth(&mut self, depth: usize) -> CarrierGrowth {
        match self {
            Self::Fixed(words) if words.len() / ENCLOSURE_WORDS >= depth => CarrierGrowth::Present,
            Self::Fixed(_) => CarrierGrowth::FixedBoundary,
            Self::Growing(storage) => storage.ensure_depth(depth),
        }
    }

    fn co_present_overflow_len(&self, depth: usize) -> usize {
        match self {
            Self::Fixed(_) => 0,
            Self::Growing(storage) => storage.co_present_overflow_len(depth),
        }
    }

    fn co_present_overflow_node(&self, depth: usize, at: usize) -> Option<Node> {
        match self {
            Self::Fixed(_) => None,
            Self::Growing(storage) => storage.co_present_overflow_node(depth, at),
        }
    }

    fn legacy_projection_complete(&self) -> bool {
        match self {
            Self::Fixed(_) => true,
            Self::Growing(storage) => storage.legacy_projection_complete(),
        }
    }

    fn release_co_present(&mut self, depth: usize, enclosure: &mut Enclosure) -> CarrierGrowth {
        let cleared = match self {
            Self::Fixed(_) => CarrierGrowth::Present,
            Self::Growing(storage) => storage.clear_co_present_overflow(depth),
        };
        if cleared != CarrierGrowth::Present {
            return cleared;
        }
        enclosure.register = [absent_node(); REGISTER as usize];
        enclosure.head = 0;
        enclosure.live = 0;
        CarrierGrowth::Present
    }

    /// Admit one arrival into the complete live aperture. Historical fixed/card rows retain their
    /// exact ring behavior. The generalized growable posture fills that byte-exact prefix once,
    /// then grows outside it rather than overwriting an earlier co-present relation.
    fn admit_co_present(
        &mut self,
        depth: usize,
        enclosure: &mut Enclosure,
        node: Node,
    ) -> CarrierGrowth {
        if enclosure.live < REGISTER as usize {
            let head = enclosure.head;
            enclosure.register[head] = node;
            enclosure.head = (head + 1) % (REGISTER as usize);
            enclosure.live += 1;
            return CarrierGrowth::Present;
        }
        match self {
            Self::Fixed(_) => {
                let head = enclosure.head;
                enclosure.register[head] = node;
                enclosure.head = (head + 1) % (REGISTER as usize);
                CarrierGrowth::Present
            }
            Self::Growing(storage) => storage.append_co_present_overflow(depth, node),
        }
    }
}

impl SparseOwnStorage for [SparseOwnCell] {
    fn reset(&mut self) -> bool {
        for cell in self.iter_mut() {
            *cell = SparseOwnCell::EMPTY;
        }
        true
    }

    fn as_slice(&self) -> &[SparseOwnCell] {
        self
    }

    fn live_slice_mut(&mut self, live: usize) -> Option<&mut [SparseOwnCell]> {
        self.get_mut(..live)
    }

    fn insert_at(&mut self, live: usize, at: usize, cell: SparseOwnCell) -> bool {
        if live >= self.len() || at > live {
            return false;
        }
        self.copy_within(at..live, at + 1);
        self[at] = cell;
        true
    }

    fn remove_at(&mut self, live: usize, at: usize) -> bool {
        if live == 0 || live > self.len() || at >= live {
            return false;
        }
        self.copy_within(at + 1..live, at);
        self[live - 1] = SparseOwnCell::EMPTY;
        true
    }
}

impl SparseOwnCell {
    pub const EMPTY: SparseOwnCell = SparseOwnCell {
        grip: 0,
        position: (Cog::ZERO, Cog::ZERO),
        form: RegionalForm::UNBORN,
    };

    #[inline]
    pub fn grip(self) -> Grip {
        self.grip
    }

    #[inline]
    pub fn position(self) -> Place {
        self.position
    }

    #[inline]
    pub fn form(self) -> RegionalForm {
        self.form
    }
}

/// Exact post-deposit posture of one accepted deed.  This is a boundary receipt: it lets a sparse
/// membrane retain the live grip population while the REGISTER breathes, without scanning a dense
/// chart or feeding an address back into the deposit law.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FeltDeposit {
    pub grip: Grip,
    pub axis: u32,
    pub live: bool,
}

/// Allocation-free sparse storage state for the body's own REGISTER deposit law.  The caller owns
/// the complete `cells` reservation.  Only `cells[..live]` participate, kept in exact grip order;
/// no operation allocates or visits `axis²`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct SparseOwnState {
    register: crate::chart::Register,
    live: usize,
    releases: u64,
    narrows: u64,
}

impl SparseOwnState {
    /// Form a new rank-zero sparse surface over one complete physical deed reservation.  Capacity
    /// is derived from the admitted transaction; rejecting an unrepresentable gauge here occurs
    /// before any body mutation.
    pub fn preflight<S: SparseOwnStorage + ?Sized>(storage: &mut S) -> Option<Self> {
        storage.reset().then_some(())?;
        Some(Self {
            register: crate::chart::Register {
                axis: 1,
                occupancy: 0,
            },
            live: 0,
            releases: 0,
            narrows: 0,
        })
    }

    #[inline]
    pub fn axis(self) -> u32 {
        self.register.axis
    }

    #[inline]
    pub fn occupancy(self) -> u64 {
        self.register.occupancy
    }

    #[inline]
    pub fn breath(self) -> (u64, u64) {
        (self.releases, self.narrows)
    }

    #[inline]
    pub fn cells<'a, S: SparseOwnStorage + ?Sized>(
        self,
        storage: &'a S,
    ) -> Option<&'a [SparseOwnCell]> {
        storage.as_slice().get(..self.live)
    }

    #[inline]
    fn find(self, cells: &[SparseOwnCell], grip: Grip) -> Result<usize, usize> {
        cells[..self.live].binary_search_by_key(&grip, |cell| cell.grip)
    }

    #[inline]
    fn form_at<S: SparseOwnStorage + ?Sized>(self, storage: &S, grip: Grip) -> RegionalForm {
        self.find(storage.as_slice(), grip)
            .ok()
            .map(|at| storage.as_slice()[at].form)
            .unwrap_or(RegionalForm::UNBORN)
    }

    /// Deposit one exact construction/term through the same REGISTER arrival, alias,
    /// annihilation, and retirement law used by live Eros.  `None` is a preflight-contract or
    /// topology violation; a correctly reserved surface cannot refuse after conduct begins.
    pub fn deposit_term<S: SparseOwnStorage + ?Sized>(
        &mut self,
        storage: &mut S,
        position: Place,
        term: FeltTerm,
    ) -> Option<FeltDeposit> {
        if self.live > storage.as_slice().len() || self.register.occupancy != self.live as u64 {
            return None;
        }
        let mut grip = place::ground(position, self.register.axis as i64);
        if self.find(storage.as_slice(), grip).is_err() {
            loop {
                let (next, carried) = self.register.arrive();
                if !carried {
                    self.register = next;
                    break;
                }
                let old_axis = self.register.axis;
                let new_axis = old_axis.checked_mul(2)?;
                if sparse_axis_is_representable(new_axis).is_none() {
                    return None;
                }
                for cell in storage.live_slice_mut(self.live)? {
                    cell.grip = crate::chart::zero_extend_grip(cell.grip, old_axis, new_axis);
                }
                self.register = self.register.digit();
                grip = place::ground(position, new_axis as i64);
                if self.find(storage.as_slice(), grip).is_ok() {
                    break;
                }
            }
        }

        let existing = self.find(storage.as_slice(), grip).ok();
        let prior = existing
            .map(|at| storage.as_slice()[at].form)
            .unwrap_or(RegionalForm::UNBORN);
        let form = prior.deposit(term);
        let (same, other) = form.resultant();
        let (this_way, that_way) = form.fiber();
        let releases = same.mag == 0
            && other.mag == 0
            && this_way == crate::num::Rung::ZERO
            && that_way == crate::num::Rung::ZERO;

        let live = if releases {
            if let Some(at) = existing {
                if !storage.remove_at(self.live, at) {
                    return None;
                }
                self.live -= 1;
            }
            let (register, _) = self.register.depart();
            self.register = register;
            self.releases += 1;
            self.narrow(storage)?;
            false
        } else if let Some(at) = existing {
            storage.live_slice_mut(self.live)?[at].form = form;
            true
        } else {
            let at = self.find(storage.as_slice(), grip).unwrap_err();
            if !storage.insert_at(
                self.live,
                at,
                SparseOwnCell {
                    grip,
                    position,
                    form,
                },
            ) {
                return None;
            }
            self.live += 1;
            true
        };
        if self.register.occupancy != self.live as u64 {
            return None;
        }
        Some(FeltDeposit {
            grip: place::ground(position, self.register.axis as i64),
            axis: self.register.axis,
            live,
        })
    }

    fn narrow<S: SparseOwnStorage + ?Sized>(&mut self, storage: &mut S) -> Option<()> {
        loop {
            if self.register.axis <= 1 {
                return Some(());
            }
            let new_axis = self.register.axis >> 1;
            let tooth = crate::chart::hand(new_axis);
            if self.register.occupancy & !(tooth - 1) != 0 {
                return Some(());
            }
            for cell in self.cells(storage)? {
                if crate::chart::zero_extended_source(cell.grip, new_axis, self.register.axis)
                    != Some(place::ground(cell.position, new_axis as i64))
                {
                    return Some(());
                }
            }
            for cell in storage.live_slice_mut(self.live)? {
                cell.grip =
                    crate::chart::zero_extended_source(cell.grip, new_axis, self.register.axis)?;
            }
            self.register = self.register.digit_retired();
            self.narrows += 1;
        }
    }
}

#[inline]
fn sparse_axis_is_representable(axis: u32) -> Option<()> {
    let cells = (axis as u64).checked_mul(axis as u64)?;
    (cells <= Grip::MAX as u64 + 1).then_some(())
}

/// Physical or structural refusal at the arbitrary-rank current-local OWN mouth. `UNBORN` is not
/// an error; it is the exact successful read of an unoccupied local address.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RankedOwnError {
    Geometry,
    Topology,
    ResourceExtent,
    ResourceReservation,
    Poisoned,
}

/// Result of trying to found one genuinely unoccupied ranked address. A carry is the enacted
/// chart digit itself: no cell or occupancy increment has committed yet.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RankedFoundEdge {
    Inserted,
    Carry,
}

/// Source-neutral cell face exposed only for exact testimony and transport across a boundary.
/// The substrate's ranked address remains its own physical representation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RankedOwnCellFace {
    pub founder: Place,
    pub form: RegionalForm,
}

/// Substrate mouth for the ceiling-free current-local chart. The body owns arrive, carry, alias,
/// annihilation, and retirement order. The substrate owns only exact ranked address material,
/// fallible growth, and an arbitrary-width occupancy population.
pub trait RankedOwnStorage {
    fn reset(&mut self) -> Result<(), RankedOwnError>;
    fn form_at_position(&self, rank: u64, position: Place) -> Result<RegionalForm, RankedOwnError>;
    fn try_found(
        &mut self,
        rank: u64,
        position: Place,
        form: RegionalForm,
    ) -> Result<RankedFoundEdge, RankedOwnError>;
    fn replace(
        &mut self,
        rank: u64,
        position: Place,
        expected: RegionalForm,
        replacement: RegionalForm,
    ) -> Result<(), RankedOwnError>;
    fn release(
        &mut self,
        rank: u64,
        position: Place,
        expected: RegionalForm,
    ) -> Result<(), RankedOwnError>;
    fn zero_extend(&mut self, old_rank: u64, new_rank: u64) -> Result<(), RankedOwnError>;
    fn occupancy_below_hand(&self, retiring_rank: u64) -> Result<bool, RankedOwnError>;
    fn founders_in_zero_section(
        &self,
        old_rank: u64,
        new_rank: u64,
    ) -> Result<bool, RankedOwnError>;
    fn zero_section(&mut self, old_rank: u64, new_rank: u64) -> Result<(), RankedOwnError>;
    fn occupancy_words(&self) -> &[u64];
    fn cell_count(&self) -> usize;
    fn cell_face(&self, at: usize) -> Option<RankedOwnCellFace>;
}

/// Post-deed face of the ceiling-free OWN chart. The ranked address itself remains in the storage
/// which enacted it; no flat grip is manufactured for this receipt.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RankedFeltDeposit {
    pub rank: u64,
    pub live: bool,
}

/// Body-owned law for one arbitrary-rank current-local OWN population. Any physical refusal
/// poisons the disposable successor: no later deed may read or emit from a partial current.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct RankedOwnState {
    rank: u64,
    releases: u64,
    narrows: u64,
    poisoned: bool,
}

impl RankedOwnState {
    pub fn preflight<S: RankedOwnStorage + ?Sized>(
        storage: &mut S,
    ) -> Result<Self, RankedOwnError> {
        storage.reset()?;
        Ok(Self {
            rank: 0,
            releases: 0,
            narrows: 0,
            poisoned: false,
        })
    }

    #[inline]
    pub const fn rank(self) -> u64 {
        self.rank
    }

    #[inline]
    pub const fn breath(self) -> (u64, u64) {
        (self.releases, self.narrows)
    }

    #[inline]
    pub const fn poisoned(self) -> bool {
        self.poisoned
    }

    fn refuse<T>(&mut self, error: RankedOwnError) -> Result<T, RankedOwnError> {
        self.poisoned = true;
        Err(error)
    }

    fn storage<T>(&mut self, result: Result<T, RankedOwnError>) -> Result<T, RankedOwnError> {
        match result {
            Ok(value) => Ok(value),
            Err(error) => self.refuse(error),
        }
    }

    pub fn form_at<S: RankedOwnStorage + ?Sized>(
        &mut self,
        storage: &S,
        position: Place,
    ) -> Result<RegionalForm, RankedOwnError> {
        if self.poisoned {
            return Err(RankedOwnError::Poisoned);
        }
        self.storage(storage.form_at_position(self.rank, position))
    }

    pub fn deposit_term<S: RankedOwnStorage + ?Sized>(
        &mut self,
        storage: &mut S,
        position: Place,
        term: FeltTerm,
    ) -> Result<RankedFeltDeposit, RankedOwnError> {
        if self.poisoned {
            return Err(RankedOwnError::Poisoned);
        }
        loop {
            let rank = self.rank;
            let prior = self.storage(storage.form_at_position(rank, position))?;
            let form = prior.deposit(term);
            let (same, other) = form.resultant();
            let (this_way, that_way) = form.fiber();
            let releases = same.mag == 0
                && other.mag == 0
                && this_way == crate::num::Rung::ZERO
                && that_way == crate::num::Rung::ZERO;

            if !prior.occupied() {
                if releases || !form.occupied() {
                    return Ok(RankedFeltDeposit { rank, live: false });
                }
                match self.storage(storage.try_found(rank, position, form))? {
                    RankedFoundEdge::Inserted => {
                        return Ok(RankedFeltDeposit { rank, live: true });
                    }
                    RankedFoundEdge::Carry => {
                        let new_rank = match rank.checked_add(1) {
                            Some(rank) => rank,
                            None => return self.refuse(RankedOwnError::ResourceExtent),
                        };
                        self.storage(storage.zero_extend(rank, new_rank))?;
                        self.rank = new_rank;
                        // Re-read at the enacted gauge. A previously distinct arrival may now be
                        // the kin of carried history and must deepen without incrementing.
                        continue;
                    }
                }
            }

            if releases {
                self.storage(storage.release(rank, position, prior))?;
                self.releases = match self.releases.checked_add(1) {
                    Some(value) => value,
                    None => return self.refuse(RankedOwnError::ResourceExtent),
                };
                self.narrow(storage)?;
                return Ok(RankedFeltDeposit {
                    rank: self.rank,
                    live: false,
                });
            }

            self.storage(storage.replace(rank, position, prior, form))?;
            return Ok(RankedFeltDeposit { rank, live: true });
        }
    }

    fn narrow<S: RankedOwnStorage + ?Sized>(
        &mut self,
        storage: &mut S,
    ) -> Result<(), RankedOwnError> {
        while self.rank != 0 {
            let old_rank = self.rank;
            let new_rank = old_rank - 1;
            if !self.storage(storage.occupancy_below_hand(new_rank))?
                || !self.storage(storage.founders_in_zero_section(old_rank, new_rank))?
            {
                return Ok(());
            }
            self.storage(storage.zero_section(old_rank, new_rank))?;
            self.rank = new_rank;
            self.narrows = match self.narrows.checked_add(1) {
                Some(value) => value,
                None => return self.refuse(RankedOwnError::ResourceExtent),
            };
        }
        Ok(())
    }
}

/// The OWN chart's three lawful postures (`§XXXII` ethos): a bounded gate's DECLARED grain, the
/// historical dense REGISTER parity species, or the allocation-free sparse REGISTER production
/// surface.  Both REGISTER species obey the same body-owned transition law.
enum OwnStore<'a> {
    Declared(&'a mut [u32]),
    Register(&'a mut dyn OwnRecast),
    Sparse {
        cells: &'a mut [SparseOwnCell],
        state: SparseOwnState,
    },
    SparseStorage {
        storage: &'a mut dyn SparseOwnStorage,
        state: SparseOwnState,
    },
    RankedStorage {
        storage: &'a mut dyn RankedOwnStorage,
        state: RankedOwnState,
    },
}

enum StandingStore<'a> {
    Dense {
        words: &'a [u32],
        axis: i64,
    },
    Sparse {
        cells: &'a [SparseStandingCell],
        axis: i64,
    },
    Query(&'a dyn StandingQuery),
}

impl StandingStore<'_> {
    #[inline]
    fn receiver_rank(&self) -> u64 {
        match self {
            Self::Dense { axis, .. } | Self::Sparse { axis, .. } => {
                (*axis as u64).trailing_zeros() as u64
            }
            Self::Query(query) => query.receiver_rank(),
        }
    }

    #[inline]
    fn flat_grip_at(&self, position: Place) -> Option<Grip> {
        let rank = self.receiver_rank();
        if rank > 16 {
            return None;
        }
        Some(place::ground(position, 1i64 << rank))
    }

    #[inline]
    fn form_at_flat_grip(&self, grip: Grip) -> Option<RegionalForm> {
        match self {
            Self::Dense { words, .. } => {
                let at = grip as usize * FORM_WORDS;
                if at + FORM_WORDS <= words.len() {
                    Some(RegionalForm::unpack(words, at))
                } else {
                    Some(RegionalForm::UNBORN)
                }
            }
            Self::Sparse { cells, .. } => Some(
                cells
                    .binary_search_by_key(&grip, |cell| cell.grip)
                    .ok()
                    .map(|at| cells[at].form)
                    .unwrap_or(RegionalForm::UNBORN),
            ),
            Self::Query(query) => query.form_at_flat_grip(grip),
        }
    }

    #[inline]
    fn contact_at(&self, position: Place) -> Option<StandingContact> {
        let rank = self.receiver_rank();
        let flat_grip = self.flat_grip_at(position);
        let form = match self {
            Self::Dense { .. } | Self::Sparse { .. } => self.form_at_flat_grip(flat_grip?)?,
            Self::Query(query) => query.form_at_position(position)?,
        };
        Some(StandingContact::new(form, flat_grip, rank))
    }

    fn sparse_is_canonical(cells: &[SparseStandingCell], axis: i64) -> bool {
        if axis <= 0 || axis & (axis - 1) != 0 || axis > u32::MAX as i64 {
            return false;
        }
        let extent = (axis as u64).checked_mul(axis as u64);
        let Some(extent) = extent else {
            return false;
        };
        let mut previous = None;
        for cell in cells {
            if !cell.form.occupied()
                || cell.grip as u64 >= extent
                || previous.is_some_and(|grip| grip >= cell.grip)
            {
                return false;
            }
            previous = Some(cell.grip);
        }
        true
    }
}

struct Medium<'a> {
    standing: StandingStore<'a>,
    own: OwnStore<'a>,
    own_axis: i64,
    founded_cells: bool,
    register: crate::chart::Register,
    /// THE BREATH'S BOUNDARY FACE (instrument only — never a body input): how many cells
    /// released on exact annihilation and how many digits retired this current. The arithmetic
    /// experiment convicted the silent breath: an event with no boundary face cannot be read.
    releases: u64,
    narrows: u64,
    resource_refused: bool,
}

impl<'a> Medium<'a> {
    #[inline]
    fn own(&self) -> &[u32] {
        match &self.own {
            OwnStore::Declared(words) => words,
            OwnStore::Register(chart) => chart.words(),
            OwnStore::Sparse { .. }
            | OwnStore::SparseStorage { .. }
            | OwnStore::RankedStorage { .. } => &[],
        }
    }

    #[inline]
    fn own_mut(&mut self) -> &mut [u32] {
        match &mut self.own {
            OwnStore::Declared(words) => words,
            OwnStore::Register(chart) => chart.words_mut(),
            OwnStore::Sparse { .. }
            | OwnStore::SparseStorage { .. }
            | OwnStore::RankedStorage { .. } => {
                unreachable!("sparse OWN writes cross SparseOwnState, never the dense word seam")
            }
        }
    }

    #[inline]
    fn over(standing: &'a [u32], own: &'a mut [u32], axis: i64) -> Medium<'a> {
        Medium {
            standing: StandingStore::Dense {
                words: standing,
                axis,
            },
            own: OwnStore::Declared(own),
            own_axis: axis,
            founded_cells: false,
            register: crate::chart::Register {
                axis: axis as u32,
                occupancy: 0,
            },
            releases: 0,
            narrows: 0,
            resource_refused: false,
        }
    }

    /// A non-Cartesian first-person chart: standing and this lineage's OWN construction declare
    /// their grains separately. Each OWN cell carries its founding position beside its ordered
    /// RegionalForm, so the receiving edge re-grounds construction rather than consulting a key.
    #[inline]
    fn over_resident(
        standing: &'a [u32],
        own: &'a mut [u32],
        standing_axis: i64,
        own_axis: i64,
    ) -> Medium<'a> {
        Medium {
            standing: StandingStore::Dense {
                words: standing,
                axis: standing_axis,
            },
            own: OwnStore::Declared(own),
            own_axis,
            founded_cells: true,
            register: crate::chart::Register {
                axis: own_axis as u32,
                occupancy: 0,
            },
            releases: 0,
            narrows: 0,
            resource_refused: false,
        }
    }

    /// THE REGISTER POSTURE (`§XXXII-c`): the lineage chart born at the uncommitted rank-zero
    /// seed. Every genuinely new grip is an arrive event; the increment that carries into the
    /// rank's top tooth widens the chart through the boundary seam, and the arriving contact
    /// grounds at the new hand.
    #[inline]
    fn over_register(
        standing: &'a [u32],
        own: &'a mut dyn OwnRecast,
        standing_axis: i64,
    ) -> Medium<'a> {
        Medium {
            standing: StandingStore::Dense {
                words: standing,
                axis: standing_axis,
            },
            own: OwnStore::Register(own),
            own_axis: 1,
            founded_cells: true,
            register: crate::chart::Register {
                axis: 1,
                occupancy: 0,
            },
            releases: 0,
            narrows: 0,
            resource_refused: false,
        }
    }

    /// The production REGISTER posture over caller-reserved live cells.  The body owns every
    /// transition while storage remains proportional to the maximum admitted deed population.
    #[inline]
    fn over_sparse(
        standing: &'a [u32],
        cells: &'a mut [SparseOwnCell],
        standing_axis: i64,
    ) -> Option<Medium<'a>> {
        let state = SparseOwnState::preflight(cells)?;
        Some(Medium {
            standing: StandingStore::Dense {
                words: standing,
                axis: standing_axis,
            },
            own: OwnStore::Sparse { cells, state },
            own_axis: 1,
            founded_cells: true,
            register: crate::chart::Register {
                axis: 1,
                occupancy: 0,
            },
            releases: 0,
            narrows: 0,
            resource_refused: false,
        })
    }

    #[inline]
    fn over_sparse_storage(
        standing: &'a [u32],
        storage: &'a mut dyn SparseOwnStorage,
        standing_axis: i64,
    ) -> Option<Medium<'a>> {
        let state = SparseOwnState::preflight(storage)?;
        Some(Medium {
            standing: StandingStore::Dense {
                words: standing,
                axis: standing_axis,
            },
            own: OwnStore::SparseStorage { storage, state },
            own_axis: 1,
            founded_cells: true,
            register: crate::chart::Register {
                axis: 1,
                occupancy: 0,
            },
            releases: 0,
            narrows: 0,
            resource_refused: false,
        })
    }

    #[inline]
    fn over_sparse_standing(
        standing: &'a [SparseStandingCell],
        cells: &'a mut [SparseOwnCell],
        standing_axis: i64,
    ) -> Option<Medium<'a>> {
        if !StandingStore::sparse_is_canonical(standing, standing_axis) {
            return None;
        }
        let state = SparseOwnState::preflight(cells)?;
        Some(Medium {
            standing: StandingStore::Sparse {
                cells: standing,
                axis: standing_axis,
            },
            own: OwnStore::Sparse { cells, state },
            own_axis: 1,
            founded_cells: true,
            register: crate::chart::Register {
                axis: 1,
                occupancy: 0,
            },
            releases: 0,
            narrows: 0,
            resource_refused: false,
        })
    }

    #[inline]
    fn over_sparse_world_storage(
        standing: &'a [SparseStandingCell],
        storage: &'a mut dyn SparseOwnStorage,
        standing_axis: i64,
    ) -> Option<Medium<'a>> {
        if !StandingStore::sparse_is_canonical(standing, standing_axis) {
            return None;
        }
        let state = SparseOwnState::preflight(storage)?;
        Some(Medium {
            standing: StandingStore::Sparse {
                cells: standing,
                axis: standing_axis,
            },
            own: OwnStore::SparseStorage { storage, state },
            own_axis: 1,
            founded_cells: true,
            register: crate::chart::Register {
                axis: 1,
                occupancy: 0,
            },
            releases: 0,
            narrows: 0,
            resource_refused: false,
        })
    }

    /// General standing-world posture.  The receiver owns its chart and answers directly at the
    /// Soma construction; no flat grip or materialized axis crosses this mouth.
    #[inline]
    fn over_standing_query_storage(
        standing: &'a dyn StandingQuery,
        storage: &'a mut dyn SparseOwnStorage,
    ) -> Option<Medium<'a>> {
        let state = SparseOwnState::preflight(storage)?;
        Some(Medium {
            standing: StandingStore::Query(standing),
            own: OwnStore::SparseStorage { storage, state },
            own_axis: 1,
            founded_cells: true,
            register: crate::chart::Register {
                axis: 1,
                occupancy: 0,
            },
            releases: 0,
            narrows: 0,
            resource_refused: false,
        })
    }

    /// Complete production posture: arbitrary receiver-standing geometry and arbitrary-rank
    /// current-local OWN share one source-neutral construction mouth. No flat chart is formed.
    #[inline]
    fn over_standing_query_ranked_storage(
        standing: &'a dyn StandingQuery,
        storage: &'a mut dyn RankedOwnStorage,
    ) -> Option<Medium<'a>> {
        let state = RankedOwnState::preflight(storage).ok()?;
        Some(Medium {
            standing: StandingStore::Query(standing),
            own: OwnStore::RankedStorage { storage, state },
            // Historical fields remain exact only for historical postures. Production callers
            // read `own_rank` and the storage's occupancy limbs instead.
            own_axis: 1,
            founded_cells: true,
            register: crate::chart::Register {
                axis: 1,
                occupancy: 0,
            },
            releases: 0,
            narrows: 0,
            resource_refused: false,
        })
    }

    /// Exact historical flat projection of a swung place, when the receiver supplies one.
    #[inline]
    fn flat_grip(&self, p: Place) -> Option<Grip> {
        self.standing.flat_grip_at(p)
    }

    /// PLACE a construction at its grip (place-not-store).
    #[inline]
    fn place(&self, bytes: &[u8]) -> Option<Grip> {
        self.flat_grip(wind(bytes))
    }

    /// ★ THE CONE at a grip (`§XXVIII`) — the reader's whole past cone: PRE-LIGHT STANDING joined with
    /// ITS OWN DEPOSITS. A grip past either reservation reads the UNBORN place (the boundary guard, not
    /// a panic — the same inert crossing the pool word had).
    #[inline]
    fn cone(&self, g: Grip) -> RegionalForm {
        let at = (g as usize) * FORM_WORDS;
        if self.founded_cells || at + FORM_WORDS > self.own().len() {
            return RegionalForm::UNBORN;
        }
        self.standing
            .form_at_flat_grip(g)
            .unwrap_or(RegionalForm::UNBORN)
            .join(RegionalForm::unpack(self.own(), at))
    }

    /// Read one cast in both frames of the past cone. Standing is addressed at the receiving body's
    /// grain; OWN is addressed at this lineage's reservation grain. The same construction selects
    /// both directly, so neither chart stores or searches for an address.
    #[inline]
    fn cone_at(&mut self, position: Place) -> (Option<Grip>, RegionalForm, RegionalForm, u64) {
        let Some(contact) = self.standing.contact_at(position) else {
            self.resource_refused = true;
            return (None, RegionalForm::UNBORN, RegionalForm::UNBORN, 0);
        };
        let standing = contact.form();
        let ranked = match &mut self.own {
            OwnStore::RankedStorage { storage, state } => {
                match state.form_at(&**storage, position) {
                    Ok(form) => Some(form),
                    Err(_) => {
                        self.resource_refused = true;
                        return (None, RegionalForm::UNBORN, RegionalForm::UNBORN, 0);
                    }
                }
            }
            _ => None,
        };
        let own_grip = if ranked.is_none() {
            Some(place::ground(position, self.own_axis))
        } else {
            None
        };
        let sparse = match (&self.own, own_grip) {
            (OwnStore::Sparse { cells, state }, Some(grip)) => Some(state.form_at(&**cells, grip)),
            (OwnStore::SparseStorage { storage, state }, Some(grip)) => {
                Some(state.form_at(&**storage, grip))
            }
            _ => None,
        };
        let own = if let Some(form) = ranked.or(sparse) {
            form
        } else if self.founded_cells {
            let own_grip = own_grip.expect("only flat founded cells reach the flat word seam");
            let at = own_grip as usize * OWN_CELL_WORDS;
            if at + OWN_CELL_WORDS <= self.own().len() && self.own()[at + OWN_CELL_LIVE] != 0 {
                RegionalForm::unpack(self.own(), at + OWN_CELL_FORM)
            } else {
                RegionalForm::UNBORN
            }
        } else {
            let own_grip = own_grip.expect("declared cells retain a flat chart");
            let at = own_grip as usize * FORM_WORDS;
            if at + FORM_WORDS <= self.own().len() {
                RegionalForm::unpack(self.own(), at)
            } else {
                RegionalForm::UNBORN
            }
        };
        (
            contact.flat_grip(),
            standing.join(own),
            standing,
            contact.receiver_rank(),
        )
    }

    /// DEPOSIT one deed's felt term into the OWN region at a grip (the spool grows; a crossing past the
    /// reservation is inert). Deposit-only — the standing region is never mutated by a live body.
    #[inline]
    fn deposit(&mut self, g: Grip, term: FeltTerm) -> bool {
        if self.founded_cells {
            return false;
        }
        let at = (g as usize) * FORM_WORDS;
        if at + FORM_WORDS > self.own().len() {
            return false;
        }
        let form = RegionalForm::unpack(self.own(), at).deposit(term);
        let mut row = [0u32; FORM_WORDS];
        form.pack(&mut row, 0);
        self.own_mut()[at..at + FORM_WORDS].copy_from_slice(&row);
        true
    }

    /// Deposit at a construction, not an address. The local grip is re-derived at the lineage's
    /// own grain. On first contact the cell keeps that founding position whole; later contacts
    /// at the same local cell deepen only its ordered form.
    ///
    /// Under the register posture (`§XXXII-c`) a genuinely new grip is the register's own arrive
    /// event; the increment that carries into the rank's top tooth widens the chart through the
    /// boundary seam (existing cells zero-extend whole), and THIS arriving contact grounds at the
    /// new hand. One arrival produces at most one carry, so the re-entry is depth one.
    fn deposit_at(&mut self, position: Place, term: FeltTerm) -> bool {
        if let OwnStore::RankedStorage { storage, state } = &mut self.own {
            if state.deposit_term(&mut **storage, position, term).is_err() {
                self.resource_refused = true;
                return false;
            }
            (self.releases, self.narrows) = state.breath();
            return true;
        }
        if matches!(
            self.own,
            OwnStore::Sparse { .. } | OwnStore::SparseStorage { .. }
        ) {
            let receipt = match &mut self.own {
                OwnStore::Sparse { cells, state } => {
                    state.deposit_term(&mut **cells, position, term)
                }
                OwnStore::SparseStorage { storage, state } => {
                    state.deposit_term(&mut **storage, position, term)
                }
                _ => None,
            };
            let Some(_receipt) = receipt else {
                self.resource_refused = true;
                return false;
            };
            let state = match &self.own {
                OwnStore::Sparse { state, .. } | OwnStore::SparseStorage { state, .. } => *state,
                _ => unreachable!(),
            };
            self.own_axis = state.axis() as i64;
            self.register = state.register;
            (self.releases, self.narrows) = state.breath();
            return true;
        }
        if !self.founded_cells {
            return self.deposit(place::ground(position, self.own_axis), term);
        }
        let mut grip = place::ground(position, self.own_axis);
        let mut at = grip as usize * OWN_CELL_WORDS;
        if at + OWN_CELL_WORDS > self.own().len() {
            return false;
        }
        if self.own()[at + OWN_CELL_LIVE] == 0 {
            if let OwnStore::Register(_) = self.own {
                // THE INFALL DECOMPOSES AT THE ACCEPTED GAUGE (Brandon's four-verb ruling,
                // 2026-07-10 — emanation · infall · transport · foil; the older holonics'
                // `infall = transport ⊕ foil`). An arrival is counted ONLY where it lands as
                // FOIL (genuinely founds); a landing that aliases zero-extended live history is
                // pure TRANSPORT — kin — and the kin never drives the count (the forbidden
                // coupling). The carry is §XXXII-b's own cascade run mid-current: when the
                // candidate hand cannot hold the infall, the digit stands and the arrival is
                // re-judged at the climbed gauge. The register's occupancy is therefore the
                // foil count at the standing gauge — it can never diverge from the live grips.
                loop {
                    let (next, carried) = self.register.arrive();
                    if !carried {
                        self.register = next;
                        break;
                    }
                    let old_axis = self.own_axis;
                    let new_axis = old_axis << 1;
                    if let OwnStore::Register(chart) = &mut self.own {
                        chart.recast(old_axis, new_axis);
                    }
                    self.own_axis = new_axis;
                    self.register = self.register.digit();
                    grip = place::ground(position, self.own_axis);
                    at = grip as usize * OWN_CELL_WORDS;
                    debug_assert!(at + OWN_CELL_WORDS <= self.own().len());
                    if self.own()[at + OWN_CELL_LIVE] != 0 {
                        // TRANSPORT at the accepted gauge: the moved cell carries this infall's
                        // kin — deepen below, founder untouched, the arrival never counts.
                        break;
                    }
                    // still FOIL at the climbed gauge: re-judge the arrive at the new hand.
                }
            }
            // The founding construction is written ONLY where the (possibly re-grounded) cell is
            // genuinely UNBORN. An aliased accepted-rank landing deepens the moved cell below —
            // its founder crosses untouched, byte-whole.
            if self.own()[at + OWN_CELL_LIVE] == 0 {
                let mut word = 0usize;
                while word < COG_WORDS {
                    self.own_mut()[at + OWN_CELL_POSITION + word] =
                        cog_packed_word(position.0, word);
                    self.own_mut()[at + OWN_CELL_POSITION + COG_WORDS + word] =
                        cog_packed_word(position.1, word);
                    word += 1;
                }
            }
        }
        let form = RegionalForm::unpack(self.own(), at + OWN_CELL_FORM).deposit(term);
        // THE ANNIHILATION RELEASE (Brandon's ruling, 2026-07-10). A pure-ride cell whose
        // directed resultant cancels EXACTLY, with both fiber arms empty, holds no winding —
        // releasing it un-deposits nothing (time parity lives on the transport, and the
        // transport already radiated). The register departs, and the retirement CASCADE re-runs
        // from the register's standing configuration (`FORMULA §XXXVI` — the width changes at
        // the events; the off-section survivor is the barrier, and a borrow blocked at its own
        // crossing completes at the later event that clears it). A cell with ANY standing fiber
        // can never release: winding cannot be un-deposited. Register posture only — a declared
        // gate's grain is fixed by declaration.
        if matches!(self.own, OwnStore::Register(_)) {
            let (same, other) = form.resultant();
            let (this_way, that_way) = form.fiber();
            if same.mag == 0
                && other.mag == 0
                && this_way == crate::num::Rung::ZERO
                && that_way == crate::num::Rung::ZERO
            {
                let mut word = 0usize;
                while word < OWN_CELL_WORDS {
                    self.own_mut()[at + word] = 0;
                    word += 1;
                }
                let (register, _borrowed) = self.register.depart();
                self.register = register;
                self.releases += 1;
                self.narrow_cascade();
                return true;
            }
        }
        form.pack(self.own_mut(), at + OWN_CELL_FORM);
        self.own_mut()[at + OWN_CELL_LIVE] = 1;
        true
    }

    /// THE BREATH'S CASCADE (`FORMULA §XXXVI` — the width changes at the events). At each
    /// departure event the retirement cascade re-runs from the register's own STANDING
    /// CONFIGURATION: a digit retires when the occupancy register stands entirely below the
    /// retiring rank's tooth (the exact mirror of the carry's hand, read as a bit configuration
    /// — the event triggers, the state decides; never a resident poll) AND every surviving live
    /// cell's carried founder re-grounds to the exact source of its zero-section grip — the
    /// lossless exact inverse of the widening. THE OFF-SECTION SURVIVOR IS THE BARRIER: a blocked
    /// narrow is an excited compound configuration — standing state, never a carried flag — and it
    /// relaxes at the later event whose departure clears the barrier, cascading through every digit
    /// the configuration affords, exactly as the carry cascades on arrivals. A spread that genuinely
    /// needs the width keeps it: the machine occupies what it needs, and no more. No merge is
    /// ever performed here.
    fn narrow_cascade(&mut self) {
        loop {
            if self.own_axis <= 1 {
                return;
            }
            // The register face: occupancy stands entirely below the retiring rank's tooth.
            let tooth = crate::chart::hand((self.own_axis >> 1) as u32);
            if self.register.occupancy & !(tooth - 1) != 0 {
                return;
            }
            // The chart face: every live cell is construction-clean at the retiring digit. A
            // section coordinate alone is insufficient: the carried founder must re-ground to
            // that section's exact source in the receiving narrower chart.
            let new_axis = self.own_axis >> 1;
            let cells = (self.own_axis * self.own_axis) as usize;
            let mut grip = 0usize;
            while grip < cells {
                let at = grip * OWN_CELL_WORDS;
                if self.own()[at + OWN_CELL_LIVE] != 0
                    && crate::chart::zero_extended_source(
                        grip as u32,
                        new_axis as u32,
                        self.own_axis as u32,
                    ) != Some(place::ground(own_cell_position(self.own(), at), new_axis))
                {
                    return;
                }
                grip += 1;
            }
            if let OwnStore::Register(chart) = &mut self.own {
                chart.recast(self.own_axis, new_axis);
            } else {
                return;
            }
            self.own_axis = new_axis;
            self.register = self.register.digit_retired();
            self.narrows += 1;
        }
    }
}

/// One current-local sparse OWN surface reconstructed from accepted deed emissions.  This is the
/// same REGISTER deposit law used by [`ErosBody`], without re-running perception, action, or source
/// events.  A membrane sweeps one current journal through this mouth once and then shares the
/// resulting surface across plural cut incidences.
pub struct FeltEmissionSurface<'a> {
    medium: Medium<'a>,
}

impl<'a> FeltEmissionSurface<'a> {
    pub fn over_register(own: &'a mut dyn OwnRecast) -> Self {
        Self {
            // Emission replay performs deposits only. No cone/terrain read occurs, so there is no
            // pre-light standing chart to manufacture at this boundary.
            medium: Medium::over_register(&[], own, 1),
        }
    }

    /// Accept one already-validated emitted deed. A mismatched hand is refused before mutation;
    /// otherwise the exact position and term cross the ordinary REGISTER deposit seam.
    pub fn deposit(&mut self, emission: FeltEmission) -> bool {
        self.deposit_with_receipt(emission).is_some()
    }

    /// The same accepted deposit with its exact post-event chart posture.  `grip` is derived from
    /// the deed's carried position at the resulting axis; it is testimony, never an input address.
    pub fn deposit_with_receipt(&mut self, emission: FeltEmission) -> Option<FeltDeposit> {
        if !emission.hand_is_exact() || !self.medium.deposit_at(emission.position, emission.term) {
            return None;
        }
        let axis = self.medium.own_axis as u32;
        let grip = place::ground(emission.position, self.medium.own_axis);
        let at = grip as usize * OWN_CELL_WORDS;
        let live = at + OWN_CELL_WORDS <= self.medium.own().len()
            && self.medium.own()[at + OWN_CELL_LIVE] != 0;
        Some(FeltDeposit { grip, axis, live })
    }

    pub fn axis(&self) -> u32 {
        self.medium.register.axis
    }

    pub fn occupancy(&self) -> u64 {
        self.medium.register.occupancy
    }

    pub fn breath(&self) -> (u64, u64) {
        (self.medium.releases, self.medium.narrows)
    }
}

/// ONE POSITIONAL LANDING on the active felt medium: where the arrival stands and the first-order
/// face through which it arrived. Shared flow, quotient radiation, and scalar standing are absent;
/// the chi-bearing deed crosses separately into the lane-local regional form.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Landing {
    /// Exact flat compatibility projection where the receiver has one. The causal construction
    /// remains in the face and emitted deed, so a ranked receiver needs no sentinel address.
    pub cell: Option<Grip>,
    pub face: Face,
    /// Local projection `(cross, aim)`. It is not the second-order `χ` which crosses.
    pub meeting_ratio: (i64, i64),
    pub founds: bool,
}

/// HISTORICAL one-word-pool landing. This type remains only so the recorded pre-§XXIV `Manifold`
/// arithmetic can reproduce its quotient/remainder traces; it is not returned by `ErosBody`.
#[derive(Clone, Copy, Debug)]
pub struct FlowLanding {
    pub cell: Grip,
    pub face: Face,
    pub meeting_ratio: (i64, i64),
    pub founds: bool,
    pub windings: u32,
    pub radiated: u64,
    pub fed: u32,
    pub standing: u32,
    pub standing_delta: i64,
}

/// Boundary-only count of the FeltTerms accepted into one lane-local spool. These four faces remain
/// separate because a ride, an oriented founding, and a completed dark passage are different
/// crossings. The counts are never read by the body and never substitute for the regional form.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct TermCounts {
    pub ride: u64,
    pub found_this: u64,
    pub found_that: u64,
    pub dark: u64,
}

/// The exact causal hand of one accepted felt crossing.  This is not an observer label: RIDE,
/// FOUND on either winding arm, and a completed dark passage are the four body deeds which already
/// update [`TermCounts`] separately.  The explicit hand is required at the output boundary because
/// [`WindingQuantum::None`] is shared by RIDE and DARK.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum FeltDeed {
    Ride,
    FoundThis,
    FoundThat,
    Dark,
}

/// One accepted OWN deposit at the body's native topology seam.  The construction position and
/// complete felt term are sufficient to replay the deposit through the same REGISTER law; no grip,
/// packed OWN row, source encoding, or observer scalar substitutes for them.  Event/current cause
/// is deliberately absent here and is attached by the active membrane which owns that chronology.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct FeltEmission {
    pub position: Place,
    pub term: FeltTerm,
    pub deed: FeltDeed,
    /// Exact occupied receiver-before cell whose form bent this deed, when one existed. Grey
    /// co-presence and dark deeds carry no standing read. This is outward causal incidence only;
    /// the body never consumes it.
    pub standing_read: Option<StandingRead>,
}

/// Exact pre-event receiver needed to form a source-supplied directed A2 contact. This is captured
/// before the target event changes the body. It contains no event ordinal, source tag, or action
/// scalar and therefore cannot manufacture incidence.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EventReceiver {
    pub channel: LineageChannel,
    pub held: Face,
    pub held_live: bool,
}

/// One actual directed event meeting and its resolved crossing, when the target receiver supplied
/// a formed fourth contact. An unresolved meeting remains exact without fabricating a deed.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DirectedEventContact {
    pub receiver: EventReceiver,
    pub meeting: Face,
    pub emission: Option<FeltEmission>,
}

/// Form one receiver-relative directed contact from the immutable standing-before field alone.
///
/// This is the read-only half of [`ErosBody::directed_event_contact_at_source_grain`].  A physical
/// executor may therefore spread co-present contact formation across independent lanes without
/// sharing or cloning the lineage's mutable carrier.  The caller must supply the receiver captured
/// at the source constituent's actual grain; grain validation remains the mounted body's concern.
/// `None` is an exact standing-query refusal, never an open fourth contact.
pub fn directed_event_contact_over_standing(
    standing: &dyn StandingQuery,
    receiver: EventReceiver,
    from: Place,
    to: Place,
) -> Option<DirectedEventContact> {
    let meeting = face(to, from, receiver.channel.frame().tip());
    if !receiver.held_live {
        return Some(DirectedEventContact {
            receiver,
            meeting,
            emission: None,
        });
    }
    let Some(initial_chi) = meeting.chi_against(&receiver.held) else {
        return Some(DirectedEventContact {
            receiver,
            meeting,
            emission: None,
        });
    };
    let standing_position = cast_position(initial_chi);
    let standing_form = standing.form_at_position(standing_position)?;
    let receiver_rank = standing.receiver_rank();
    let flat_grip = if receiver_rank <= 16 {
        Some(place::ground(standing_position, 1i64 << receiver_rank))
    } else {
        None
    };
    let standing_read = standing_form.occupied().then_some(StandingRead {
        position: standing_position,
        receiver_rank,
        flat_grip,
        form: standing_form,
    });
    let met = standing_form.drag(meeting);
    if met.arrow.at_horizon() {
        return Some(DirectedEventContact {
            receiver,
            meeting,
            emission: None,
        });
    }
    let Some(chi) = met.chi_against(&receiver.held) else {
        return Some(DirectedEventContact {
            receiver,
            meeting,
            emission: None,
        });
    };
    let wound = met.wound_against(&receiver.held);
    let winding = if !wound {
        WindingQuantum::None
    } else if chi.other.turn & 2 == 0 {
        WindingQuantum::ThisWay
    } else {
        WindingQuantum::ThatWay
    };
    let deed = match winding {
        WindingQuantum::None => FeltDeed::Ride,
        WindingQuantum::ThisWay => FeltDeed::FoundThis,
        WindingQuantum::ThatWay => FeltDeed::FoundThat,
    };
    Some(DirectedEventContact {
        receiver,
        meeting,
        emission: Some(FeltEmission {
            position: cast_position(chi),
            term: FeltTerm { chi, winding },
            deed,
            standing_read,
        }),
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct StandingRead {
    /// Exact construction which the receiver resolved against its standing chart.  This can
    /// differ from the later post-drag deed position and therefore cannot be reconstructed from
    /// the emitted deposit alone.
    pub position: Place,
    /// Rank of the receiver chart which resolved `position`. Position without this frame cannot
    /// name a ranked address once the historical flat quotient no longer exists.
    pub receiver_rank: u64,
    /// Historical exact flat projection, where the receiver has one.  `None` is a real absence of
    /// that quotient, not grip zero.
    pub flat_grip: Option<Grip>,
    pub form: RegionalForm,
}

impl FeltEmission {
    /// Validate that the explicit output deed and the transported term carry one exact causal
    /// hand.  This pure boundary law is shared by dense and sparse receiving surfaces; neither
    /// implementation is allowed to reinterpret a winding as a category or repair it after
    /// mutation.
    #[inline]
    pub fn hand_is_exact(self) -> bool {
        match self.deed {
            FeltDeed::Ride | FeltDeed::Dark => self.term.winding == WindingQuantum::None,
            FeltDeed::FoundThis => {
                self.term.winding == WindingQuantum::ThisWay && self.term.chi.other.turn & 2 == 0
            }
            FeltDeed::FoundThat => {
                self.term.winding == WindingQuantum::ThatWay && self.term.chi.other.turn & 2 != 0
            }
        }
    }
}

/// Allocation-free output aperture for accepted felt deeds.  A no-op target preserves every
/// historical body mouth; a formed membrane target may journal each emission exactly once.  The
/// body never reads a target and a full physical target must suspend outside this host mouth rather
/// than silently drop an accepted deed.
pub trait FeltEmissionTarget {
    fn emit(&mut self, emission: FeltEmission);
}

/// Borrowed internal incidence of one actual source event. `len` and `relation` parameterize the
/// event's own geometry; they are not a sequence of world instants. The boundary implementation
/// owns the source representation while Soma receives only canonical relations in their declared
/// path order.
pub trait EventIncidence {
    fn len(&self) -> usize;
    fn relation(&self, at: usize) -> Cog;

    #[inline]
    fn is_empty(&self) -> bool {
        self.len() == 0
    }
}

impl<F> FeltEmissionTarget for F
where
    F: FnMut(FeltEmission),
{
    #[inline]
    fn emit(&mut self, emission: FeltEmission) {
        self(emission)
    }
}

struct NoFeltEmission;

impl FeltEmissionTarget for NoFeltEmission {
    #[inline(always)]
    fn emit(&mut self, _emission: FeltEmission) {}
}

impl TermCounts {
    pub const ZERO: TermCounts = TermCounts {
        ride: 0,
        found_this: 0,
        found_that: 0,
        dark: 0,
    };

    /// A boundary count of all accepted terms. This scalar is useful only beside the exact
    /// fiber/resultant topology; cancellation makes it incapable of describing the form.
    #[inline]
    pub fn total(self) -> u64 {
        self.ride + self.found_this + self.found_that + self.dark
    }

    /// Combine independent lane instruments at the membrane. This does not combine their forms;
    /// the configuration fold alone performs that physical operation.
    #[inline]
    pub fn add(self, other: TermCounts) -> TermCounts {
        TermCounts {
            ride: self.ride + other.ride,
            found_this: self.found_this + other.found_this,
            found_that: self.found_that + other.found_that,
            dark: self.dark + other.dark,
        }
    }
}

/// ★ EROS ON THE HOST MANIFOLD — the driven body (`FORMULA §V`): one lineage channel `K`, its
/// gauge anchor, grain-local stances/flywheels/registers, and the two-region felt medium. The stance
/// is `FRAME(K)`'s tip read at the content grain; the anchor remains the chart gauge and never
/// resets. It consumes driven shape-light one construction at a time, stores no authored symbols,
/// and writes only chi-bearing deed terms into its OWN region.
///
/// **Θ discipline (§XXV):** the worldline is `K` — the ordered composition of this body's OWN deed
/// emanations; `Θ = TURN(K)` is read at a reach, never carried as a numeric counter (a wrapping
/// counter un-deposits winding — convicted). It never crosses to another body as a stamp; dilation
/// is read by comparing two worldlines three-body (Ledger U).
///
/// **★ THE POLE IS THE COUPLING SLOT (`FORMULA §IV`; the W4 cut).** Here the pole trails the last arrival — which
/// is MIRROR-GRADE coupling (the terrain echoing itself), stated plainly. W4 re-points the pole at the
/// CIRCULATION'S OWN STANCE (where the pathing current stands), which is the whole coupling: perception relating
/// from where thought stands. The slot is already load-bearing; W4 changes what fills it, not the law.
pub struct ErosBody<'a> {
    medium: Medium<'a>,
    frame: Place,
    pole: Place,
    /// ★ `K` (§XXV) — the lineage channel: the frame and Θ are its two reads. Seeded by the first
    /// difference (the seed frame's dead-bit place); advanced only by `fold`, one deed emanation
    /// per driven event. Never a counter.
    channel: LineageChannel,
    /// ★ THE CARRIER (`FORMULA §XVIII` — THE ILLICIUM'S LIVE VERTICAL STATE, ratified 2026-07-09):
    /// depth 0 is the word grain; **a completion at depth k is an arrival at depth k+1 — the same
    /// node, the same verb.** A CALLER-PROVIDED word reservation, rows of `ENCLOSURE_WORDS` — the
    /// boundary's own, like the pool. Each open depth carries its own enclosure: the REGISTER (the
    /// co-presence window, grain-invariant by its own derivation), a stance (the
    /// depth's standing thought) and a flywheel (the depth's held rotor): the illicium is
    /// depth-recursive; the hourglass nests. A depth is instantiated by its first brick (the same
    /// birth law as every stance — no birth detection). The reservation's extent is NEVER a
    /// constant — `carrier.len() / ENCLOSURE_WORDS` is the depth this boundary affords; past it
    /// THE RETIREMENT stands (no cap; its shared felt crossing remains PRESENTED and unfilled).
    carrier: CarrierStore<'a>,
    /// completed thoughts — depth 0's cuts (a boundary count, not a mechanism).
    thoughts: u32,
    /// Chi-bearing terms that landed in this light's OWN region. A boundary instrument only: the
    /// body never consults it, it is not carried in `K`, and it cannot alter placement or a deed.
    /// M2c reads this count beside (never instead of) the regional topology.
    terms_deposited: TermCounts,
    /// ★ W9 · THE LIVING BOUNDARY (the scope's first grain, ratified 2026-07-09): the sub-illicium —
    /// the atom-grain traversal given the SAME live law (sub-stance, sub-groove), so the walk FEELS
    /// the standing terrain (the tire on the road) instead of dead reckoning. Its completions are
    /// THE FOLDS — the cohered segments, found never listed — handed up as the word grain's arrivals
    /// (the bricks). The whitespace splitter dies as a consequence, never by decree.
    sub_stance: Node,
    sub_fly: Face,
    sub_fly_live: bool,
    /// ★ THE DARK TREAD (ratified 2026-07-09 — the induced-current law: a static bind induces nothing;
    /// the dark is free; the tread is OVER TIME): the standing dark passage's accumulated drive. A
    /// zero-magnitude difference is not an event — it is one sameness EXTENDED, carrying only duration;
    /// the passage deposits WHOLE at its completion (the first resolving difference, or the light's end),
    /// at the frame's own place — where every dark atom grounds (one place per lineage).
    dark_pending: u64,
    /// First exact depth required beyond the mounted carrier, when physical storage refused to
    /// re-base. This pressure is a membrane face and never a Soma deed.
    required_carrier_depth: usize,
}

/// ★ ONE ENCLOSURE of the carrier (`FORMULA §XVIII(b)`) — a depth's whole receiving apparatus: the
/// REGISTER (co-present bricks at THIS depth — coherence is collocation at every depth), the stance
/// (the depth's standing thought) and the flywheel (the depth's held rotor). `stance.len == 0` with
/// an empty register is the unborn enclosure — instantiated by its first brick.
#[derive(Clone, Copy)]
pub struct Enclosure {
    pub register: [Node; REGISTER as usize],
    pub head: usize,
    pub live: usize,
    pub stance: Node,
    pub fly: Face,
    pub fly_live: bool,
}

/// the carrier's word layout — ONE source for both substrates (the kernel carries the complete
/// first-person stand in a per-lane buffer; the host carries the same organs natively). The layout
/// IS the stroke seam, so its header, enclosure rows, reservation-derived deferred siblings, and
/// within-atom continuation have one mouth here instead of re-spoken literals in the membrane or
/// kernel.
pub const NODE_WORDS: usize = 16; // well 5 ⊕ place 10 ⊕ len 1
pub const FACE_WORDS: usize = 15; // reach 5 ⊕ aim 5 ⊕ cross 5
/// register 15×16 ⊕ head 1 ⊕ live 1 ⊕ stance 16 ⊕ fly 15 ⊕ fly_live 1
pub const ENCLOSURE_REGISTER: usize = 0;
pub const ENCLOSURE_HEAD: usize = (REGISTER as usize) * NODE_WORDS;
pub const ENCLOSURE_LIVE: usize = ENCLOSURE_HEAD + 1;
pub const ENCLOSURE_STANCE: usize = ENCLOSURE_LIVE + 1;
pub const ENCLOSURE_FLY: usize = ENCLOSURE_STANCE + NODE_WORDS;
pub const ENCLOSURE_FLY_LIVE: usize = ENCLOSURE_FLY + FACE_WORDS;
pub const ENCLOSURE_WORDS: usize = ENCLOSURE_FLY_LIVE + 1;

/// Conservative accepted-deed envelope for one complete current under this body's presently
/// mounted enclosure species.  It is a physical reservation face, never a score or conduct cap.
/// A transaction either affords the complete envelope or remains wholly open.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CurrentConductEnvelope {
    pub bright_atoms: u64,
    pub dark_intervals: u64,
    pub carrier_depth: u64,
    pub maximum_deeds: u64,
}

/// Derive the complete output reservation for a current before body mutation.  At one bright atom
/// the sub-grain can emit one deed.  Every reached enclosure can emit at most `REGISTER` grey
/// contacts, one perception deed, and one path deed; the two possible bricks make a full binary
/// depth tree.  A completed wholly-static interval emits exactly one further deed.
pub fn current_conduct_envelope(
    bright_atoms: u64,
    dark_intervals: u64,
    carrier_depth: usize,
) -> Option<CurrentConductEnvelope> {
    let mut level_nodes = 1u64;
    let mut enclosure_nodes = 0u64;
    let mut depth = 0usize;
    while depth < carrier_depth {
        enclosure_nodes = enclosure_nodes.checked_add(level_nodes)?;
        level_nodes = level_nodes.checked_mul(2)?;
        depth += 1;
    }
    let per_bright = enclosure_nodes
        .checked_mul(REGISTER as u64 + 2)?
        .checked_add(1)?;
    let maximum_deeds = bright_atoms
        .checked_mul(per_bright)?
        .checked_add(dark_intervals)?;
    Some(CurrentConductEnvelope {
        bright_atoms,
        dark_intervals,
        carrier_depth: u64::try_from(carrier_depth).ok()?,
        maximum_deeds,
    })
}

/// THE CARRIED FRAME'S HEADER — cursor ⊕ standing dark passage ⊕ the atom-grain stance/flywheel ⊕
/// the lineage channel `K` (§XXV: `K` must cross a stroke seam byte-exact — the worldline resumes,
/// never restarts). The channel stands where the four boundary-reserved words stood and extends
/// beyond them (its packing mouth is `LineageChannel::pack`/`unpack` in `channel`). All offsets are
/// shared with the card so no membrane literal can silently fork the first person at a stroke.
pub const CARRIER_CURSOR_LO: usize = 0;
pub const CARRIER_CURSOR_HI: usize = 1;
pub const CARRIER_DARK_LO: usize = 2;
pub const CARRIER_DARK_HI: usize = 3;
pub const CARRIER_SUB_STANCE: usize = 4;
pub const CARRIER_SUB_FLY: usize = CARRIER_SUB_STANCE + NODE_WORDS;
pub const CARRIER_SUB_FLY_LIVE: usize = CARRIER_SUB_FLY + FACE_WORDS;
pub const CARRIER_CHANNEL: usize = CARRIER_SUB_FLY_LIVE + 1;
pub const CARRIER_HEADER_WORDS: usize = CARRIER_CHANNEL + CHANNEL_WORDS;

/// Exact modality-neutral first-person header for the live host membrane. The generalized carrier
/// is a separate typed construction because its co-presence may grow beyond the historical
/// flat/card enclosure rows. Neither face is complete without the other.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LiveBodyHeader {
    words: [u32; CARRIER_HEADER_WORDS],
}

impl LiveBodyHeader {
    pub fn from_words_checked(words: &[u32]) -> Option<Self> {
        if !live_body_header_is_canonical(words) {
            return None;
        }
        let mut retained = [0u32; CARRIER_HEADER_WORDS];
        retained.copy_from_slice(words);
        Some(Self { words: retained })
    }

    pub const fn words(&self) -> &[u32; CARRIER_HEADER_WORDS] {
        &self.words
    }

    pub fn cursor(self) -> u64 {
        self.words[CARRIER_CURSOR_LO] as u64 | ((self.words[CARRIER_CURSOR_HI] as u64) << 32)
    }

    pub fn channel(self) -> LineageChannel {
        LineageChannel::unpack(&self.words, CARRIER_CHANNEL)
            .expect("a constructed live header retains canonical K")
    }
}

/// One deferred efferent can stand at each open depth while the afferent branch climbs. The lawful
/// scratch extent is therefore exactly the carrier reservation's depth — no second constant. Card
/// rows mount one node-slot per enclosure after the enclosure region; host recursion has the same
/// structural depth directly.
pub const CARRIER_DEFERRED_WORDS: usize = NODE_WORDS;

/// §XXVIII-b · THE STROKE SEAM DESCENDING. A content-heavy atom may cross our substrate seam
/// while its depth-first thickening remains one unfinished event in the body's time. The exact
/// continuation is one phase, the active depth, and the current brick. Deferred efferent siblings
/// already stand in the reservation-derived slots above. These words live at the row's tail so the
/// established header/enclosure/deferred prefix retains one spelling; historical at-rest rows are
/// extended only by this canonical all-zero face.
pub const CARRIER_CONTINUATION_PHASE: usize = 0;
pub const CARRIER_CONTINUATION_DEPTH_LO: usize = 1;
pub const CARRIER_CONTINUATION_DEPTH_HI: usize = 2;
pub const CARRIER_CONTINUATION_BRICK: usize = 3;
pub const CARRIER_CONTINUATION_WORDS: usize = CARRIER_CONTINUATION_BRICK + NODE_WORDS;

/// §XXXII-c · one event-forced OWN recast suspension. The caller and its exact checkpoint occupy
/// one control word; the only old-gauge value which cannot be reconstructed after the chart moves
/// is the pre-drag regional form. Every other face is re-derived from the frozen carrier/K and raw
/// admitted atom. The pending tail follows the older continuation so the whole established prefix
/// remains byte-stable and historical rows extend only by this canonical all-zero face.
pub const CARRIER_PENDING_CONTROL: usize = 0;
pub const CARRIER_PENDING_FORM: usize = 1;
pub const CARRIER_PENDING_WORDS: usize = CARRIER_PENDING_FORM + FORM_WORDS;
/// The externally versioned name used by SLEEP migration mouths.
pub const CARRIER_PENDING_DEED_WORDS: usize = CARRIER_PENDING_WORDS;

pub const PENDING_NONE: u32 = 0;
pub const PENDING_DARK_BEFORE: u32 = 1;
pub const PENDING_DARK_TERMINAL: u32 = 2;
pub const PENDING_SUB: u32 = 3;
pub const PENDING_ENCLOSURE_CO_PRESENT: u32 = 4;
pub const PENDING_ENCLOSURE_TERMINAL: u32 = 5;
pub const PENDING_PATH: u32 = 6;
pub const PENDING_INVALID: u32 = 7;
pub const PENDING_KIND_MASK: u32 = 0b111;
pub const PENDING_CONTACT_SHIFT: u32 = 3;
/// One enclosure can expose at most THE REGISTER's fifteen co-present contacts. Four bits are
/// therefore the structural contact hand, not an independent pending-deed cap.
pub const PENDING_CONTACT_MASK: u32 = 0b1111;
const _: [(); PENDING_CONTACT_MASK as usize] = [(); REGISTER as usize];
pub const PENDING_CONTROL_MASK: u32 =
    PENDING_KIND_MASK | (PENDING_CONTACT_MASK << PENDING_CONTACT_SHIFT);

pub const CONTINUATION_NONE: u32 = 0;
pub const CONTINUATION_PERCEIVE_AFFERENT: u32 = 1;
pub const CONTINUATION_PERCEIVE_EFFERENT: u32 = 2;
pub const CONTINUATION_PERCEIVE_UNWIND: u32 = 3;
pub const CONTINUATION_WORD_PATH: u32 = 4;
pub const CONTINUATION_PATH_AFFERENT: u32 = 5;
pub const CONTINUATION_PATH_EFFERENT: u32 = 6;
pub const CONTINUATION_PATH_UNWIND: u32 = 7;
/// The committed SUB fold's depth-zero arrival. Its live brick is the input to `perceive_grain(0)`;
/// naming that caller before entering it lets an enclosure deed suspend without inventing another
/// node or caller-depth payload.
pub const CONTINUATION_WORD_PERCEIVE: u32 = 8;

#[inline]
pub const fn carrier_row_words(depth: usize) -> usize {
    CARRIER_HEADER_WORDS
        + depth * (ENCLOSURE_WORDS + CARRIER_DEFERRED_WORDS)
        + CARRIER_CONTINUATION_WORDS
        + CARRIER_PENDING_WORDS
}

#[inline]
pub const fn carrier_row_depth(words: usize) -> usize {
    carrier_depth_afforded_by_words(words)
}

/// Read the deepest whole carrier reservation afforded by a boundary word extent. Any remainder is
/// outside the row; it never changes the construction's depth or becomes an interior cap.
#[inline]
pub const fn carrier_depth_afforded_by_words(words: usize) -> usize {
    if words <= CARRIER_HEADER_WORDS + CARRIER_CONTINUATION_WORDS + CARRIER_PENDING_WORDS {
        0
    } else {
        (words - CARRIER_HEADER_WORDS - CARRIER_CONTINUATION_WORDS - CARRIER_PENDING_WORDS)
            / (ENCLOSURE_WORDS + CARRIER_DEFERRED_WORDS)
    }
}

#[inline]
pub const fn carrier_enclosure_base(depth: usize) -> usize {
    CARRIER_HEADER_WORDS + depth * ENCLOSURE_WORDS
}

#[inline]
pub const fn carrier_deferred_base(reserved_depth: usize, depth: usize) -> usize {
    CARRIER_HEADER_WORDS + reserved_depth * ENCLOSURE_WORDS + depth * CARRIER_DEFERRED_WORDS
}

#[inline]
pub const fn carrier_continuation_base(reserved_depth: usize) -> usize {
    CARRIER_HEADER_WORDS + reserved_depth * (ENCLOSURE_WORDS + CARRIER_DEFERRED_WORDS)
}

#[inline]
pub const fn carrier_pending_base(reserved_depth: usize) -> usize {
    carrier_continuation_base(reserved_depth) + CARRIER_CONTINUATION_WORDS
}

#[inline]
pub const fn pending_control(kind: u32, next_contact_exclusive: u32) -> u32 {
    assert!(
        next_contact_exclusive & !PENDING_CONTACT_MASK == 0,
        "a pending co-present checkpoint fits the enclosure's derived REGISTER"
    );
    kind | (next_contact_exclusive << PENDING_CONTACT_SHIFT)
}

#[inline]
pub const fn pending_kind(control: u32) -> u32 {
    control & PENDING_KIND_MASK
}

#[inline]
pub const fn pending_next_contact(control: u32) -> u32 {
    (control >> PENDING_CONTACT_SHIFT) & PENDING_CONTACT_MASK
}

#[inline]
pub fn cog_packed_word(c: Cog, word: usize) -> u32 {
    num::cog_packed_word(c, word)
}

#[inline]
pub fn unpack_cog(w: &[u32], at: usize) -> Cog {
    num::read_cog(w, at)
}

#[inline]
pub fn node_packed_word(n: Node, word: usize) -> u32 {
    if word < COG_WORDS {
        cog_packed_word(n.well, word)
    } else if word < 2 * COG_WORDS {
        cog_packed_word(n.place.0, word - COG_WORDS)
    } else if word < 3 * COG_WORDS {
        cog_packed_word(n.place.1, word - 2 * COG_WORDS)
    } else if word == 3 * COG_WORDS {
        n.len
    } else {
        0
    }
}

#[inline]
pub fn face_packed_word(f: Face, word: usize) -> u32 {
    if word < COG_WORDS {
        cog_packed_word(f.arrow.reach, word)
    } else if word < 2 * COG_WORDS {
        cog_packed_word(f.arrow.aim, word - COG_WORDS)
    } else {
        cog_packed_word(f.arrow.cross, word - 2 * COG_WORDS)
    }
}

#[inline]
fn pack_node(n: Node, out: &mut [u32], at: usize) {
    let mut word = 0usize;
    while word < NODE_WORDS {
        out[at + word] = node_packed_word(n, word);
        word += 1;
    }
}

#[inline]
fn pack_face(f: Face, out: &mut [u32], at: usize) {
    let mut word = 0usize;
    while word < FACE_WORDS {
        out[at + word] = face_packed_word(f, word);
        word += 1;
    }
}

/// Ground one whole node after its owning reader has proved the row extent.
///
/// # Safety
///
/// `at..at + NODE_WORDS` must be a live row in `w`.
#[inline(always)]
pub unsafe fn unpack_node_unchecked_with<S: WordSeam>(w: &[u32], at: usize) -> Node {
    Node {
        well: unsafe { num::read_cog_unchecked::<S>(w, at) },
        place: (
            unsafe { num::read_cog_unchecked::<S>(w, at + COG_WORDS) },
            unsafe { num::read_cog_unchecked::<S>(w, at + 2 * COG_WORDS) },
        ),
        len: unsafe { S::read_u32_unchecked(w, at + 3 * COG_WORDS) },
    }
}

/// Ground one whole face after its owning reader has proved the row extent.
///
/// # Safety
///
/// `at..at + FACE_WORDS` must be a live row in `w`.
#[inline(always)]
pub unsafe fn unpack_face_unchecked_with<S: WordSeam>(w: &[u32], at: usize) -> Face {
    Face {
        arrow: crate::arrow::Arrow {
            reach: unsafe { num::read_cog_unchecked::<S>(w, at) },
            aim: unsafe { num::read_cog_unchecked::<S>(w, at + COG_WORDS) },
            cross: unsafe { num::read_cog_unchecked::<S>(w, at + 2 * COG_WORDS) },
        },
    }
}

#[inline(always)]
fn absent_node() -> Node {
    Node {
        well: Cog::ZERO,
        place: (Cog::ZERO, Cog::ZERO),
        len: 0,
    }
}

#[inline(always)]
fn absent_face() -> Face {
    Face {
        arrow: crate::arrow::Arrow {
            reach: Cog::ZERO,
            aim: Cog::ZERO,
            cross: Cog::ZERO,
        },
    }
}

/// Read one whole node through `S`; a short row is one structural absence.
#[inline]
pub fn unpack_node_with<S: WordSeam>(w: &[u32], at: usize) -> Node {
    if row_fits(w, at, NODE_WORDS) {
        unsafe { unpack_node_unchecked_with::<S>(w, at) }
    } else {
        absent_node()
    }
}

/// Read one whole face through `S`; a short row is one structural absence.
#[inline]
pub fn unpack_face_with<S: WordSeam>(w: &[u32], at: usize) -> Face {
    if row_fits(w, at, FACE_WORDS) {
        unsafe { unpack_face_unchecked_with::<S>(w, at) }
    } else {
        absent_face()
    }
}

#[inline]
pub fn unpack_node(w: &[u32], at: usize) -> Node {
    unpack_node_with::<SliceWordSeam>(w, at)
}

#[inline]
pub fn unpack_face(w: &[u32], at: usize) -> Face {
    unpack_face_with::<SliceWordSeam>(w, at)
}

#[inline]
fn packed_words_are_zero(w: &[u32], at: usize, words: usize) -> bool {
    row_fits(w, at, words) && w[at..at + words].iter().all(|word| *word == 0)
}

/// Whether one packed node has canonical nested number rows and reproduces its exact boundary
/// spelling. Node liveness is contextual: callers decide whether a zero-length payload is allowed.
pub fn packed_node_is_canonical(w: &[u32], at: usize) -> bool {
    if !row_fits(w, at, NODE_WORDS) {
        return false;
    }
    let mut cog = 0usize;
    while cog < 3 {
        if !num::packed_cog_is_canonical(w, at + cog * COG_WORDS) {
            return false;
        }
        cog += 1;
    }
    let node = unpack_node(w, at);
    let mut word = 0usize;
    while word < NODE_WORDS {
        if node_packed_word(node, word) != w[at + word] {
            return false;
        }
        word += 1;
    }
    true
}

/// Whether one packed face has canonical nested number rows and reproduces its exact boundary
/// spelling. Formedness belongs to the deed which reads the face, not to this representation check.
pub fn packed_face_is_canonical(w: &[u32], at: usize) -> bool {
    if !row_fits(w, at, FACE_WORDS) {
        return false;
    }
    let mut cog = 0usize;
    while cog < 3 {
        if !num::packed_cog_is_canonical(w, at + cog * COG_WORDS) {
            return false;
        }
        cog += 1;
    }
    let face = unpack_face(w, at);
    let mut word = 0usize;
    while word < FACE_WORDS {
        if face_packed_word(face, word) != w[at + word] {
            return false;
        }
        word += 1;
    }
    true
}

impl Enclosure {
    /// One scalar carrier word. The card issues atomic stores through this mouth; the host's seam
    /// pack loops over the same words, so the enclosure layout has one author across substrates.
    #[inline]
    pub fn packed_word(&self, word: usize) -> u32 {
        if word < ENCLOSURE_HEAD {
            node_packed_word(self.register[word / NODE_WORDS], word % NODE_WORDS)
        } else if word == ENCLOSURE_HEAD {
            self.head as u32
        } else if word == ENCLOSURE_LIVE {
            self.live as u32
        } else if word < ENCLOSURE_FLY {
            node_packed_word(self.stance, word - ENCLOSURE_STANCE)
        } else if word < ENCLOSURE_FLY_LIVE {
            face_packed_word(self.fly, word - ENCLOSURE_FLY)
        } else {
            self.fly_live as u32
        }
    }

    /// pack this enclosure into its word row (the carrier's carriage; an all-zero row unpacks to
    /// the unborn enclosure — every used path gates on `len`/`live`, so zeroed buffers are lawful
    /// birth).
    pub fn pack(&self, out: &mut [u32; ENCLOSURE_WORDS]) {
        let mut word = 0usize;
        while word < ENCLOSURE_WORDS {
            out[word] = self.packed_word(word);
            word += 1;
        }
    }

    /// Unpack one already-proved enclosure row through `S`.
    ///
    /// # Safety
    ///
    /// `base..base + ENCLOSURE_WORDS` is live in `w`.
    pub unsafe fn unpack_at_unchecked_with<S: WordSeam>(w: &[u32], base: usize) -> Enclosure {
        let mut r = Enclosure::empty();
        let mut i = 0usize;
        while i < REGISTER as usize {
            r.register[i] = unsafe { unpack_node_unchecked_with::<S>(w, base + i * NODE_WORDS) };
            i += 1;
        }
        r.head = unsafe { S::read_u32_unchecked(w, base + ENCLOSURE_HEAD) } as usize
            % (REGISTER as usize);
        r.live = (unsafe { S::read_u32_unchecked(w, base + ENCLOSURE_LIVE) } as usize)
            .min(REGISTER as usize);
        r.stance = unsafe { unpack_node_unchecked_with::<S>(w, base + ENCLOSURE_STANCE) };
        r.fly = unsafe { unpack_face_unchecked_with::<S>(w, base + ENCLOSURE_FLY) };
        r.fly_live = unsafe { S::read_u32_unchecked(w, base + ENCLOSURE_FLY_LIVE) } != 0;
        r
    }

    /// Safe whole-row enclosure read; a short row is one wholly absent packed enclosure.
    pub fn unpack_at_with<S: WordSeam>(w: &[u32], base: usize) -> Enclosure {
        if row_fits(w, base, ENCLOSURE_WORDS) {
            unsafe { Enclosure::unpack_at_unchecked_with::<S>(w, base) }
        } else {
            Enclosure {
                register: [absent_node(); REGISTER as usize],
                head: 0,
                live: 0,
                stance: absent_node(),
                fly: absent_face(),
                fly_live: false,
            }
        }
    }

    pub fn unpack_at(w: &[u32], base: usize) -> Enclosure {
        Enclosure::unpack_at_with::<SliceWordSeam>(w, base)
    }

    pub fn empty() -> Enclosure {
        let e = Node {
            well: Cog::lit(1),
            place: place::origin(),
            len: 0,
        };
        Enclosure {
            register: [e; REGISTER as usize],
            head: 0,
            live: 0,
            stance: e,
            fly: face(place::origin(), place::origin(), place::origin()),
            fly_live: false,
        }
    }
}

#[inline]
pub const fn continuation_is_afferent(phase: u32) -> bool {
    phase == CONTINUATION_PERCEIVE_AFFERENT || phase == CONTINUATION_PATH_AFFERENT
}

#[inline]
pub const fn continuation_is_efferent(phase: u32) -> bool {
    phase == CONTINUATION_PERCEIVE_EFFERENT || phase == CONTINUATION_PATH_EFFERENT
}

#[inline]
pub const fn continuation_is_unwind(phase: u32) -> bool {
    phase == CONTINUATION_PERCEIVE_UNWIND || phase == CONTINUATION_PATH_UNWIND
}

#[inline]
pub const fn continuation_is_perceive(phase: u32) -> bool {
    phase == CONTINUATION_PERCEIVE_AFFERENT
        || phase == CONTINUATION_PERCEIVE_EFFERENT
        || phase == CONTINUATION_PERCEIVE_UNWIND
}

#[inline]
pub const fn continuation_is_path(phase: u32) -> bool {
    phase == CONTINUATION_PATH_AFFERENT
        || phase == CONTINUATION_PATH_EFFERENT
        || phase == CONTINUATION_PATH_UNWIND
}

#[inline]
pub const fn continuation_shape_is_formed(
    phase: u32,
    continuation_depth: usize,
    brick_live: bool,
    reserved_depth: usize,
) -> bool {
    if phase == CONTINUATION_NONE || phase == CONTINUATION_WORD_PATH {
        continuation_depth == 0 && !brick_live
    } else if phase == CONTINUATION_WORD_PERCEIVE {
        continuation_depth == 0 && brick_live
    } else if continuation_is_afferent(phase) {
        continuation_depth >= 1 && continuation_depth <= reserved_depth && brick_live
    } else if continuation_is_efferent(phase) {
        continuation_depth >= 1 && continuation_depth < reserved_depth
    } else if continuation_is_unwind(phase) {
        continuation_depth >= 1 && continuation_depth <= reserved_depth && !brick_live
    } else {
        false
    }
}

#[inline]
pub fn carrier_continuation_phase(w: &[u32]) -> u32 {
    let depth = carrier_row_depth(w.len());
    if depth == 0 || carrier_row_words(depth) != w.len() {
        u32::MAX
    } else {
        w[carrier_continuation_base(depth) + CARRIER_CONTINUATION_PHASE]
    }
}

#[inline]
pub fn carrier_pending_control(w: &[u32]) -> u32 {
    let depth = carrier_row_depth(w.len());
    if depth == 0 || carrier_row_words(depth) != w.len() {
        u32::MAX
    } else {
        w[carrier_pending_base(depth) + CARRIER_PENDING_CONTROL]
    }
}

#[inline]
pub fn carrier_pending_kind(w: &[u32]) -> u32 {
    pending_kind(carrier_pending_control(w))
}

/// Validate one whole boundary-carried frame without clipping any of its live faces. This is the
/// exact row emitted by host/card carriage: one canonical atom-grain header and `K`, canonical open
/// enclosures, and either the all-zero completed continuation or the exact state of one unfinished
/// within-atom thickening. The latter is still one event: this check exposes no receiving edge.
pub fn carried_frame_is_canonical(w: &[u32]) -> bool {
    let depth = carrier_row_depth(w.len());
    if depth == 0 || carrier_row_words(depth) != w.len() {
        return false;
    }

    if !packed_node_is_canonical(w, CARRIER_SUB_STANCE)
        || !packed_face_is_canonical(w, CARRIER_SUB_FLY)
        || w[CARRIER_SUB_FLY_LIVE] > 1
        || !LineageChannel::packed_row_is_canonical(w, CARRIER_CHANNEL)
    {
        return false;
    }
    let sub_stance = unpack_node(w, CARRIER_SUB_STANCE);
    if sub_stance.len == 0 && !packed_words_are_zero(w, CARRIER_SUB_STANCE, NODE_WORDS) {
        return false;
    }
    if w[CARRIER_SUB_FLY_LIVE] == 0 && !packed_words_are_zero(w, CARRIER_SUB_FLY, FACE_WORDS) {
        return false;
    }
    if w[CARRIER_SUB_FLY_LIVE] != 0
        && (sub_stance.len == 0 || !unpack_face(w, CARRIER_SUB_FLY).rotor_formed())
    {
        return false;
    }

    let continuation = carrier_continuation_base(depth);
    let phase = w[continuation + CARRIER_CONTINUATION_PHASE];
    let continuation_depth_u64 = w[continuation + CARRIER_CONTINUATION_DEPTH_LO] as u64
        | ((w[continuation + CARRIER_CONTINUATION_DEPTH_HI] as u64) << 32);
    if continuation_depth_u64 > usize::MAX as u64 {
        return false;
    }
    let continuation_depth = continuation_depth_u64 as usize;
    if phase > CONTINUATION_WORD_PERCEIVE
        || !packed_node_is_canonical(w, continuation + CARRIER_CONTINUATION_BRICK)
    {
        return false;
    }
    let continuation_brick = unpack_node(w, continuation + CARRIER_CONTINUATION_BRICK);
    if continuation_brick.len == 0
        && !packed_words_are_zero(w, continuation + CARRIER_CONTINUATION_BRICK, NODE_WORDS)
    {
        return false;
    }
    if !continuation_shape_is_formed(
        phase,
        continuation_depth,
        continuation_brick.len != 0,
        depth,
    ) {
        return false;
    }

    let pending = carrier_pending_base(depth);
    let control = w[pending + CARRIER_PENDING_CONTROL];
    let kind = pending_kind(control);
    let next_contact = pending_next_contact(control) as usize;
    if control & !PENDING_CONTROL_MASK != 0
        || kind == PENDING_INVALID
        || RegionalForm::unpack_compact_checked(w, pending + CARRIER_PENDING_FORM).is_err()
    {
        return false;
    }
    let form_is_zero = packed_words_are_zero(w, pending + CARRIER_PENDING_FORM, FORM_WORDS);
    if kind == PENDING_NONE {
        if control != 0 || !form_is_zero {
            return false;
        }
    } else if kind == PENDING_DARK_BEFORE || kind == PENDING_DARK_TERMINAL {
        if next_contact != 0
            || !form_is_zero
            || phase != CONTINUATION_NONE
            || continuation_depth != 0
            || continuation_brick.len != 0
        {
            return false;
        }
    } else if kind == PENDING_SUB {
        if next_contact != 0
            || phase != CONTINUATION_NONE
            || continuation_depth != 0
            || continuation_brick.len != 0
        {
            return false;
        }
    } else if kind == PENDING_ENCLOSURE_CO_PRESENT || kind == PENDING_ENCLOSURE_TERMINAL {
        if (kind == PENDING_ENCLOSURE_CO_PRESENT && !form_is_zero)
            || (kind == PENDING_ENCLOSURE_TERMINAL && next_contact != 0)
            || !(phase == CONTINUATION_WORD_PERCEIVE || continuation_is_afferent(phase))
            || (phase == CONTINUATION_WORD_PERCEIVE && continuation_depth != 0)
            || (continuation_is_afferent(phase)
                && (continuation_depth == 0 || continuation_depth >= depth))
            || continuation_brick.len == 0
        {
            return false;
        }
    } else if kind == PENDING_PATH {
        if next_contact != 0
            || !(phase == CONTINUATION_WORD_PATH || continuation_is_efferent(phase))
        {
            return false;
        }
    } else {
        return false;
    }

    let mut d = 0usize;
    while d < depth {
        let base = carrier_enclosure_base(d);
        let mut slot = 0usize;
        while slot < REGISTER as usize {
            let at = base + slot * NODE_WORDS;
            if !packed_node_is_canonical(w, at) {
                return false;
            }
            let node = unpack_node(w, at);
            if node.len == 0 && !packed_words_are_zero(w, at, NODE_WORDS) {
                return false;
            }
            slot += 1;
        }
        let head = w[base + ENCLOSURE_HEAD] as usize;
        let live = w[base + ENCLOSURE_LIVE] as usize;
        if head >= REGISTER as usize
            || live > REGISTER as usize
            || (live < REGISTER as usize && head != live)
        {
            return false;
        }
        slot = 0;
        while slot < REGISTER as usize {
            let at = base + slot * NODE_WORDS;
            let node = unpack_node(w, at);
            let active = live == REGISTER as usize || slot < live;
            if (active && node.len == 0) || (!active && !packed_words_are_zero(w, at, NODE_WORDS)) {
                return false;
            }
            slot += 1;
        }
        if !packed_node_is_canonical(w, base + ENCLOSURE_STANCE)
            || !packed_face_is_canonical(w, base + ENCLOSURE_FLY)
            || w[base + ENCLOSURE_FLY_LIVE] > 1
        {
            return false;
        }
        let stance = unpack_node(w, base + ENCLOSURE_STANCE);
        if stance.len == 0 && !packed_words_are_zero(w, base + ENCLOSURE_STANCE, NODE_WORDS) {
            return false;
        }
        if w[base + ENCLOSURE_FLY_LIVE] == 0
            && !packed_words_are_zero(w, base + ENCLOSURE_FLY, FACE_WORDS)
        {
            return false;
        }
        if w[base + ENCLOSURE_FLY_LIVE] != 0
            && (stance.len == 0 || !unpack_face(w, base + ENCLOSURE_FLY).rotor_formed())
        {
            return false;
        }
        let enclosure = Enclosure::unpack_at(w, base);
        let mut word = 0usize;
        while word < ENCLOSURE_WORDS {
            if enclosure.packed_word(word) != w[base + word] {
                return false;
            }
            word += 1;
        }
        if kind == PENDING_ENCLOSURE_CO_PRESENT && d == continuation_depth {
            if live == 0 || next_contact == 0 || next_contact > live {
                return false;
            }
        }

        let deferred = carrier_deferred_base(depth, d);
        if !packed_node_is_canonical(w, deferred) {
            return false;
        }
        let sibling = unpack_node(w, deferred);
        if sibling.len == 0 && !packed_words_are_zero(w, deferred, CARRIER_DEFERRED_WORDS) {
            return false;
        }
        // A deferred sibling can stand only below the currently descending/unwinding hand. A
        // completed continuation and the word-path bridge carry no hidden interior branch.
        if (d == 0
            || phase == CONTINUATION_NONE
            || phase == CONTINUATION_WORD_PATH
            || d >= continuation_depth)
            && sibling.len != 0
        {
            return false;
        }
        d += 1;
    }
    true
}

/// Validate the exact header used by the generalized live host membrane. The carrier's enclosure
/// cores and dynamically grown co-presence are validated by their own typed snapshot; omitting
/// them here is a type boundary, not a projection.
pub fn live_body_header_is_canonical(w: &[u32]) -> bool {
    if w.len() != CARRIER_HEADER_WORDS
        || !packed_node_is_canonical(w, CARRIER_SUB_STANCE)
        || !packed_face_is_canonical(w, CARRIER_SUB_FLY)
        || w[CARRIER_SUB_FLY_LIVE] > 1
        || !LineageChannel::packed_row_is_canonical(w, CARRIER_CHANNEL)
    {
        return false;
    }
    let sub_stance = unpack_node(w, CARRIER_SUB_STANCE);
    if sub_stance.len == 0 && !packed_words_are_zero(w, CARRIER_SUB_STANCE, NODE_WORDS) {
        return false;
    }
    if w[CARRIER_SUB_FLY_LIVE] == 0 && !packed_words_are_zero(w, CARRIER_SUB_FLY, FACE_WORDS) {
        return false;
    }
    if w[CARRIER_SUB_FLY_LIVE] != 0
        && (sub_stance.len == 0 || !unpack_face(w, CARRIER_SUB_FLY).rotor_formed())
    {
        return false;
    }
    true
}

/// The receiving edge and sleep may cross only after the unfinished atom has completed. Canonical
/// continuation rows remain lawful across substrate installments but are not at rest.
pub fn carried_frame_is_at_rest(w: &[u32]) -> bool {
    carried_frame_is_canonical(w)
        && carrier_continuation_phase(w) == CONTINUATION_NONE
        && carrier_pending_kind(w) == PENDING_NONE
}

/// one grain's beat, returned up the thickening: the enclosed brick (if the grain completed), and
/// the beat's boundary instrumentation.
struct GrainBeat {
    brick: Option<Node>,
    landing: Landing,
    faces: u32,
    faces_founded: u32,
    completed: bool,
    deposited: bool,
}

/// The result of carrying one already-completed constituent into its receiving grain. `completed`
/// speaks only for the first receiving enclosure; deeper completions are consequences of that
/// hand-up and must not be counted again as additional source events.
struct Thickening {
    climbed: u32,
    completed: bool,
}

/// The deed's whole interior emanation at a driven site (§XXV): the dragged meeting's rotor RIDES
/// or FOUNDS by the 2nd-order test against the held rotor — the founding's hand is the χ test's
/// oriented Different, exactly as `cross()` reads it. An unformed meeting is the frame's horizon:
/// no fold here (darkness folds exactly once, at the tread's deposit). An unformed held rotor
/// cannot supply the fourth contact — the meeting cannot be 2nd-order tested and rides.
pub fn deed_emanation(
    met: &Face,
    fly: &Face,
    fly_live: bool,
    wound: bool,
) -> Option<DeedEmanation> {
    let rotor = soul::FormedRotor::of(met.arrow.aim, met.arrow.cross)?;
    if fly_live && wound {
        let chi = met.chi_against(fly)?;
        let hand = if chi.other.turn & 2 == 0 {
            WindingQuantum::ThisWay
        } else {
            WindingQuantum::ThatWay
        };
        return DeedEmanation::found(rotor, hand);
    }
    Some(DeedEmanation::ride(rotor))
}

impl<'a> ErosBody<'a> {
    /// a driven body over a caller-provided felt medium (the boundary's reservation) ⊕ a caller-provided
    /// CARRIER (the illicium's live vertical state — rows of `ENCLOSURE_WORDS`, the same one-buffer
    /// discipline as the regional form: no cap, only the reservation the caller affords).
    /// `frame_seed` founds the lineage's gauge anchor. `quantum` remains only as a pre-M4 seam
    /// compatibility input; the felt series has no shared digit or divisor.
    pub fn over(
        standing: &'a [u32],
        own: &'a mut [u32],
        axis: i64,
        frame_seed: &[u8],
        quantum: u32,
        carrier: &'a mut [u32],
    ) -> ErosBody<'a> {
        let frame = wind(frame_seed);
        // `quantum` stays in the pre-M4 boundary signature only; the felt series re-bases inside
        // its own Cogs and consumes no shared divisor.
        let _ = quantum;
        ErosBody {
            medium: Medium::over(standing, own, axis),
            frame,
            pole: place::origin(),
            // §XXV: the first difference founds the first frame — the channel seeds at the seed
            // frame's own place.
            channel: LineageChannel::from_first_difference(frame)
                .expect("the seed frame is one dead-bit difference — never the origin"),
            carrier: CarrierStore::Fixed(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance: Node {
                well: Cog::lit(1),
                place: place::origin(),
                len: 0,
            },
            sub_fly: face(place::origin(), place::origin(), place::origin()),
            sub_fly_live: false,
            dark_pending: 0,
            required_carrier_depth: 0,
        }
    }

    /// Found one lineage over a resident standing chart and its own reservation-sized local chart.
    /// Both axes are boundary-declared powers of two. The OWN buffer is `axis²` founded regional
    /// cells, not a plane over every standing place; each cell carries the construction that founded
    /// it so the true edge can re-ground it in the standing frame.
    pub fn over_resident(
        standing: &'a [u32],
        own: &'a mut [u32],
        standing_axis: i64,
        own_axis: i64,
        frame_seed: &[u8],
        quantum: u32,
        carrier: &'a mut [u32],
    ) -> ErosBody<'a> {
        assert!(
            standing_axis > 0 && standing_axis & (standing_axis - 1) == 0,
            "the standing chart has a dyadic boundary grain"
        );
        assert!(
            own_axis > 0 && own_axis & (own_axis - 1) == 0,
            "the lineage chart has a dyadic boundary grain"
        );
        assert!(
            standing.len() >= standing_axis as usize * standing_axis as usize * FORM_WORDS,
            "standing affords its declared chart"
        );
        assert!(
            own.len() >= own_axis as usize * own_axis as usize * OWN_CELL_WORDS,
            "OWN affords its declared lineage chart"
        );
        let frame = wind(frame_seed);
        let _ = quantum;
        ErosBody {
            medium: Medium::over_resident(standing, own, standing_axis, own_axis),
            frame,
            pole: place::origin(),
            channel: LineageChannel::from_first_difference(frame)
                .expect("the seed frame is one dead-bit difference — never the origin"),
            carrier: CarrierStore::Fixed(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance: Node {
                well: Cog::lit(1),
                place: place::origin(),
                len: 0,
            },
            sub_fly: face(place::origin(), place::origin(), place::origin()),
            sub_fly_live: false,
            dark_pending: 0,
            required_carrier_depth: 0,
        }
    }

    /// THE REGISTER POSTURE (`FORMULA §XXXII-c`): found one lineage whose local chart is BORN at
    /// the uncommitted rank-zero seed and widens at its own occupancy register's carry events.
    /// No grain is chosen and no extent of the light is consulted — a world-delivered stream has
    /// no length while it is being related. The boundary supplies growth through `OwnRecast`;
    /// the mapping is the law's (`zero_extend_own_cells`).
    pub fn over_register(
        standing: &'a [u32],
        own: &'a mut dyn OwnRecast,
        standing_axis: i64,
        frame_seed: &[u8],
        quantum: u32,
        carrier: &'a mut [u32],
    ) -> ErosBody<'a> {
        assert!(
            standing_axis > 0 && standing_axis & (standing_axis - 1) == 0,
            "the standing chart has a dyadic boundary grain"
        );
        assert!(
            own.words().len() >= OWN_CELL_WORDS,
            "the rank-zero chart affords its one cell"
        );
        let frame = wind(frame_seed);
        let _ = quantum;
        ErosBody {
            medium: Medium::over_register(standing, own, standing_axis),
            frame,
            pole: place::origin(),
            channel: LineageChannel::from_first_difference(frame)
                .expect("the seed frame is one dead-bit difference — never the origin"),
            carrier: CarrierStore::Fixed(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance: Node {
                well: Cog::lit(1),
                place: place::origin(),
                len: 0,
            },
            sub_fly: face(place::origin(), place::origin(), place::origin()),
            sub_fly_live: false,
            dark_pending: 0,
            required_carrier_depth: 0,
        }
    }

    /// Organ-neutral birth at a first difference which has already crossed the source organ's
    /// positional mouth.  Unlike the historical byte-seed constructor, no container spelling is
    /// re-read here.  `first_difference` is the carried frame itself; a source membrane commonly
    /// obtains it from [`atom_node`] on the current's first canonical relation atom.
    pub fn over_register_from_first_difference(
        standing: &'a [u32],
        own: &'a mut dyn OwnRecast,
        standing_axis: i64,
        first_difference: Place,
        carrier: &'a mut [u32],
    ) -> Option<ErosBody<'a>> {
        if standing_axis <= 0
            || standing_axis & (standing_axis - 1) != 0
            || own.words().len() < OWN_CELL_WORDS
        {
            return None;
        }
        let channel = LineageChannel::from_first_difference(first_difference)?;
        Some(ErosBody {
            medium: Medium::over_register(standing, own, standing_axis),
            frame: first_difference,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Fixed(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance: Node {
                well: Cog::lit(1),
                place: place::origin(),
                len: 0,
            },
            sub_fly: face(place::origin(), place::origin(), place::origin()),
            sub_fly_live: false,
            dark_pending: 0,
            required_carrier_depth: 0,
        })
    }

    /// Organ-neutral production birth over an allocation-free sparse OWN reservation.  The caller
    /// derives `cells.len()` from [`current_conduct_envelope`] for this exact current and carrier
    /// depth.  The standing chart is immutable receiver-before terrain shared lawfully by every
    /// co-present lineage; no source representation or octet grain enters this constructor.
    pub fn over_sparse_from_first_difference(
        standing: &'a [u32],
        cells: &'a mut [SparseOwnCell],
        standing_axis: i64,
        first_difference: Place,
        carrier: &'a mut [u32],
    ) -> Option<ErosBody<'a>> {
        if standing_axis <= 0 || standing_axis & (standing_axis - 1) != 0 {
            return None;
        }
        let axis = usize::try_from(standing_axis).ok()?;
        let required = axis.checked_mul(axis)?.checked_mul(FORM_WORDS)?;
        if standing.len() < required {
            return None;
        }
        let channel = LineageChannel::from_first_difference(first_difference)?;
        Some(ErosBody {
            medium: Medium::over_sparse(standing, cells, standing_axis)?,
            frame: first_difference,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Fixed(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance: Node {
                well: Cog::lit(1),
                place: place::origin(),
                len: 0,
            },
            sub_fly: face(place::origin(), place::origin(), place::origin()),
            sub_fly_live: false,
            dark_pending: 0,
            required_carrier_depth: 0,
        })
    }

    /// Growable-storage counterpart of `over_sparse_from_first_difference`.  Storage growth is a
    /// substrate act behind [`SparseOwnStorage`]; the body performs the identical sparse REGISTER
    /// transition and reports physical refusal to the enclosing transaction.
    pub fn over_sparse_storage_from_first_difference(
        standing: &'a [u32],
        storage: &'a mut dyn SparseOwnStorage,
        standing_axis: i64,
        first_difference: Place,
        carrier: &'a mut [u32],
    ) -> Option<ErosBody<'a>> {
        if standing_axis <= 0 || standing_axis & (standing_axis - 1) != 0 {
            return None;
        }
        let axis = usize::try_from(standing_axis).ok()?;
        let required = axis.checked_mul(axis)?.checked_mul(FORM_WORDS)?;
        if standing.len() < required {
            return None;
        }
        let channel = LineageChannel::from_first_difference(first_difference)?;
        Some(ErosBody {
            medium: Medium::over_sparse_storage(standing, storage, standing_axis)?,
            frame: first_difference,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Fixed(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance: Node {
                well: Cog::lit(1),
                place: place::origin(),
                len: 0,
            },
            sub_fly: face(place::origin(), place::origin(), place::origin()),
            sub_fly_live: false,
            dark_pending: 0,
            required_carrier_depth: 0,
        })
    }

    /// The fully sparse production posture: both the shared receiver-before terrain and this
    /// current's independently growing OWN surface are proportional to lived topology.  The
    /// standing slice is immutable and canonical at `standing_axis`; every co-present current may
    /// borrow that same before-face while retaining a separate cells/carrier reservation.
    pub fn over_sparse_world_from_first_difference(
        standing: &'a [SparseStandingCell],
        cells: &'a mut [SparseOwnCell],
        standing_axis: i64,
        first_difference: Place,
        carrier: &'a mut [u32],
    ) -> Option<ErosBody<'a>> {
        let channel = LineageChannel::from_first_difference(first_difference)?;
        Some(ErosBody {
            medium: Medium::over_sparse_standing(standing, cells, standing_axis)?,
            frame: first_difference,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Fixed(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance: Node {
                well: Cog::lit(1),
                place: place::origin(),
                len: 0,
            },
            sub_fly: face(place::origin(), place::origin(), place::origin()),
            sub_fly_live: false,
            dark_pending: 0,
            required_carrier_depth: 0,
        })
    }

    pub fn over_sparse_world_storage_from_first_difference(
        standing: &'a [SparseStandingCell],
        storage: &'a mut dyn SparseOwnStorage,
        standing_axis: i64,
        first_difference: Place,
        carrier: &'a mut dyn CarrierStorage,
    ) -> Option<ErosBody<'a>> {
        let channel = LineageChannel::from_first_difference(first_difference)?;
        Some(ErosBody {
            medium: Medium::over_sparse_world_storage(standing, storage, standing_axis)?,
            frame: first_difference,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Growing(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance: Node {
                well: Cog::lit(1),
                place: place::origin(),
                len: 0,
            },
            sub_fly: face(place::origin(), place::origin(), place::origin()),
            sub_fly_live: false,
            dark_pending: 0,
            required_carrier_depth: 0,
        })
    }

    /// General production birth over a receiver-owned standing-query surface.  The query maps the
    /// exact Soma construction into its own address species; neither a flat axis nor a storage
    /// coordinate enters the body.
    pub fn over_standing_world_storage_from_first_difference(
        standing: &'a dyn StandingQuery,
        storage: &'a mut dyn SparseOwnStorage,
        first_difference: Place,
        carrier: &'a mut dyn CarrierStorage,
    ) -> Option<ErosBody<'a>> {
        let channel = LineageChannel::from_first_difference(first_difference)?;
        Some(ErosBody {
            medium: Medium::over_standing_query_storage(standing, storage)?,
            frame: first_difference,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Growing(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance: Node {
                well: Cog::lit(1),
                place: place::origin(),
                len: 0,
            },
            sub_fly: face(place::origin(), place::origin(), place::origin()),
            sub_fly_live: false,
            dark_pending: 0,
            required_carrier_depth: 0,
        })
    }

    /// Ceiling-free organ-neutral production birth. Both the receiver and current-local OWN are
    /// addressed by the complete Soma construction; source modality and flat chart words are
    /// absent from this mouth.
    pub fn over_standing_world_ranked_storage_from_first_difference(
        standing: &'a dyn StandingQuery,
        storage: &'a mut dyn RankedOwnStorage,
        first_difference: Place,
        carrier: &'a mut dyn CarrierStorage,
    ) -> Option<ErosBody<'a>> {
        let channel = LineageChannel::from_first_difference(first_difference)?;
        Some(ErosBody {
            medium: Medium::over_standing_query_ranked_storage(standing, storage)?,
            frame: first_difference,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Growing(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance: Node {
                well: Cog::lit(1),
                place: place::origin(),
                len: 0,
            },
            sub_fly: face(place::origin(), place::origin(), place::origin()),
            sub_fly_live: false,
            dark_pending: 0,
            required_carrier_depth: 0,
        })
    }

    /// Continue one already-enacted organ-neutral body over a new sparse receiver-before surface.
    /// `K`, the open sub-illicium, dark passage, and carrier cross whole; the prior current-local
    /// OWN chart does not.  Its deeds have already integrated into standing and §XXXII-c requires
    /// that chart to die at the receiving edge, so this later current begins with a fresh rank-zero
    /// REGISTER. `carried` and `carrier` must still describe the same exact live body.
    pub fn resume_sparse_world_storage(
        standing: &'a [SparseStandingCell],
        storage: &'a mut dyn SparseOwnStorage,
        standing_axis: i64,
        carried: &[u32],
        carrier: &'a mut dyn CarrierStorage,
    ) -> Option<ErosBody<'a>> {
        let carrier_words = carrier.words();
        if carrier_words.is_empty() || carrier_words.len() % ENCLOSURE_WORDS != 0 {
            return None;
        }
        let depth = carrier_words.len() / ENCLOSURE_WORDS;
        let required = carrier_row_words(depth);
        if carried.len() != required || !carried_frame_is_at_rest(carried) {
            return None;
        }
        let enclosure_base = carrier_enclosure_base(0);
        if carried.get(enclosure_base..enclosure_base + carrier_words.len())? != carrier_words {
            return None;
        }
        let channel = LineageChannel::unpack(carried, CARRIER_CHANNEL)?;
        let frame = channel.frame().anchor;
        let dark_pending = seam::read_u32(carried, CARRIER_DARK_LO) as u64
            | ((seam::read_u32(carried, CARRIER_DARK_HI) as u64) << 32);
        let sub_stance = unpack_node(carried, CARRIER_SUB_STANCE);
        let sub_fly = unpack_face(carried, CARRIER_SUB_FLY);
        let sub_fly_live = seam::read_u32(carried, CARRIER_SUB_FLY_LIVE) != 0;
        Some(ErosBody {
            medium: Medium::over_sparse_world_storage(standing, storage, standing_axis)?,
            frame,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Growing(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance,
            sub_fly,
            sub_fly_live,
            dark_pending,
            required_carrier_depth: 0,
        })
    }

    /// Continue one exact carried body over an arbitrary receiver-owned standing-query surface.
    /// The carried frame is validated before OWN reset, exactly as in the flat compatibility
    /// posture; only the terrain addressing mouth differs.
    pub fn resume_standing_world_storage(
        standing: &'a dyn StandingQuery,
        storage: &'a mut dyn SparseOwnStorage,
        carried: &[u32],
        carrier: &'a mut dyn CarrierStorage,
    ) -> Option<ErosBody<'a>> {
        let carrier_words = carrier.words();
        if carrier_words.is_empty() || carrier_words.len() % ENCLOSURE_WORDS != 0 {
            return None;
        }
        let depth = carrier_words.len() / ENCLOSURE_WORDS;
        let required = carrier_row_words(depth);
        if carried.len() != required || !carried_frame_is_at_rest(carried) {
            return None;
        }
        let enclosure_base = carrier_enclosure_base(0);
        if carried.get(enclosure_base..enclosure_base + carrier_words.len())? != carrier_words {
            return None;
        }
        let header = LiveBodyHeader::from_words_checked(carried.get(..CARRIER_HEADER_WORDS)?)?;
        Self::resume_standing_world_storage_from_live_header(standing, storage, header, carrier)
    }

    /// Continue a generalized live body from its one exact header and complete typed carrier.
    /// Unlike the historical carried-frame mouth, this path has no flat REGISTER projection and
    /// therefore cannot silently omit dynamically admitted co-presence.
    pub fn resume_standing_world_storage_from_live_header(
        standing: &'a dyn StandingQuery,
        storage: &'a mut dyn SparseOwnStorage,
        header: LiveBodyHeader,
        carrier: &'a mut dyn CarrierStorage,
    ) -> Option<ErosBody<'a>> {
        let carrier_words = carrier.words();
        if carrier_words.is_empty() || carrier_words.len() % ENCLOSURE_WORDS != 0 {
            return None;
        }
        let carried = header.words();
        let channel = header.channel();
        let frame = channel.frame().anchor;
        let dark_pending = seam::read_u32(carried, CARRIER_DARK_LO) as u64
            | ((seam::read_u32(carried, CARRIER_DARK_HI) as u64) << 32);
        let sub_stance = unpack_node(carried, CARRIER_SUB_STANCE);
        let sub_fly = unpack_face(carried, CARRIER_SUB_FLY);
        let sub_fly_live = seam::read_u32(carried, CARRIER_SUB_FLY_LIVE) != 0;
        Some(ErosBody {
            medium: Medium::over_standing_query_storage(standing, storage)?,
            frame,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Growing(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance,
            sub_fly,
            sub_fly_live,
            dark_pending,
            required_carrier_depth: 0,
        })
    }

    /// Ceiling-free continuation of one complete carried body. The predecessor's exact live
    /// carrier returns whole while this receiving event begins a fresh ranked current-local OWN
    /// population over the new standing world.
    pub fn resume_standing_world_ranked_storage_from_live_header(
        standing: &'a dyn StandingQuery,
        storage: &'a mut dyn RankedOwnStorage,
        header: LiveBodyHeader,
        carrier: &'a mut dyn CarrierStorage,
    ) -> Option<ErosBody<'a>> {
        let carrier_words = carrier.words();
        if carrier_words.is_empty() || carrier_words.len() % ENCLOSURE_WORDS != 0 {
            return None;
        }
        let carried = header.words();
        let channel = header.channel();
        let frame = channel.frame().anchor;
        let dark_pending = seam::read_u32(carried, CARRIER_DARK_LO) as u64
            | ((seam::read_u32(carried, CARRIER_DARK_HI) as u64) << 32);
        let sub_stance = unpack_node(carried, CARRIER_SUB_STANCE);
        let sub_fly = unpack_face(carried, CARRIER_SUB_FLY);
        let sub_fly_live = seam::read_u32(carried, CARRIER_SUB_FLY_LIVE) != 0;
        Some(ErosBody {
            medium: Medium::over_standing_query_ranked_storage(standing, storage)?,
            frame,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Growing(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance,
            sub_fly,
            sub_fly_live,
            dark_pending,
            required_carrier_depth: 0,
        })
    }

    /// Exact live cells of the sparse production posture.  This is a borrowed body face; callers
    /// may retain it as a carried surface only after the current has completed.
    pub fn sparse_own_cells(&self) -> Option<&[SparseOwnCell]> {
        match &self.medium.own {
            OwnStore::Sparse { cells, state } => state.cells(&**cells),
            OwnStore::SparseStorage { storage, state } => state.cells(&**storage),
            _ => None,
        }
    }

    /// Exact current-local dyadic rank. Unlike `own_axis`, this face has no scalar-axis ceiling.
    pub fn own_rank(&self) -> u64 {
        match &self.medium.own {
            OwnStore::RankedStorage { state, .. } => state.rank(),
            _ => (self.medium.own_axis as u64).trailing_zeros() as u64,
        }
    }

    /// Exact arbitrary-width occupancy words for the production ranked posture. Historical
    /// postures retain their `u64` compatibility observer instead.
    pub fn ranked_own_occupancy_words(&self) -> Option<&[u64]> {
        match &self.medium.own {
            OwnStore::RankedStorage { storage, .. } => Some(storage.occupancy_words()),
            _ => None,
        }
    }

    pub fn ranked_own_cell_count(&self) -> Option<usize> {
        match &self.medium.own {
            OwnStore::RankedStorage { storage, .. } => Some(storage.cell_count()),
            _ => None,
        }
    }

    pub fn ranked_own_cell_face(&self, at: usize) -> Option<RankedOwnCellFace> {
        match &self.medium.own {
            OwnStore::RankedStorage { storage, .. } => storage.cell_face(at),
            _ => None,
        }
    }

    /// Physical sparse-storage refusal on this disposable current-local successor.  The body never
    /// converts it into a deed or clips the event; the membrane must discard the whole uncommitted
    /// current and leave the receiver-before owner installed.
    pub fn resource_refused(&self) -> bool {
        self.medium.resource_refused
    }

    pub fn required_carrier_depth(&self) -> Option<usize> {
        (self.required_carrier_depth != 0).then_some(self.required_carrier_depth)
    }

    /// The lineage chart's current grain — the register's own axis after whatever carry events
    /// its arrivals produced. A declared-grain posture returns its declared axis unchanged.
    pub fn own_axis(&self) -> i64 {
        assert!(
            !matches!(self.medium.own, OwnStore::RankedStorage { .. }),
            "a ranked OWN chart has no necessarily representable scalar axis"
        );
        self.medium.own_axis
    }

    /// Boundary read of the current-local chart register's occupied-grip population.  It is
    /// testimony beside the exact cells and never drives a body deed.
    pub fn own_occupancy(&self) -> u64 {
        assert!(
            !matches!(self.medium.own, OwnStore::RankedStorage { .. }),
            "a ranked OWN population has no necessarily representable u64 count"
        );
        self.medium.register.occupancy
    }

    /// THE BREATH READ (instrument, off the hot path, never a body input): `(releases, narrows)`
    /// — annihilation-released cells and retired digits over this current's life.
    pub fn breath(&self) -> (u64, u64) {
        (self.medium.releases, self.medium.narrows)
    }

    /// Continue one already-carried lineage over a new light without founding a replacement body.
    /// `carried` is the exact boundary row written by `pack_carried_frame`: its header restores the
    /// open sub-illicium and K, while its enclosure extent is still only the reservation afforded by
    /// the membrane. This constructor is the host mirror instrument for standing-life gates; on the
    /// card the same words never leave their resident buffer.
    pub fn resume(
        standing: &'a [u32],
        own: &'a mut [u32],
        axis: i64,
        frame_seed: &[u8],
        quantum: u32,
        carried: &'a mut [u32],
    ) -> ErosBody<'a> {
        let depth = carrier_row_depth(carried.len());
        let required = carrier_row_words(depth);
        assert!(
            depth != 0 && carried.len() >= required,
            "a continuing lineage carries one whole reserved row"
        );
        assert!(
            carried_frame_is_at_rest(&carried[..required]),
            "the legacy host resume cannot cut an unfinished within-atom continuation"
        );
        // The carried channel is the continuing frame. The arriving light's seed may found only a
        // genuinely new zeroed carrier; it cannot replace a live predecessor at resume.
        let _ = frame_seed;
        let channel = LineageChannel::unpack(carried, CARRIER_CHANNEL)
            .expect("a continuing lineage carries its complete channel K");
        let frame = channel.frame().anchor;
        let dark_pending = seam::read_u32(carried, CARRIER_DARK_LO) as u64
            | ((seam::read_u32(carried, CARRIER_DARK_HI) as u64) << 32);
        let sub_stance = unpack_node(carried, CARRIER_SUB_STANCE);
        let sub_fly = unpack_face(carried, CARRIER_SUB_FLY);
        let sub_fly_live = seam::read_u32(carried, CARRIER_SUB_FLY_LIVE) != 0;
        let enclosure_base = carrier_enclosure_base(0);
        let enclosure_words = depth * ENCLOSURE_WORDS;
        let carrier = &mut carried[enclosure_base..enclosure_base + enclosure_words];
        let _ = quantum;
        ErosBody {
            medium: Medium::over(standing, own, axis),
            frame,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Fixed(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance,
            sub_fly,
            sub_fly_live,
            dark_pending,
            required_carrier_depth: 0,
        }
    }

    /// Continue one already-carried lineage over its resident local chart. This is the founded-chart
    /// counterpart of `resume`: the carrier restores the same open illicium and K while standing
    /// and OWN retain their distinct boundary grains. The next light receives the standing body at
    /// `standing_axis` and deposits into the lineage's unchanged `own_axis` reservation.
    pub fn resume_resident(
        standing: &'a [u32],
        own: &'a mut [u32],
        standing_axis: i64,
        own_axis: i64,
        frame_seed: &[u8],
        quantum: u32,
        carried: &'a mut [u32],
    ) -> ErosBody<'a> {
        assert!(
            standing_axis > 0 && standing_axis & (standing_axis - 1) == 0,
            "the standing chart has a dyadic boundary grain"
        );
        assert!(
            own_axis > 0 && own_axis & (own_axis - 1) == 0,
            "the lineage chart has a dyadic boundary grain"
        );
        assert!(
            standing.len() >= standing_axis as usize * standing_axis as usize * FORM_WORDS,
            "standing affords its declared chart"
        );
        assert!(
            own.len() >= own_axis as usize * own_axis as usize * OWN_CELL_WORDS,
            "OWN affords its declared lineage chart"
        );
        let depth = carrier_row_depth(carried.len());
        let required = carrier_row_words(depth);
        assert!(
            depth != 0 && carried.len() >= required,
            "a continuing lineage carries one whole reserved row"
        );
        assert!(
            carried_frame_is_at_rest(&carried[..required]),
            "the legacy resident resume cannot cut an unfinished within-atom continuation"
        );
        // The carried channel is the continuing frame. The arriving light's seed may found only a
        // genuinely new zeroed carrier; it cannot replace a live predecessor at resume.
        let _ = frame_seed;
        let channel = LineageChannel::unpack(carried, CARRIER_CHANNEL)
            .expect("a continuing lineage carries its complete channel K");
        let frame = channel.frame().anchor;
        let dark_pending = seam::read_u32(carried, CARRIER_DARK_LO) as u64
            | ((seam::read_u32(carried, CARRIER_DARK_HI) as u64) << 32);
        let sub_stance = unpack_node(carried, CARRIER_SUB_STANCE);
        let sub_fly = unpack_face(carried, CARRIER_SUB_FLY);
        let sub_fly_live = seam::read_u32(carried, CARRIER_SUB_FLY_LIVE) != 0;
        let enclosure_base = carrier_enclosure_base(0);
        let enclosure_words = depth * ENCLOSURE_WORDS;
        let carrier = &mut carried[enclosure_base..enclosure_base + enclosure_words];
        let _ = quantum;
        ErosBody {
            medium: Medium::over_resident(standing, own, standing_axis, own_axis),
            frame,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Fixed(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance,
            sub_fly,
            sub_fly_live,
            dark_pending,
            required_carrier_depth: 0,
        }
    }

    /// Continue one already-carried lineage while the arriving light opens a fresh event-born
    /// REGISTER. The complete carrier restores K and the open illicium; no local chart face crosses
    /// the receiving edge. Consequently the new current begins from the same uncommitted rank-zero
    /// seed as `over_register`, and only its own FOIL arrivals choose its later grain.
    pub fn resume_register(
        standing: &'a [u32],
        own: &'a mut dyn OwnRecast,
        standing_axis: i64,
        frame_seed: &[u8],
        quantum: u32,
        carried: &'a mut [u32],
    ) -> ErosBody<'a> {
        assert!(
            standing_axis > 0 && standing_axis & (standing_axis - 1) == 0,
            "the standing chart has a dyadic boundary grain"
        );
        assert!(
            standing.len() >= standing_axis as usize * standing_axis as usize * FORM_WORDS,
            "standing affords its declared chart"
        );
        assert!(
            own.words().len() >= OWN_CELL_WORDS,
            "the rank-zero chart affords its one cell"
        );
        let depth = carrier_row_depth(carried.len());
        let required = carrier_row_words(depth);
        assert!(
            depth != 0 && carried.len() >= required,
            "a continuing lineage carries one whole reserved row"
        );
        assert!(
            carried_frame_is_at_rest(&carried[..required]),
            "the register resume cannot cut an unfinished within-atom continuation"
        );
        // The carried channel is the continuing frame. The arriving light's seed cannot replace a
        // live predecessor; it only supplies the boundary pair already present in the raw light.
        let _ = frame_seed;
        let channel = LineageChannel::unpack(carried, CARRIER_CHANNEL)
            .expect("a continuing lineage carries its complete channel K");
        let frame = channel.frame().anchor;
        let dark_pending = seam::read_u32(carried, CARRIER_DARK_LO) as u64
            | ((seam::read_u32(carried, CARRIER_DARK_HI) as u64) << 32);
        let sub_stance = unpack_node(carried, CARRIER_SUB_STANCE);
        let sub_fly = unpack_face(carried, CARRIER_SUB_FLY);
        let sub_fly_live = seam::read_u32(carried, CARRIER_SUB_FLY_LIVE) != 0;
        let enclosure_base = carrier_enclosure_base(0);
        let enclosure_words = depth * ENCLOSURE_WORDS;
        let carrier = &mut carried[enclosure_base..enclosure_base + enclosure_words];
        let _ = quantum;
        ErosBody {
            medium: Medium::over_register(standing, own, standing_axis),
            frame,
            pole: place::origin(),
            channel,
            carrier: CarrierStore::Fixed(carrier),
            thoughts: 0,
            terms_deposited: TermCounts::ZERO,
            sub_stance,
            sub_fly,
            sub_fly_live,
            dark_pending,
            required_carrier_depth: 0,
        }
    }

    /// the carrier's own extent — the reservation's rows (`carrier.len() / ENCLOSURE_WORDS`), NEVER
    /// a constant: the boundary's reservation is the caller's, like the pool.
    #[inline]
    pub fn carrier_depth(&self) -> usize {
        self.carrier.words().len() / ENCLOSURE_WORDS
    }

    /// Retain the exact first-person header independently of any particular carrier storage
    /// projection. The generalized live snapshot pairs this with the complete typed carrier.
    pub fn live_header(&self, cursor: u64) -> LiveBodyHeader {
        let mut words = [0u32; CARRIER_HEADER_WORDS];
        words[CARRIER_CURSOR_LO] = cursor as u32;
        words[CARRIER_CURSOR_HI] = (cursor >> 32) as u32;
        words[CARRIER_DARK_LO] = self.dark_pending as u32;
        words[CARRIER_DARK_HI] = (self.dark_pending >> 32) as u32;
        if self.sub_stance.len != 0 {
            pack_node(self.sub_stance, &mut words, CARRIER_SUB_STANCE);
        }
        if self.sub_fly_live {
            pack_face(self.sub_fly, &mut words, CARRIER_SUB_FLY);
            words[CARRIER_SUB_FLY_LIVE] = 1;
        }
        self.channel.pack(&mut words, CARRIER_CHANNEL);
        debug_assert!(live_body_header_is_canonical(&words));
        LiveBodyHeader { words }
    }

    /// Pack the WHOLE CARRIED FRAME into the card's one shared row layout. This is a boundary
    /// mirror instrument: cursor is the membrane's own progress through the current worldline;
    /// every live organ comes from this body; deferred slots are empty because a beat drains its
    /// thickening before returning. The pool never consults this rendering.
    pub fn pack_carried_frame(&self, cursor: u64, out: &mut [u32]) -> bool {
        if !self.carrier.legacy_projection_complete() {
            return false;
        }
        let depth = self.carrier_depth();
        let words = carrier_row_words(depth);
        if out.len() < words {
            return false;
        }
        let mut i = 0usize;
        while i < words {
            out[i] = 0;
            i += 1;
        }
        let header = self.live_header(cursor);
        out[..CARRIER_HEADER_WORDS].copy_from_slice(header.words());
        let enclosure_base = carrier_enclosure_base(0);
        let mut j = 0usize;
        while j < self.carrier.words().len() {
            out[enclosure_base + j] = self.carrier.words()[j];
            j += 1;
        }
        true
    }

    /// an enclosure at depth `d` — unpacked from the carrier's own row. Past the reservation's own
    /// extent there is no row to read: the unborn enclosure (`Enclosure::empty()`) stands there, the
    /// same lawful birth an all-zero row already reads as.
    fn enclosure(&self, d: usize) -> Enclosure {
        let base = d * ENCLOSURE_WORDS;
        if base + ENCLOSURE_WORDS > self.carrier.words().len() {
            return Enclosure::empty();
        }
        Enclosure::unpack_at(self.carrier.words(), base)
    }

    /// store an enclosure into the carrier's row at depth `d` (packed local, then copied — plain
    /// copies are lawful on the host). A depth past the reservation is never stored to (THE
    /// RETIREMENT handles it before this is ever called).
    fn enclosure_store(&mut self, d: usize, e: &Enclosure) {
        let base = d * ENCLOSURE_WORDS;
        if base + ENCLOSURE_WORDS > self.carrier.words().len() {
            return;
        }
        let mut row = [0u32; ENCLOSURE_WORDS];
        e.pack(&mut row);
        self.carrier.words_mut()[base..base + ENCLOSURE_WORDS].copy_from_slice(&row);
    }

    /// the STANDING THOUGHT — where depth 0's circulation stands (the pole of every word-grain perception).
    #[inline]
    pub fn stance(&self) -> Node {
        self.enclosure(0).stance
    }

    /// how many enclosures stand open across the whole carrier (a boundary read — an audit, scanning
    /// the reservation): a row whose stance is born or whose register carries co-presence counts.
    pub fn standing_enclosures(&self) -> u32 {
        let mut n = 0u32;
        let mut d = 0usize;
        let depth = self.carrier_depth();
        while d < depth {
            let e = self.enclosure(d);
            if e.stance.len != 0 || e.live > 0 {
                n += 1;
            }
            d += 1;
        }
        n
    }

    /// completed thoughts — the swing's cuts so far.
    #[inline]
    pub fn thoughts(&self) -> u32 {
        self.thoughts
    }

    /// How many chi-bearing FeltTerms successfully landed in this body's lane-local spool during
    /// the present light. This is membrane instrumentation, not a transition input or scalar read
    /// of the form; cancellations remain visible through the regional fiber/resultant topology.
    #[inline]
    pub fn deposited_terms(&self) -> TermCounts {
        self.terms_deposited
    }

    /// ★ THE CONE at a grip (`§XXVIII`) — the reader's whole past cone: PRE-LIGHT STANDING ⊕ this
    /// body's OWN deposits, joined as the felt series. The terrain read the drag consumes and the reads
    /// consult; the retired flow/sweep word is gone.
    #[inline]
    pub fn cone(&self, g: Grip) -> RegionalForm {
        self.medium.cone(g)
    }

    /// boundary read of depth 0's flywheel (the held rotor) — for mirror instrumentation.
    #[inline]
    pub fn flywheel(&self) -> (Face, bool) {
        let e = self.enclosure(0);
        (e.fly, e.fly_live)
    }

    /// Capture the historical atom-event receiver before that event changes any live state. The
    /// private sub-illicium belongs to an organ event's component walk and cannot lawfully make
    /// directed incidence depend on how that event happened to be decomposed for storage.
    pub fn event_receiver(&self) -> EventReceiver {
        self.event_receiver_at_source_grain(1)
            .expect("the historical atom event has one receiving grain")
    }

    /// Capture the actual receiver for a source constituent whose boundary has already completed
    /// at `source_grain`. Grain one enters carrier enclosure zero; every greater grain enters the
    /// correspondingly enclosing row. Reading beyond the mounted carrier is the exact unborn
    /// receiver and does not allocate or create an event.
    pub fn event_receiver_at_source_grain(&self, source_grain: u32) -> Option<EventReceiver> {
        let depth = usize::try_from(source_grain.checked_sub(1)?).ok()?;
        let enclosure = self.enclosure(depth);
        Some(EventReceiver {
            channel: self.channel,
            held: enclosure.fly,
            held_live: enclosure.fly_live,
        })
    }

    /// Form one source-supplied directed A2 contact against a previously captured target receiver.
    /// The target's complete past cone drags the meeting through the same `complete_cast` law as
    /// ordinary conduct. The resulting felt relation is returned to the cut configuration fold;
    /// this probe neither deposits into current-local OWN nor folds the lineage channel a second
    /// time. An unborn fourth contact or horizon remains an unresolved meeting with no emission.
    pub fn directed_event_contact(
        &mut self,
        receiver: EventReceiver,
        from: Place,
        to: Place,
    ) -> DirectedEventContact {
        self.directed_event_contact_at_source_grain(receiver, 1, from, to)
    }

    /// Form one directed meeting against the same pre-event enclosure which receives a completed
    /// source constituent at `source_grain`. This is not a search across scales: the source's
    /// declared boundary fixes the one enclosure, and an unborn enclosure remains an honest open
    /// fourth contact.
    pub fn directed_event_contact_at_source_grain(
        &mut self,
        receiver: EventReceiver,
        source_grain: u32,
        from: Place,
        to: Place,
    ) -> DirectedEventContact {
        // `to` is the arriving event face and `from` is the standing event face.  Their pole is
        // the target's complete pre-event lineage frame, never an event ordinal or the private
        // component-walk frame.  Reversing the supplied hand therefore reverses the actual A2
        // construction rather than merely changing listener testimony.
        let meeting = face(to, from, receiver.channel.frame().tip());
        if self.event_receiver_at_source_grain(source_grain) != Some(receiver)
            || !receiver.held_live
        {
            return DirectedEventContact {
                receiver,
                meeting,
                emission: None,
            };
        }
        let (_grip, _regional_form, met, standing_read) =
            self.complete_cast(meeting, &receiver.held, true);
        if met.arrow.at_horizon() {
            return DirectedEventContact {
                receiver,
                meeting,
                emission: None,
            };
        }
        let Some(chi) = met.chi_against(&receiver.held) else {
            return DirectedEventContact {
                receiver,
                meeting,
                emission: None,
            };
        };
        let wound = met.wound_against(&receiver.held);
        let winding = if !wound {
            WindingQuantum::None
        } else if chi.other.turn & 2 == 0 {
            WindingQuantum::ThisWay
        } else {
            WindingQuantum::ThatWay
        };
        let deed = match winding {
            WindingQuantum::None => FeltDeed::Ride,
            WindingQuantum::ThisWay => FeltDeed::FoundThis,
            WindingQuantum::ThatWay => FeltDeed::FoundThat,
        };
        DirectedEventContact {
            receiver,
            meeting,
            emission: Some(FeltEmission {
                position: cast_position(chi),
                term: FeltTerm { chi, winding },
                deed,
                standing_read,
            }),
        }
    }

    /// `K` — the body's lineage channel (§XXV): the ordered composition of its own deed emanations.
    #[inline]
    pub fn channel(&self) -> LineageChannel {
        self.channel
    }

    /// `Θ = TURN(K)` — the HOW-WOUND read of the channel, at a reach re-judged by the present
    /// landing (§XXVI — the reach is supplied at the read, never carried).
    #[inline]
    pub fn turn_at(&self, reach: Cog) -> WorldlineTurn {
        self.channel.turn_at(reach)
    }

    /// Restore `K` at a stroke resume — the membrane hands the carried frame's channel back to a
    /// freshly mounted body (`over()` seeds only the genesis channel; across a seam the worldline
    /// CONTINUES, never restarts). The membrane's stroke-resume mouth; every other advance of the
    /// channel is the body's own fold.
    #[inline]
    pub fn adopt_channel(&mut self, k: LineageChannel) {
        self.channel = k;
    }

    /// ONE FOLD of `K` (§XXV): the event's own deed emanation extends the channel. A degenerate
    /// composed rotor folds nothing — the event's other effects stand; never a panic.
    #[inline]
    fn fold_channel(&mut self, emanation: DeedEmanation) {
        if let Some(k) = self.channel.fold(emanation) {
            self.channel = k;
        }
    }

    /// place a construction without depositing — for reading induced change against a later drive.
    #[inline]
    pub fn place(&self, bytes: &[u8]) -> Grip {
        self.medium
            .place(bytes)
            .expect("this historical observer requires an exact flat receiver chart")
    }

    /// ★ DRIVE — consume one driven construction (`drive_flow` is A1's supplied current for this event). The
    /// Meno solve lands, the event's own deed folds the channel (§XXV), and the returned differential is what
    /// the next event may consume as charge. The pole then moves (W4: to the circulation's stance; here:
    /// trailing the arrival — mirror-grade, marked).
    pub fn drive(&mut self, bytes: &[u8], _drive_flow: u32) -> Landing {
        // §XXIV: this foil verb holds no flywheel — the meeting cannot be 2nd-order tested and
        // deposits NO shared relation (an unborn flywheel crosses nothing; A1's raw drive is
        // consumed by the lineage's interior, never fed as terrain). The construction is placed and
        // the deed rides the channel; the pole moves.
        let p = wind(bytes);
        let g = self.medium.flat_grip(p);
        let rel = face(p, self.pole, self.frame);
        if let Some(rotor) = soul::FormedRotor::of(rel.arrow.aim, rel.arrow.cross) {
            self.fold_channel(DeedEmanation::ride(rotor));
        }
        self.pole = p;
        Landing {
            cell: g,
            face: rel,
            meeting_ratio: rel.meeting_ratio(),
            founds: rel.founds(),
        }
    }

    /// §XXIX · THE COMPLETION — reconstruct a prior cast from this receiver's own second-order
    /// meeting, read the cone there, and let that standing form drag the meeting at the receiver's
    /// hand. An unborn fourth contact has only virtual light and therefore completes no crossing.
    #[inline]
    fn complete_cast(
        &mut self,
        meeting: Face,
        fly: &Face,
        fly_live: bool,
    ) -> (Option<Grip>, RegionalForm, Face, Option<StandingRead>) {
        if !fly_live {
            return (None, RegionalForm::UNBORN, meeting, None);
        }
        let Some(chi) = meeting.chi_against(fly) else {
            return (None, RegionalForm::UNBORN, meeting, None);
        };
        let position = cast_position(chi);
        let (grip, regional_form, standing, receiver_rank) = self.medium.cone_at(position);
        let standing_read = standing.occupied().then_some(StandingRead {
            position,
            receiver_rank,
            flat_grip: grip,
            form: standing,
        });
        (
            grip,
            regional_form,
            regional_form.drag(meeting),
            standing_read,
        )
    }

    /// ★ ONE DEED's felt term crosses into the medium (`§XXIV` — the deed's lawful crossing). Only a
    /// CHI-BEARING deed crosses: an unborn flywheel has no second-order invariant and deposits NOTHING.
    /// The winding quantum rides ONLY on FOUND (`wound`), its hand read from `chi.other`'s turn sign
    /// exactly as `deed_emanation`/`cross` read it. §XXIX derives the consequence's position only
    /// after that fourth contact: the projectively re-based χ grounds the cast on the cut.
    #[inline]
    fn cross_deed<T: FeltEmissionTarget>(
        &mut self,
        met: &Face,
        fly: &Face,
        fly_live: bool,
        wound: bool,
        standing_read: Option<StandingRead>,
        target: &mut T,
    ) {
        if !fly_live {
            return;
        }
        let Some(chi) = met.chi_against(fly) else {
            return;
        };
        let winding = if wound {
            if chi.other.turn & 2 == 0 {
                WindingQuantum::ThisWay
            } else {
                WindingQuantum::ThatWay
            }
        } else {
            WindingQuantum::None
        };
        let position = cast_position(chi);
        let term = FeltTerm { chi, winding };
        if self.medium.deposit_at(position, term) {
            let deed = match winding {
                WindingQuantum::None => FeltDeed::Ride,
                WindingQuantum::ThisWay => FeltDeed::FoundThis,
                WindingQuantum::ThatWay => FeltDeed::FoundThat,
            };
            match winding {
                WindingQuantum::None => self.terms_deposited.ride += 1,
                WindingQuantum::ThisWay => self.terms_deposited.found_this += 1,
                WindingQuantum::ThatWay => self.terms_deposited.found_that += 1,
            }
            target.emit(FeltEmission {
                position,
                term,
                deed,
                standing_read,
            });
        }
    }

    /// ★ PERCEIVE (W3 · THE EYES ⊕ W4 · THE POLE) — one arrival of driven light, WHOLE:
    ///
    /// 1. **THE LANDING, FROM THE STANCE (`FORMULA §IV` — the coupling).** The arrival relates with the
    ///    STANDING THOUGHT as its pole — perception forms against where the circulation stands, so what the
    ///    body has integrated bends how new light relates. Expectation is a position; no wire, no store.
    ///    (The bare `drive` verb keeps the trailing mirror-pole — it is the FOIL, not the machine.)
    /// 2. **THE GREY MATTER (W3).** A directed face term from each co-present register member to the arrival
    ///    (coherence IS collocation over time, and ONLY collocation — no semantics enter; the window is the grain).
    /// 3. **THE REINTEGRATOR (W4 — the swing decides; nothing scans, nothing scores).** The landing's own
    ///    three-body face is the cut: where it RIDES (in-plane — recognition), the thought CONTINUES — the
    ///    stance bonds the arrival (a higher blade; the composition re-bases as it climbs — the fold thickens)
    ///    and the new composition LANDS in the pool (the thought's mass deposits — production inducing
    ///    structure the next perception reads); where it FOUNDS (the aim orthogonal to the standing thought),
    ///    the thought COMPLETES — the swing's cut, the segmentation — and the arrival begins the new thought.
    ///
    /// A1 supplies the event's drive; only the formed second-order deed crosses as a FeltTerm. The
    /// register then slides (the oldest co-presence dissipates).
    pub fn perceive(&mut self, bytes: &[u8], drive_flow: u32) -> Perception {
        self.perceive_node(locate(bytes), drive_flow)
    }

    /// ★ W9 · the word grain's arrival as a NODE — the fold handed up by the living boundary (the
    /// brick; the cohered segment's completed invariant) enters the same perceive atom the byte-span
    /// arrival always did. One law, whichever grain supplied the arrival.
    pub fn perceive_node(&mut self, node: Node, drive_flow: u32) -> Perception {
        let mut target = NoFeltEmission;
        self.perceive_node_emitting(node, drive_flow, &mut target)
    }

    fn perceive_node_emitting<T: FeltEmissionTarget>(
        &mut self,
        node: Node,
        drive_flow: u32,
        target: &mut T,
    ) -> Perception {
        // depth 0 — the word grain's beat (the arrival's own).
        let beat0 = self.perceive_grain(0, node, drive_flow, target);
        let mut climbed = 0u32;
        if let Some(b) = beat0.brick {
            climbed = self.thicken(1, b, drive_flow, target);
        }
        Perception {
            landing: beat0.landing,
            faces: beat0.faces,
            faces_founded: beat0.faces_founded,
            thought_completed: beat0.completed,
            thought_deposited: beat0.deposited,
            climbed,
        }
    }

    /// ★ THE THICKENING (`FORMULA §XVIII`) — a completed brick re-bases into the next depth: it
    /// ARRIVES there (that enclosure's own perceive — the same verb) and the enclosure takes its own
    /// deed step (the hourglass whole at every grain). Completions from EITHER face — the arrival's
    /// cut (afferent) or the enclosure's own step cutting (efferent, the ratified two-worldline
    /// completion law — thicken on; the afferent brick thickens first (the worldline's order within
    /// the beat, depth-first: each brick's whole consequence before the next). Plain recursion is
    /// bounded structurally by actual completed depth. A growable boundary mounts the next row only
    /// when reached; a fixed or exhausted boundary reports pressure and the disposable passage
    /// stops without consuming the brick.
    fn thicken<T: FeltEmissionTarget>(
        &mut self,
        start: usize,
        first: Node,
        drive_flow: u32,
        target: &mut T,
    ) -> u32 {
        self.thicken_branch(start, first, drive_flow, target)
            .climbed
    }

    /// One depth-first branch of THE THICKENING. At a beat the efferent completion is held by this
    /// call frame while the afferent completion climbs first; therefore there is at most one
    /// deferred efferent per open depth, and call depth can never exceed the mounted carrier depth.
    fn thicken_branch<T: FeltEmissionTarget>(
        &mut self,
        k: usize,
        brick: Node,
        drive_flow: u32,
        target: &mut T,
    ) -> Thickening {
        if k >= self.carrier_depth() {
            match self.carrier.ensure_depth(k + 1) {
                CarrierGrowth::Present if k < self.carrier_depth() => {}
                CarrierGrowth::FixedBoundary | CarrierGrowth::Refused | CarrierGrowth::Present => {
                    self.required_carrier_depth = k + 1;
                    self.medium.resource_refused = true;
                    return Thickening {
                        climbed: 0,
                        completed: false,
                    };
                }
            }
        }
        let beat = self.perceive_grain(k, brick, drive_flow, target);
        let step = self.path_grain(k, drive_flow, target);
        let completed = beat.brick.is_some() || step.brick.is_some();
        let mut climbed = 1u32;
        // The afferent brick's whole consequence precedes the deferred efferent sibling — the same
        // order the old LIFO carry implemented, now without an authored extent.
        if let Some(ab) = beat.brick {
            climbed += self.thicken_branch(k + 1, ab, drive_flow, target).climbed;
            if self.resource_refused() {
                return Thickening { climbed, completed };
            }
        }
        if let Some(sb) = step.brick {
            climbed += self.thicken_branch(k + 1, sb, drive_flow, target).climbed;
        }
        Thickening { climbed, completed }
    }

    /// ★ ONE ENCLOSURE'S PERCEIVE (`FORMULA §XVIII(b,d)`) — the whole perceive atom on depth `k`'s
    /// own apparatus: the landing FROM THE ENCLOSURE'S STANCE (the coupling at this grain), the grey
    /// matter from the ENCLOSURE'S reach (coherence is collocation at every grain — bricks collocated
    /// in the carrier's time), the swing 2nd-order against the ENCLOSURE'S flywheel with the standing
    /// sweep dragging the meeting (§XIV at every grain). A completion emits THE BRICK — the enclosed
    /// stance, crossing RE-BASED (§XVIII(a): the completion re-base; the interior scale encloses).
    fn perceive_grain<T: FeltEmissionTarget>(
        &mut self,
        k: usize,
        node: Node,
        _drive_flow: u32,
        target: &mut T,
    ) -> GrainBeat {
        let mut e = self.enclosure(k);
        // 1 · the landing, from the enclosure's stance (the pole re-pointed — the coupling). §XXIV: the
        // raw arrival deposits NO shared relation (A1's drive is consumed by the lineage's interior);
        // the terrain-derived flow fields retire (the felt series carries the standing form now).
        let g_cell = self.medium.flat_grip(node.place);
        let rel_face = face(node.place, e.stance.place, self.frame);
        let landing = Landing {
            cell: g_cell,
            face: rel_face,
            meeting_ratio: rel_face.meeting_ratio(),
            founds: rel_face.founds(),
        };
        // 2 · the grey matter — faces from the enclosure's co-presence (oldest→newest). Each register
        // member→arrival face crosses ONE felt term (`§XXIV`/RULE 3): `chi = that_face.chi_against(the
        // depth's fly)`, no winding hand — the recognition is a ride. An unborn flywheel crosses nothing.
        let mut faces = 0u32;
        let mut faces_founded = 0u32;
        let mut i = 0usize;
        while i < e.live {
            let idx = (e.head + (REGISTER as usize) - e.live + i) % (REGISTER as usize);
            let c = e.register[idx];
            if c.len != 0 {
                let fc = face(c.place, node.place, self.frame);
                self.cross_deed(&fc, &e.fly, e.fly_live, false, None, target);
                faces += 1;
                if bond(c, node, self.frame).1.founds() {
                    faces_founded += 1;
                }
            }
            i += 1;
        }
        let overflow = self.carrier.co_present_overflow_len(k);
        let mut overflow_at = 0usize;
        while overflow_at < overflow {
            let Some(c) = self.carrier.co_present_overflow_node(k, overflow_at) else {
                self.medium.resource_refused = true;
                break;
            };
            if c.len != 0 {
                let fc = face(c.place, node.place, self.frame);
                self.cross_deed(&fc, &e.fly, e.fly_live, false, None, target);
                let Some(next_faces) = faces.checked_add(1) else {
                    self.medium.resource_refused = true;
                    break;
                };
                faces = next_faces;
                if bond(c, node, self.frame).1.founds() {
                    let Some(next_founded) = faces_founded.checked_add(1) else {
                        self.medium.resource_refused = true;
                        break;
                    };
                    faces_founded = next_founded;
                }
            }
            overflow_at += 1;
        }
        if self.medium.resource_refused {
            return GrainBeat {
                brick: None,
                landing,
                faces,
                faces_founded,
                completed: false,
                deposited: false,
            };
        }
        // 3 · the reintegrator — THE SWING (`§XIII`) with §XXIX's second pyramid: this receiver
        // reconstructs the positional-χ cast from its own meeting ⊕ flywheel, then the cone there
        // drags the meeting at this hand. First-order virtual light has no standing address.
        let (_rel_grip, rel_form, met, standing_read) = if e.stance.len != 0 {
            self.complete_cast(landing.face, &e.fly, e.fly_live)
        } else {
            (None, RegionalForm::UNBORN, landing.face, None)
        };
        // THE FRAME'S HORIZON: an unconstructible relating is not read — the beat passes through.
        let dark = met.arrow.at_horizon();
        let node_at_pole = {
            let dr = node.place.0.sub(self.frame.0);
            let di = node.place.1.sub(self.frame.1);
            dr.mag == 0 && di.mag == 0
        };
        let wound = if dark {
            false
        } else if e.fly_live {
            met.wound_against(&e.fly)
        } else {
            met.founds()
        };
        // §XXV: the beat's own deed folds `K` — ride or found by the 2nd-order test; the horizon
        // folds nothing (darkness folds exactly once, at the tread's deposit).
        if let Some(deed) = deed_emanation(&met, &e.fly, e.fly_live, wound) {
            self.fold_channel(deed);
        }
        let mut completed = false;
        let mut deposited = false;
        let mut brick: Option<Node> = None;
        if e.stance.len == 0 {
            // the first brick begins the enclosure's first thought (the enclosure instantiates — the
            // same birth law as every stance; no birth detection) — unless the arrival stands at the pole.
            if !node_at_pole {
                e.stance = node;
            }
        } else if dark {
            // the frame's horizon — the beat passes through unread (the reach still slides below).
        } else if wound {
            completed = true; // the cut — the enclosure's thought completes
            if k == 0 {
                self.thoughts = self.thoughts.wrapping_add(1);
            }
            // ★ THE BRICK (§XVIII(a)) — the enclosed stance crosses re-based: the completion
            // re-base removes the interior's common rank (the enclosure's scale becomes gauge).
            let old = e.stance;
            let sr = old.place.0.sub(self.frame.0);
            let si = old.place.1.sub(self.frame.1);
            let (sr2, si2) = rebase_pair(sr, si);
            let the_brick = Node {
                well: old.well,
                place: (self.frame.0.add(sr2), self.frame.1.add(si2)),
                len: old.len,
            };
            // THE FOUND DEED CROSSES (`§XXIV` ⊕ §XXIX): the winding hand and positional cast are
            // both read from the whole post-drag χ. FOUND pays curvature.
            self.cross_deed(&met, &e.fly, e.fly_live, true, standing_read, target);
            brick = Some(the_brick);
            e.stance = node;
            // The completed construction now exists as `the_brick` at the next grain. Its lower
            // arrivals no longer remain independently co-present; the triggering arrival begins
            // the successor construction and is admitted below after this release.
            if self.carrier.release_co_present(k, &mut e) != CarrierGrowth::Present {
                self.medium.resource_refused = true;
                return GrainBeat {
                    brick: None,
                    landing,
                    faces,
                    faces_founded,
                    completed: false,
                    deposited: false,
                };
            }
            // THE CUT'S PRECESSION: the groove never zeroes — dragged by the cone at the cut's own grip.
            if e.fly_live {
                e.fly = rel_form.drag(e.fly);
            }
        } else {
            // the thought continues — bond ⊕ RIDE deed. §XXIV/RULE 2: a face-relating crosses one felt
            // term at that face's grip, no winding (the ride is cheap — the terrain already paid).
            let (mol, _rel) = bond(e.stance, node, self.frame);
            self.cross_deed(&met, &e.fly, e.fly_live, false, standing_read, target);
            deposited = true;
            e.stance = mol;
            e.fly = met;
            e.fly_live = true;
        }
        // The arrival joins this enclosure's co-present light. The fixed/card compatibility row
        // retains its historical ring. A growable production carrier retains every admitted
        // relation beyond that prefix; only an actual body closure may dissipate it.
        match self.carrier.admit_co_present(k, &mut e, node) {
            CarrierGrowth::Present => {}
            CarrierGrowth::FixedBoundary | CarrierGrowth::Refused => {
                self.medium.resource_refused = true;
                return GrainBeat {
                    brick: None,
                    landing,
                    faces,
                    faces_founded,
                    completed: false,
                    deposited: false,
                };
            }
        }
        self.enclosure_store(k, &e);
        GrainBeat {
            brick,
            landing,
            faces,
            faces_founded,
            completed,
            deposited,
        }
    }

    /// ★ W6 · THE PATHING — ONE STEP of the brain's own current at depth 0 (the word grain), with the
    /// step's own completions thickening the carrier (`§XVIII`: the efferent brick is a completion too).
    pub fn path(&mut self, drive_flow: u32) -> Pathing {
        let mut target = NoFeltEmission;
        self.path_emitting(drive_flow, &mut target)
    }

    fn path_emitting<T: FeltEmissionTarget>(&mut self, drive_flow: u32, target: &mut T) -> Pathing {
        let step = self.path_grain(0, drive_flow, target);
        if let Some(b) = step.brick {
            self.thicken(1, b, drive_flow, target);
        }
        step
    }

    /// ★ ONE GRAIN'S DEED STEP (`§XIII` run forward, on depth `k`'s own stance and flywheel): the held
    /// rotor places the next grip (no candidate set); the STANDING SWEEP there drags the meeting
    /// (§XIV); the current deposits as it passes (A1); the swing rides along — the cut PRECESSES the
    /// groove, re-bases the enclosure (the ratified completion re-base) and emits it as THE BRICK.
    fn path_grain<T: FeltEmissionTarget>(
        &mut self,
        k: usize,
        _drive_flow: u32,
        target: &mut T,
    ) -> Pathing {
        let mut e = self.enclosure(k);
        // structural precondition, not a threshold: before a standing thought with a live groove
        // there is no held rotor to run forward (the enclosure's eyes wake the enclosure's brain).
        if e.stance.len == 0 || !e.fly_live {
            return Pathing {
                grip: None,
                regional_form: RegionalForm::UNBORN,
                cut: false,
                stepped: false,
                meeting_rotor: (Cog::lit(0), Cog::lit(0)),
                brick: None,
            };
        }
        // 1 · the deed-run-forward: next = F + Δ_fly·(S − F).
        let (fa, fc) = (e.fly.arrow.aim, e.fly.arrow.cross);
        let sr = e.stance.place.0.sub(self.frame.0);
        let si = e.stance.place.1.sub(self.frame.1);
        let next: Place = (
            fa.mul(sr).sub(fc.mul(si)).add(self.frame.0),
            fc.mul(sr).add(fa.mul(si)).add(self.frame.1),
        );
        // 2 · the second pyramid: reconstruct the positional-χ cast from this step's own meeting
        // against its held groove; the cone at that cut address completes the crossing by drag.
        let meeting = face(next, e.stance.place, self.frame);
        let (g, regional_form, met, standing_read) = self.complete_cast(meeting, &e.fly, true);
        let dark = met.arrow.at_horizon();
        let wound = if dark {
            false
        } else {
            met.wound_against(&e.fly)
        };
        // §XXV: the step's own deed folds `K` (the groove is live here by the precondition above).
        if let Some(deed) = deed_emanation(&met, &e.fly, true, wound) {
            self.fold_channel(deed);
        }
        // 3 · the swing's move: the cut precesses the groove and CROSSES a FOUND term at the brick's
        // ground; the ride re-aims the groove and crosses a RIDE term at the step's own grip; darkness
        // holds. §XXIV/RULE 2 — the deed's own consequence stands at its grip; A1's drive rides interior.
        let mut cut = false;
        if dark {
            // inertia — no torque from a meeting this pole cannot construct.
        } else if wound {
            cut = true;
            if k == 0 {
                self.thoughts = self.thoughts.wrapping_add(1);
            }
            // ★ THE COMPLETION RE-BASE (ratified): the utterance encloses — its interior scale becomes
            // gauge; the ENCLOSURE CROSSES as the brick (§XVIII: the efferent completion thickens).
            let sr2 = next.0.sub(self.frame.0);
            let si2 = next.1.sub(self.frame.1);
            let (sr3, si3) = rebase_pair(sr2, si2);
            let enclosed = Node {
                well: e.stance.well,
                place: (self.frame.0.add(sr3), self.frame.1.add(si3)),
                len: e.stance.len,
            };
            // THE FOUND DEED casts its post-drag χ (against the pre-precession groove).
            self.cross_deed(&met, &e.fly, true, true, standing_read, target);
            e.fly = regional_form.drag(e.fly); // the receiver's completion precesses the groove
            let (fa2, fc2) = rebase_pair(e.fly.arrow.aim, e.fly.arrow.cross);
            e.fly.arrow.aim = fa2;
            e.fly.arrow.cross = fc2;
            e.stance = enclosed;
            // The enclosed face has already handed upward. Retaining its former arrivals here
            // would keep discharged constituency active and make later co-presence cumulative.
            if self.carrier.release_co_present(k, &mut e) != CarrierGrowth::Present {
                self.medium.resource_refused = true;
                return Pathing {
                    grip: g,
                    regional_form,
                    cut: false,
                    stepped: false,
                    meeting_rotor: (met.arrow.cross, met.arrow.aim),
                    brick: None,
                };
            }
            self.enclosure_store(k, &e);
            return Pathing {
                grip: g,
                regional_form,
                cut,
                stepped: true,
                meeting_rotor: (met.arrow.cross, met.arrow.aim),
                brick: Some(enclosed),
            };
        } else {
            self.cross_deed(&met, &e.fly, true, false, standing_read, target);
            e.fly = met;
        }
        e.stance = Node {
            well: e.stance.well,
            place: next,
            len: e.stance.len,
        };
        self.enclosure_store(k, &e);
        Pathing {
            grip: g,
            regional_form,
            cut,
            stepped: true,
            meeting_rotor: (met.arrow.cross, met.arrow.aim),
            brick: None,
        }
    }

    /// ★ W7 · LIVE — one arrival of light through the WHOLE CIRCUIT (the brain/eyes frame closed): the eye
    /// lands it (`perceive`), and the same given current hands on into ONE deed-run-forward step of the
    /// brain (`path`). One arrival, one traversal of the circuit's length — there is no clock but the light
    /// itself, and no ratio anywhere: the beat is structural. The coupling back needs no wire: the step
    /// moves the STANCE (and §IV says perception lands from the stance) and its deposits stand in the ONE
    /// pool the next arrival's terrain read passes — the active thought bends perception through the pole
    /// and through the gravity, both already law. Before the first groove the brain has nothing to run
    /// forward and the step lawfully does not happen (`stepped = false`) — the eyes wake the brain.
    pub fn live(&mut self, bytes: &[u8], drive_flow: u32) -> (Perception, Pathing) {
        let p = self.perceive(bytes, drive_flow);
        let step = self.path(drive_flow);
        (p, step)
    }

    /// ★ W9 · LIVE_ATOM — ONE ATOM of raw light through the LIVING BOUNDARY (the scope's first grain).
    /// The atom is the signed difference of two adjacent packets, located exactly as `locate` walks it —
    /// one atom standing alone. It arrives in the SUB-ILLICIUM by the same one verb: the meeting from
    /// the sub-stance, DRAGGED by the standing terrain at its own grip (the tire feels the road), the
    /// swing riding (the sub-composition climbs) or completing — and the completion is THE FOLD: the
    /// cohered segment's node hands UP as the word grain's arrival (the brick), where the whole upper
    /// circuit responds (perceive_node ⊕ the brain's step). Equal adjacent packets walk one dead bit —
    /// the frame's own place — and pass the horizon unread (runs of sameness are dark to this pole).
    /// A1 per grain: every event consumes the given drive; nothing schedules, the light is the clock.
    pub fn live_atom(&mut self, prev: u8, cur: u8, drive_flow: u32) -> AtomEvent {
        self.live_relation_atom(crate::boundary::difference(cur, prev), drive_flow)
    }

    /// ★ THE NATIVE RELATION MOUTH — one canonical difference-shape through the same living
    /// boundary without requiring an octet container. Source organs derive `relation` at their
    /// own material grain; this body neither knows nor reconstructs that world representation.
    /// This is the exact one-relation compatibility face. Production plural events enter once
    /// through [`Self::live_event_incidence_emitting`], which conducts their internal path without
    /// turning its constituents into separate source events. [`Self::live_atom`] is the exact
    /// octet-organ compatibility face.
    pub fn live_relation_atom(&mut self, relation: Cog, drive_flow: u32) -> AtomEvent {
        let mut target = NoFeltEmission;
        self.live_relation_atom_emitting(relation, drive_flow, &mut target)
    }

    /// The native relation mouth with one exact accepted-deed output aperture.  Every successful
    /// OWN deposit made by the relation—including recursive enclosure and path deeds—is emitted in
    /// the body's lived order.  The target is output-only and cannot change the Swing.
    pub fn live_relation_atom_emitting<T: FeltEmissionTarget>(
        &mut self,
        relation: Cog,
        drive_flow: u32,
        target: &mut T,
    ) -> AtomEvent {
        if self.resource_refused() {
            return AtomEvent {
                fold: None,
                perception: None,
                step: None,
            };
        }
        // ★ THE DARK TREAD (ratified 2026-07-09): a zero-magnitude difference is a STATIC LINKAGE —
        // `I = −dΦ/dt`: it induces NOTHING per atom (the dark is free; paying a transition per interior
        // atom is level-slamming, the DC crime). The sameness EXTENDS: the passage accumulates its
        // supplied drive and deposits WHOLE at its completion. Not an event — no Θ, no swing, no feed.
        if relation.mag == 0 {
            self.dark_pending += drive_flow as u64;
            return AtomEvent {
                fold: None,
                perception: None,
                step: None,
            };
        }
        // a resolving difference COMPLETES any standing dark passage — the tread deposits, over time.
        self.deposit_dark_tread(target);
        let n = atom_node(relation);
        self.live_constructed_node_emitting(n, drive_flow, target)
    }

    /// ★ THE COMPLETE EVENT INCIDENCE MOUTH — conduct the source-declared relation path inside one
    /// actual parent event. The path order is an internal parameter of the presented geometry, not
    /// additional source chronology: the caller mounts one predecessor, advances its event cursor
    /// once, and exposes no intermediate standing successor.
    ///
    /// Each resolving relation passes through the existing sub-illicium. A completed sub-grain
    /// construction therefore hands its fold immediately into the recursive carrier before the
    /// next internal relation is considered. Zero relations are exact annihilations inside the
    /// co-present incidence: they remain counted in the event and in its boundary address, but do
    /// not manufacture a dark time interval. The one A1 action remains at the parent event boundary
    /// and is never copied or divided across constituents.
    pub fn live_event_incidence_emitting<I: EventIncidence, T: FeltEmissionTarget>(
        &mut self,
        incidence: &I,
        action: Cog,
        target: &mut T,
    ) -> EventEmanation {
        debug_assert!(!incidence.is_empty());
        debug_assert!(action.mag != 0);

        // A body-local dark tread can exist only through the historical one-relation mouth. Close
        // it once at this real resolving boundary; the production membrane's whole-dark event
        // residual is carried separately and never distributed over this internal path.
        self.deposit_dark_tread(target);

        let mut resolving = 0u64;
        let mut folds = 0u64;
        let mut at = 0usize;
        while at < incidence.len() {
            let relation = incidence.relation(at);
            if relation.mag != 0 {
                resolving += 1;
                let consequence =
                    self.live_constructed_node_emitting(atom_node(relation), 0, target);
                if consequence.fold.is_some() {
                    folds += 1;
                }
                if self.resource_refused() {
                    break;
                }
            }
            at += 1;
        }
        EventEmanation {
            cells: incidence.len() as u64,
            incidences: incidence.len().saturating_sub(1) as u64,
            resolving_cells: resolving,
            formed_incidences: 0,
            compounds: 0,
            folds,
            receiver: self.event_receiver(),
        }
    }

    /// Historical compatibility mouth for a source which genuinely presents one already-completed
    /// node at its declared material grain. It is not the production plural-event mouth: a complete
    /// encoding of several relations does not prove that their construction has completed.
    pub fn live_event_node_emitting<T: FeltEmissionTarget>(
        &mut self,
        node: Node,
        action: Cog,
        target: &mut T,
    ) -> AtomEvent {
        if self.resource_refused() {
            return AtomEvent {
                fold: None,
                perception: None,
                step: None,
            };
        }
        // ActiveCut validation guarantees a non-zero canonical action. Keep the value in this
        // complete-event call even though no universal numeric actuation law is licensed: dropping
        // it at the membrane would make later body/world-specific action impossible to carry
        // exactly, while multiplying it into `node` would fabricate topology.
        debug_assert!(action.mag != 0);
        // A complete resolving event closes the one genuinely preceding dark interval. Zero
        // coordinates inside this node remain co-present geometry; they never become extra treads.
        self.deposit_dark_tread(target);
        self.live_constructed_node_emitting(node, 0, target)
    }

    /// Receive one source complex whose boundary has already completed at `source_grain`. The
    /// composed node enters its enclosing carrier row directly: its cells do not replay as atom
    /// instants and its declared dimensional boundary is not reset through the sub-illicium.
    /// `true` reports only whether this receiving grain completed during the one event.
    pub fn live_completed_event_node_at_grain_emitting<T: FeltEmissionTarget>(
        &mut self,
        node: Node,
        source_grain: u32,
        action: Cog,
        target: &mut T,
    ) -> bool {
        if self.resource_refused() {
            return false;
        }
        debug_assert!(action.mag != 0);
        let Some(depth) = source_grain
            .checked_sub(1)
            .and_then(|depth| usize::try_from(depth).ok())
        else {
            self.medium.resource_refused = true;
            return false;
        };
        self.deposit_dark_tread(target);
        self.thicken_branch(depth, node, 0, target).completed
    }

    /// Shared bright construction law. The node has already been composed at the receiving event
    /// grain; this function must never be used to turn its interior components into clock ticks.
    fn live_constructed_node_emitting<T: FeltEmissionTarget>(
        &mut self,
        n: Node,
        drive_flow: u32,
        target: &mut T,
    ) -> AtomEvent {
        // §XXIV: the raw sub-arrival deposits NO shared relation (A1's drive rides the interior).
        let rel = face(n.place, self.sub_stance.place, self.frame);
        // ★ the tire feels the CONE at positional χ — the receiver constructs the second pyramid.
        let (_rel_grip, rel_form, met, standing_read) = if self.sub_stance.len != 0 {
            let fly = self.sub_fly;
            self.complete_cast(rel, &fly, self.sub_fly_live)
        } else {
            (None, RegionalForm::UNBORN, rel, None)
        };
        let dark = met.arrow.at_horizon();
        let node_at_pole = {
            let dr = n.place.0.sub(self.frame.0);
            let di = n.place.1.sub(self.frame.1);
            dr.mag == 0 && di.mag == 0
        };
        let wound = if dark {
            false
        } else if self.sub_fly_live {
            met.wound_against(&self.sub_fly)
        } else {
            met.founds()
        };
        // §XXV: the atom event's own deed folds `K` — the same one law at every grain.
        if let Some(deed) = deed_emanation(&met, &self.sub_fly, self.sub_fly_live, wound) {
            self.fold_channel(deed);
        }
        let mut fold: Option<Node> = None;
        if self.sub_stance.len == 0 {
            if !node_at_pole {
                self.sub_stance = n;
            }
        } else if dark {
            // the frame's horizon — the atom passes through unread.
        } else if wound {
            // ★ THE FOLD — the sub-segment completes; the brick is born at the boundary, crossing
            // RE-BASED (§XVIII(a) — the one law at every seam: the interior scale encloses as gauge).
            let old = self.sub_stance;
            let fr = old.place.0.sub(self.frame.0);
            let fi = old.place.1.sub(self.frame.1);
            let (fr2, fi2) = rebase_pair(fr, fi);
            let the_fold = Node {
                well: old.well,
                place: (self.frame.0.add(fr2), self.frame.1.add(fi2)),
                len: old.len,
            };
            // THE FOUND DEED casts the whole post-drag χ (§XXIV ⊕ §XXIX).
            let fly = self.sub_fly;
            let fly_live = self.sub_fly_live;
            self.cross_deed(&met, &fly, fly_live, true, standing_read, target);
            fold = Some(the_fold);
            self.sub_stance = n;
            if self.sub_fly_live {
                self.sub_fly = rel_form.drag(self.sub_fly); // the receiver's completion precesses
            }
        } else {
            let (mol, _r) = bond(self.sub_stance, n, self.frame);
            // THE RIDE DEED CROSSES at the relating's grip (§XXIV/RULE 2 — no winding hand).
            let fly = self.sub_fly;
            let fly_live = self.sub_fly_live;
            self.cross_deed(&met, &fly, fly_live, false, standing_read, target);
            self.sub_stance = mol;
            self.sub_fly = met;
            self.sub_fly_live = true;
        }
        // the fold reaches the word grain — the whole upper circuit per brick.
        let (perception, step) = match fold {
            Some(f) => {
                let p = self.perceive_node_emitting(f, drive_flow, target);
                if self.resource_refused() {
                    (Some(p), None)
                } else {
                    let s = self.path_emitting(drive_flow, target);
                    (Some(p), Some(s))
                }
            }
            None => (None, None),
        };
        AtomEvent {
            fold,
            perception,
            step,
        }
    }

    /// ★ THE DARK TREAD'S DEPOSIT — the completed passage lays its whole accumulated drive AT THE
    /// FRAME'S OWN PLACE (§XVII verbatim): the lineage's ANCHOR — its first difference, never reset.
    /// All silence is one place PER LINEAGE: its own pole. (The old universal dead-bit place was the
    /// excised card's common-frame compromise — the fixed common frame died with §XXIV.) ONE
    /// transition per hand of the glyph (a passage deeper than the u32 hand deposits in the hand's
    /// own chunks — the boundary's grain, not a guard). The passage is ONE relating: one completed
    /// silence = ONE fold of `K` (§XXV — duration, not order). The pending drive lands whole.
    fn deposit_dark_tread<T: FeltEmissionTarget>(&mut self, target: &mut T) {
        if self.dark_pending == 0 {
            return;
        }
        let action = Cog::lit(self.dark_pending as i64);
        self.dark_pending = 0;
        self.resolve_dark_action_emitting(action, target);
    }

    /// Resolve one native event-current tread whole. The active membrane retains an unresolved
    /// sequence of wholly static events as an open residual and calls this only at the first
    /// resolving relation or the current's actual boundary. Thus plural relation components do not
    /// multiply one event's action, while the historical octet mouth keeps its exact u64 tread.
    /// `action` is the complete A1 current carried by that interval, not a score or a drive chosen
    /// by Soma.
    pub fn resolve_dark_action(&mut self, action: Cog) {
        let mut target = NoFeltEmission;
        self.resolve_dark_action_emitting(action, &mut target)
    }

    /// Resolve one completed dark event interval and emit its one accepted term.  The membrane
    /// attaches the interval's exact event-cause span; the body owns only the physical deed.
    pub fn resolve_dark_action_emitting<T: FeltEmissionTarget>(
        &mut self,
        action: Cog,
        target: &mut T,
    ) {
        if action.mag == 0 {
            return;
        }
        self.fold_channel(DeedEmanation::dark());
        // PRESENTED 2026-07-09 (Brandon, in-line): the completed passage's one term is PURE SAME — the
        // groove's norm scaled by the accumulated quanta (other = 0, no hand): "deposits whole" as the
        // term's magnitude; the DC law holds (nothing per atom, one term per passage).
        let norm = if self.sub_fly_live {
            let a = self.sub_fly.arrow.aim;
            let c = self.sub_fly.arrow.cross;
            a.mul(a).add(c.mul(c))
        } else {
            Cog::lit(1)
        };
        let same = norm.mul(action);
        let position = self.channel.frame().anchor;
        let term = FeltTerm {
            chi: soul::Chi {
                same,
                other: Cog::lit(0),
            },
            winding: WindingQuantum::None,
        };
        if self.medium.deposit_at(position, term) {
            self.terms_deposited.dark += 1;
            target.emit(FeltEmission {
                position,
                term,
                deed: FeltDeed::Dark,
                standing_read: None,
            });
        }
    }

    /// ★ the light's end completes the standing dark passage (the stream's own boundary is a resolving
    /// edge). The membrane calls this before any whole-body audit; a body dropped mid-passage would
    /// otherwise carry in-flight mass the pool cannot see.
    pub fn flush_dark(&mut self) {
        let mut target = NoFeltEmission;
        self.deposit_dark_tread(&mut target);
    }

    /// test-only instrument: stage one felt term into the OWN region at a bare grip (staging a terrain
    /// difference without moving any body state). Never a boundary verb — the membrane crosses deeds.
    #[cfg(test)]
    pub(crate) fn stage_own(&mut self, g: Grip, term: FeltTerm) {
        if self.medium.deposit(g, term) {
            match term.winding {
                WindingQuantum::None => self.terms_deposited.ride += 1,
                WindingQuantum::ThisWay => self.terms_deposited.found_this += 1,
                WindingQuantum::ThatWay => self.terms_deposited.found_that += 1,
            }
        }
    }
}

/// ★ W9 · one atom of raw light through the LIVING BOUNDARY: the sub-grain's own event, and — when a
/// segment completed — the FOLD (the brick) with the whole upper circuit's response to it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct AtomEvent {
    pub fold: Option<Node>,
    pub perception: Option<Perception>,
    pub step: Option<Pathing>,
}

/// The compressed outward face of one parent event's internal incidence sweep. The live carrier,
/// rather than this scalar testimony, retains every still-open construction. `receiver` is the
/// complete post-event lineage aperture which can participate in a genuinely later event.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct EventEmanation {
    pub cells: u64,
    pub incidences: u64,
    pub resolving_cells: u64,
    pub formed_incidences: u64,
    pub compounds: u64,
    pub folds: u64,
    pub receiver: EventReceiver,
}

/// ONE PATHING step — the brain's own current, surfaced for boundary instrumentation and the reads: the grip
/// visited, the exact regional form read there, and whether the swing cut (a thought completed).
/// `stepped = false` means the body had no standing thought/groove to run forward.
///
/// `regional_form` is the active topology read. `meeting_rotor` is only the step's first-order
/// dragged meeting, not `χ`; it remains beside the form for historical trace comparison. A lawful
/// crossing exists only after a formed flywheel supplies the fourth contact.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Pathing {
    /// Exact flat compatibility projection where one exists. The accepted deed carries its full
    /// position independently, so a deep ranked receiver never fabricates a `u32` grip.
    pub grip: Option<Grip>,
    pub regional_form: RegionalForm,
    pub cut: bool,
    pub stepped: bool,
    /// (cross, aim) — the WHOLE Cogs, never `.face()`-collapsed: a live rotor whose rank has descended
    /// past the flat glyph's window reads `0` at the face while carrying full content.
    pub meeting_rotor: (Cog, Cog),
    /// ★ §XVIII: the step's cut encloses — the efferent brick (the completed utterance's node),
    /// already re-based, thickening into the next depth.
    pub brick: Option<Node>,
}

/// ONE PERCEPTION event — the arrival's cell landing ⊕ the faces its co-presence grew ⊕ the reintegrator's
/// move (continued or cut). FeltTerm counts are read once from the body at the light boundary.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Perception {
    pub landing: Landing,
    pub faces: u32,
    pub faces_founded: u32,
    /// the swing cut here — the standing thought completed and the arrival began the next.
    pub thought_completed: bool,
    /// the thought continued — its composition deposited into the lane-local regional form.
    pub thought_deposited: bool,
    /// ★ §XVIII: how many depths of the carrier this beat's completions thickened (a boundary count).
    pub climbed: u32,
}
#[cfg(test)]
#[path = "manifold_tests.rs"]
mod tests;
