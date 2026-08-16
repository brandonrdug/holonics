//! channel — THE LIGHTNING CHANNEL `K` (`FORMULA §XXV–XXVI`). A lineage is the ordered
//! composition of its own deed emanations. The same construction has two interior reads:
//! `FRAME(K)`, the basis at its tip, and `TURN(K, r)`, the composed winding about the reach
//! re-judged at the present landing.
//!
//! A bare rotor product is not enough: the present two-dimensional rotor face is commutative and
//! a closed phase loop can return to its starting glyph. `K` therefore carries the rotor as an
//! AFFINE action along its own leader. If `B` is the standing basis, `P` the ordered sweep from the
//! first-difference anchor, and `E` the deed rotor, one ordered fold is
//!
//! ```text
//! B' = B E
//! P' = P + B'
//! ```
//!
//! This is the smallest faithful lift of “each step of the leader extends the channel”: `A` then
//! `B` and `B` then `A` generally have the same terminal rotor face but different tips. The lifted
//! winding keeps the integer circuit on the universal cover, so even a rotor loop whose basis and
//! tip return still deposits its directed passage. No event counter, list, clock, normalization,
//! or carried reach participates.

use crate::num::{self, Cog, Rung, COG_WORDS, RUNG_WORDS};
use crate::place::{self, Place};
use crate::seam::{row_fits, SliceWordSeam, WordSeam};
use crate::soul::{FormedRotor, RotorRatio};

/// The oriented integer quantum deposited by a deed. `ThisWay` and `ThatWay` are relative to this
/// lineage's gauge; neither is a global clockwise label. RIDE and the static dark completion add no
/// founding quantum, though their ordered basis motion can still complete a circuit.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum WindingQuantum {
    None,
    ThisWay,
    ThatWay,
}

/// The deed's WHOLE interior emanation. A horizon exposes only χ ⊕ winding; this rotor remains in
/// the lineage and becomes its next frame. FOUND keeps the dragged meeting rotor and adds the
/// oriented unit blade when folded. A completed dark passage is one identity fold—one passage,
/// irrespective of how many identical boundary packets it contained.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
#[repr(u32)]
pub enum DeedEmanation {
    Ride(FormedRotor),
    Found {
        rotor: FormedRotor,
        winding: WindingQuantum,
    },
    Dark,
}

impl DeedEmanation {
    #[inline]
    pub fn ride(rotor: FormedRotor) -> DeedEmanation {
        DeedEmanation::Ride(rotor)
    }

    /// A founding is constructible only with an oriented quantum. `None` is a RIDE, not a FOUND
    /// sentinel.
    #[inline]
    pub fn found(rotor: FormedRotor, winding: WindingQuantum) -> Option<DeedEmanation> {
        match winding {
            WindingQuantum::None => None,
            WindingQuantum::ThisWay | WindingQuantum::ThatWay => {
                Some(DeedEmanation::Found { rotor, winding })
            }
        }
    }

    #[inline]
    pub fn dark() -> DeedEmanation {
        DeedEmanation::Dark
    }

    /// The dragged meeting rotor before the founding blade is folded into it. Darkness has no
    /// meeting rotor.
    #[inline]
    pub fn meeting_rotor(self) -> Option<FormedRotor> {
        match self {
            DeedEmanation::Ride(rotor) | DeedEmanation::Found { rotor, .. } => Some(rotor),
            DeedEmanation::Dark => None,
        }
    }

    #[inline]
    pub fn founding(self) -> WindingQuantum {
        match self {
            DeedEmanation::Found { winding, .. } => winding,
            DeedEmanation::Ride(_) | DeedEmanation::Dark => WindingQuantum::None,
        }
    }

    /// The rotor which enters the basis. FOUND is literally the dragged meeting rotor ⊕ its
    /// oriented unit blade. The unit is frame-relative `±i`; no scalar score selects it.
    fn basis_rotor(self) -> Option<FormedRotor> {
        let (rotor, quantum) = match self {
            DeedEmanation::Ride(rotor) => (rotor, WindingQuantum::None),
            DeedEmanation::Found { rotor, winding } => (rotor, winding),
            DeedEmanation::Dark => return Some(FormedRotor::identity()),
        };
        let cross = match quantum {
            WindingQuantum::None => rotor.cross(),
            WindingQuantum::ThisWay => rotor.cross().add(Cog::lit(1)),
            WindingQuantum::ThatWay => rotor.cross().sub(Cog::lit(1)),
        };
        FormedRotor::of(rotor.aim(), cross)
    }
}

/// The non-cancelling integer face of the channel's winding. The two arms are kept apart so a
/// circuit followed by its opposite remains two deposited passages, never a return to zero. The
/// arms can only grow through `LineageChannel::fold`; a bounded withdrawal fixture may check a
/// prior spelling but cannot mutate the standing channel backward or reconstruct prior state.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct OrientedWinding {
    this_way: Rung,
    that_way: Rung,
}

impl OrientedWinding {
    pub const ZERO: OrientedWinding = OrientedWinding {
        this_way: Rung::ZERO,
        that_way: Rung::ZERO,
    };

    #[inline]
    pub fn this_way(self) -> Rung {
        self.this_way
    }

    #[inline]
    pub fn that_way(self) -> Rung {
        self.that_way
    }

    #[inline]
    fn deposit(self, quantum: WindingQuantum) -> OrientedWinding {
        match quantum {
            WindingQuantum::None => self,
            WindingQuantum::ThisWay => OrientedWinding {
                this_way: self.this_way.add(Rung::of(1)),
                ..self
            },
            WindingQuantum::ThatWay => OrientedWinding {
                that_way: self.that_way.add(Rung::of(1)),
                ..self
            },
        }
    }

    fn withdraw(self, quantum: WindingQuantum) -> Option<OrientedWinding> {
        let one = Rung::of(1);
        match quantum {
            WindingQuantum::None => Some(self),
            WindingQuantum::ThisWay => {
                let prior = self.this_way.sub(one);
                if prior.neg {
                    None
                } else {
                    Some(OrientedWinding {
                        this_way: prior,
                        ..self
                    })
                }
            }
            WindingQuantum::ThatWay => {
                let prior = self.that_way.sub(one);
                if prior.neg {
                    None
                } else {
                    Some(OrientedWinding {
                        that_way: prior,
                        ..self
                    })
                }
            }
        }
    }
}

/// `FRAME(K)`: the channel read as a basis at its tip. The gauge anchor and ordered sweep remain a
/// pair: collapsing them into one finite `Place` erased a zero-faced genesis construction in the
/// first bounded restore fixture. `tip()` is the local landing projection; the frame keeps both
/// construction terms without claiming a universal inverse.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LivingFrame {
    pub anchor: Place,
    pub sweep: Place,
    pub basis: FormedRotor,
}

impl LivingFrame {
    /// The pole projected for the next relating. An empty sweep is the identity action, so the
    /// genesis anchor returns structurally rather than being normalized by a zero-valued add.
    #[inline]
    pub fn tip(self) -> Place {
        if self.sweep == place::origin() {
            self.anchor
        } else {
            (
                self.anchor.0.add(self.sweep.0),
                self.anchor.1.add(self.sweep.1),
            )
        }
    }
}

/// ★ THE DEPOSIT CENSUS of a lineage: what it has laid down, and where its basis stands.
///
/// **RENAMED FROM `DepositCensus` 2026-08-15, because it is not an action and the name claimed it
/// was.** An exact collision was exhibited: from `basis = 1`, a single `FoundThat(2+2i)` and the
/// pair `Ride(−2−i); Ride(−1)` both return `deposits = (0,1)` and `basis = 2+i`, while their sweeps
/// are `2+i` and `0`. The census cannot separate those two histories.
///
/// **The cause is one shared register.** `fold_formed_into` writes
/// `winding.deposit(phase).deposit(founding)`, so an oriented circuit crossing `C` and a founding
/// quantum `F` land in the same two hands and only `D = C + F` survives. A true action would need
///
/// ```text
///     S / quantum  =  2·pi·(C₊ − C₋)  +  arg(basis)        with  C = D − F
///     the exact undivided return being   (C₊, C₋, basis)  ⊕  (F₊, F₋)
/// ```
///
/// and this carrier holds neither `C` nor `F` apart. Its signed phase error against a true action is
/// exactly `2·pi·(F₊ − F₋)`.
///
/// **And forcing the separation is not obviously right.** An action is normally a **quotient of
/// histories**; requiring one to identify every history is a stronger demand than physics makes.
/// So this is renamed to what it is rather than repaired into what it was called: **an oriented,
/// species-erased deposit census plus a terminal weighted rotor.** That is a real invariant. It is
/// not an action, and no reading may quote it as one.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct DepositCensus {
    /// deposited passages, both hands retained separately and never netted. **Two species share
    /// this register** — circuit crossings and foundings — and it does not separate them.
    pub deposits: OrientedWinding,
    /// where the basis stands now — the undivided rotor pair `(aim, cross)`, weighted
    pub basis: FormedRotor,
}

/// `C`, the HOW-WOUND read of `K`: its ordered sweep, present basis, and integer circuit. This is
/// deliberately not a scalar turn count; two histories with the same circuit count can still have
/// different sweep/basis constructions.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ComposedTurn {
    pub anchor: Place,
    pub sweep: Place,
    pub basis: FormedRotor,
    pub winding: OrientedWinding,
}

/// `Θ = (C; r)`. Reach enters only at this read and is never a field of `LineageChannel`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct WorldlineTurn {
    pub c: ComposedTurn,
    pub r: Cog,
}

/// `K`, the lineage interior. There is no empty/default channel: the first difference constructs
/// the first frame. Anchor and sweep stay paired so the zero-faced first difference cannot be lost;
/// FRAME and TURN are literal reads of this one construction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LineageChannel {
    anchor: Place,
    sweep: Place,
    basis: FormedRotor,
    winding: OrientedWinding,
}

impl LineageChannel {
    /// The first difference is the first frame. `place::origin()` is not a difference and cannot
    /// construct a channel; the genesis dead extension is structurally distinct even though its
    /// finite magnitude face is zero.
    #[inline]
    pub fn from_first_difference(first_difference: Place) -> Option<LineageChannel> {
        if first_difference == place::origin() {
            None
        } else {
            Some(LineageChannel::from_located_first_difference(
                first_difference,
            ))
        }
    }

    /// Birth from a difference that has already crossed the positional mouth. `locate`/`atom_node`
    /// always return a live or dead extension rather than `place::origin()`, including for a
    /// zero-faced difference. Callers at that boundary therefore need no optional aggregate.
    #[inline]
    pub fn from_located_first_difference(first_difference: Place) -> LineageChannel {
        LineageChannel {
            anchor: first_difference,
            sweep: place::origin(),
            basis: FormedRotor::identity(),
            winding: OrientedWinding::ZERO,
        }
    }

    /// ★ THE DEPOSIT CENSUS — what this lineage has laid down. NOT an action; see `DepositCensus`.
    ///
    /// The fold is `basis_{k+1} = basis_k · deed_k` (phases ADD) and `sweep_{k+1} = sweep_k +
    /// basis_{k+1}` (amplitudes SUM), so unrolling gives `basis_n = Π deed_j`, which is one path's
    /// amplitude, and `sweep_n = Σ_k Π_{j<k} deed_j`, which is the sum over prefix paths. The
    /// accumulated turn is therefore the accumulated ACTION:
    ///
    /// ```text
    ///     S / quantum  =  (whole turns)  +  (the fractional remainder)
    /// ```
    ///
    /// Both halves are returned and **neither is divided**. `quanta` keeps the two hands apart, as
    /// `OrientedWinding` always does — a circuit followed by its opposite is two deposited passages,
    /// never a return to zero — and `remainder` is the undivided rotor pair.
    ///
    /// There is no clock in it, no sensor, and no temperature — temperature is the receiver's
    /// exchange rate between the count chart and the energy chart, and it may not enter an
    /// invariant.
    ///
    /// **BOUNDARY, corrected 2026-08-15 and load-bearing.** `quanta` counts **deposited passages of
    /// two species and does not separate them**: `fold_formed_into` writes
    /// `winding.deposit(phase).deposit(founding)`, so an oriented circuit crossing and a founding
    /// quantum land in the same two hands. The clean identity
    ///
    /// ```text
    ///     S / quantum  =  2·pi·circuits  +  arg(basis)
    /// ```
    ///
    /// therefore holds only for `circuits = quanta − foundings`, **and this carrier does not carry
    /// the founding count separately.** So `quanta` is a floor on deposited passages, not on whole
    /// turns of accumulated action, and a reading that treats it as the latter overcounts by one
    /// turn per founding. Separating the registers is a change to the fold's own law and is not
    /// made here; the boundary is stated instead.
    #[inline]
    pub fn deposit_census(self) -> DepositCensus {
        DepositCensus {
            deposits: self.winding,
            basis: self.basis,
        }
    }

    #[inline]
    pub fn frame(self) -> LivingFrame {
        LivingFrame {
            anchor: self.anchor,
            sweep: self.sweep,
            basis: self.basis,
        }
    }

    /// Reach is re-judged by the present landing and supplied to the read. It is impossible to
    /// carry or increment it inside `K` because `LineageChannel` has no reach member.
    #[inline]
    pub fn turn_at(self, reach: Cog) -> WorldlineTurn {
        WorldlineTurn {
            c: ComposedTurn {
                anchor: self.anchor,
                sweep: self.sweep,
                basis: self.basis,
                winding: self.winding,
            },
            r: reach,
        }
    }

    /// `K' = FOLD(K, DEED_EMANATION)` in the worldline's own order. Rotor composition re-aims the
    /// basis; that freshly aimed basis extends the leader. A phase circuit and a founding deficit
    /// deposit independently into the integer winding.
    pub fn fold(self, emanation: DeedEmanation) -> Option<LineageChannel> {
        let mut next = self;
        if !self.fold_into(emanation, &mut next) {
            return None;
        }
        Some(next)
    }

    /// The same fold for a substrate whose entry ABI cannot transport an optional aggregate. An
    /// unformed deed leaves K unchanged, exactly as the optional mouth's `None` branch does.
    #[inline(never)]
    pub fn fold_or_self(self, emanation: DeedEmanation) -> LineageChannel {
        let mut next = self;
        self.fold_into(emanation, &mut next);
        next
    }

    /// One implementation of the channel fold serves both boundary mouths. `next` begins as the
    /// prior channel and is written only after both deed and composed basis are structurally formed.
    #[inline(never)]
    fn fold_into(self, emanation: DeedEmanation, next: &mut LineageChannel) -> bool {
        let (rotor_aim, rotor_cross, founding) = match emanation {
            DeedEmanation::Ride(rotor) => (rotor.aim(), rotor.cross(), WindingQuantum::None),
            DeedEmanation::Found { rotor, winding } => (rotor.aim(), rotor.cross(), winding),
            DeedEmanation::Dark => (Cog::lit(1), Cog::lit(0), WindingQuantum::None),
        };
        self.fold_formed_into(rotor_aim, rotor_cross, founding, next)
    }

    /// Scalar lowering mouth for a deed whose meeting rotor is already formed. It carries the same
    /// whole arms and oriented founding hand as `DeedEmanation`, without requiring an aggregate enum
    /// in a shader function signature.
    #[inline(never)]
    pub fn fold_formed_hand_or_self(
        self,
        rotor_aim: Cog,
        rotor_cross: Cog,
        found_this: bool,
        found_that: bool,
    ) -> LineageChannel {
        let mut next = self;
        let founding = if found_this {
            WindingQuantum::ThisWay
        } else if found_that {
            WindingQuantum::ThatWay
        } else {
            WindingQuantum::None
        };
        self.fold_formed_into(rotor_aim, rotor_cross, founding, &mut next);
        next
    }

    fn fold_formed_into(
        self,
        rotor_aim: Cog,
        rotor_cross: Cog,
        founding: WindingQuantum,
        next: &mut LineageChannel,
    ) -> bool {
        let deed_aim = rotor_aim;
        let deed_cross = match founding {
            WindingQuantum::None => rotor_cross,
            WindingQuantum::ThisWay => rotor_cross.add(Cog::lit(1)),
            WindingQuantum::ThatWay => rotor_cross.sub(Cog::lit(1)),
        };
        if !FormedRotor::arms_form(deed_aim, deed_cross) {
            return false;
        }
        let next_aim = self
            .basis
            .aim()
            .mul(deed_aim)
            .sub(self.basis.cross().mul(deed_cross));
        let next_cross = self
            .basis
            .cross()
            .mul(deed_aim)
            .add(self.basis.aim().mul(deed_cross));
        if !FormedRotor::arms_form(next_aim, next_cross) {
            return false;
        }
        let next_basis = FormedRotor::from_formed_arms(next_aim, next_cross);
        let phase = circuit_crossing(
            self.basis.aim(),
            self.basis.cross(),
            next_basis.aim(),
            next_basis.cross(),
        );
        let winding = self.winding.deposit(phase).deposit(founding);
        *next = LineageChannel {
            anchor: self.anchor,
            sweep: (
                self.sweep.0.add(next_basis.aim()),
                self.sweep.1.add(next_basis.cross()),
            ),
            basis: next_basis,
            winding,
        };
        true
    }

    /// Bounded algebra/gauge read of one fold. The formal conjugate product returns a rotor-ratio
    /// witness—never an interior division—beside the prior sweep and winding. This does not run the
    /// channel backward, remove a deposit, reconstruct prior state, or by itself test time parity.
    pub fn restore_before(self, emanation: DeedEmanation) -> Option<ChannelCause> {
        let deed = emanation.basis_rotor()?;
        let norm = deed
            .aim()
            .mul(deed.aim())
            .add(deed.cross().mul(deed.cross()));
        let prior_basis = RotorRatio {
            aim_num: self
                .basis
                .aim()
                .mul(deed.aim())
                .add(self.basis.cross().mul(deed.cross())),
            cross_num: self
                .basis
                .cross()
                .mul(deed.aim())
                .sub(self.basis.aim().mul(deed.cross())),
            den: norm,
        };
        // A positive norm scales both prior-basis arms equally, so its numerator pair has the same
        // hand and crosses the same branch ray in this bounded fixture. The formal circuit phase can
        // therefore be unwound without dividing the ratio; this is not universal cause recovery.
        let phase = circuit_crossing(
            prior_basis.aim_num,
            prior_basis.cross_num,
            self.basis.aim(),
            self.basis.cross(),
        );
        let winding = self
            .winding
            .withdraw(emanation.founding())?
            .withdraw(phase)?;
        Some(ChannelCause {
            anchor: self.anchor,
            sweep: (
                self.sweep.0.sub(self.basis.aim()),
                self.sweep.1.sub(self.basis.cross()),
            ),
            basis: prior_basis,
            winding,
        })
    }
}

/// `K`'s carried-frame extent: anchor (2 Cogs) ⊕ sweep (2 Cogs) ⊕ basis (2 Cogs) ⊕ winding
/// (2 Rungs). ONE MOUTH — the seam packing lives with `K`; the membrane and carrier derive their
/// offsets from this constant, never a re-spoken literal.
pub const CHANNEL_WORDS: usize = 6 * COG_WORDS + 2 * RUNG_WORDS;

/// K read once, as one construction. The scalar reader accumulates the unborn face while each
/// packed word grounds; no all-zero pre-scan rereads the channel before decoding it.
#[derive(Clone, Copy)]
struct ChannelRead {
    anchor: Place,
    sweep: Place,
    basis_aim: Cog,
    basis_cross: Cog,
    winding: OrientedWinding,
}

#[inline(always)]
fn cog_has_word(cog: Cog) -> bool {
    cog.mag != 0 || cog.rank.mag != 0 || cog.rank.rank != 0 || cog.rank.neg || cog.turn != 0
}

#[inline(always)]
fn rung_has_word(rung: Rung) -> bool {
    rung.mag != 0 || rung.rank != 0 || rung.neg
}

impl ChannelRead {
    #[inline(always)]
    fn has_word(self) -> bool {
        cog_has_word(self.anchor.0)
            || cog_has_word(self.anchor.1)
            || cog_has_word(self.sweep.0)
            || cog_has_word(self.sweep.1)
            || cog_has_word(self.basis_aim)
            || cog_has_word(self.basis_cross)
            || rung_has_word(self.winding.this_way)
            || rung_has_word(self.winding.that_way)
    }

    #[inline(always)]
    fn with_basis(self, basis: FormedRotor) -> LineageChannel {
        LineageChannel {
            anchor: self.anchor,
            sweep: self.sweep,
            basis,
            winding: self.winding,
        }
    }
}

/// Expand the one channel layout directly at its consumer. No storage pointer or decoded-row
/// aggregate crosses a helper function boundary; the only local aggregate contains formed number
/// values, and each scalar seam word is read exactly once.
macro_rules! read_channel_once {
    ($seam:ty, $words:expr, $at:expr, $read:ident => $body:block) => {{
        let $read = ChannelRead {
            anchor: (
                unsafe { num::read_cog_unchecked::<$seam>($words, $at) },
                unsafe { num::read_cog_unchecked::<$seam>($words, $at + COG_WORDS) },
            ),
            sweep: (
                unsafe { num::read_cog_unchecked::<$seam>($words, $at + 2 * COG_WORDS) },
                unsafe { num::read_cog_unchecked::<$seam>($words, $at + 3 * COG_WORDS) },
            ),
            basis_aim: unsafe { num::read_cog_unchecked::<$seam>($words, $at + 4 * COG_WORDS) },
            basis_cross: unsafe { num::read_cog_unchecked::<$seam>($words, $at + 5 * COG_WORDS) },
            winding: OrientedWinding {
                this_way: unsafe { num::read_rung_unchecked::<$seam>($words, $at + 6 * COG_WORDS) },
                that_way: unsafe {
                    num::read_rung_unchecked::<$seam>($words, $at + 6 * COG_WORDS + RUNG_WORDS)
                },
            },
        };
        $body
    }};
}

impl LineageChannel {
    /// One packed carrier word of K. The cpu seam and the card's atomic store consume this same
    /// scalar mouth; CHANNEL_WORDS is therefore a layout, never a prompt to respell one elsewhere.
    #[inline]
    pub fn packed_word(&self, word: usize) -> u32 {
        if word < COG_WORDS {
            num::cog_packed_word(self.anchor.0, word)
        } else if word < 2 * COG_WORDS {
            num::cog_packed_word(self.anchor.1, word - COG_WORDS)
        } else if word < 3 * COG_WORDS {
            num::cog_packed_word(self.sweep.0, word - 2 * COG_WORDS)
        } else if word < 4 * COG_WORDS {
            num::cog_packed_word(self.sweep.1, word - 3 * COG_WORDS)
        } else if word < 5 * COG_WORDS {
            num::cog_packed_word(self.basis.aim(), word - 4 * COG_WORDS)
        } else if word < 6 * COG_WORDS {
            num::cog_packed_word(self.basis.cross(), word - 5 * COG_WORDS)
        } else if word < 6 * COG_WORDS + RUNG_WORDS {
            num::rung_packed_word(self.winding.this_way, word - 6 * COG_WORDS)
        } else {
            num::rung_packed_word(self.winding.that_way, word - 6 * COG_WORDS - RUNG_WORDS)
        }
    }

    /// Pack `K` for the stroke seam — the carried frame crosses byte-exact. The mouth lives here
    /// with the channel's own fields; no other module spells this layout.
    pub fn pack(&self, out: &mut [u32], at: usize) {
        let mut word = 0usize;
        while word < CHANNEL_WORDS {
            out[at + word] = self.packed_word(word);
            word += 1;
        }
    }

    /// Unpack `K` from a seam row. `None` is the all-zero unborn row (a zeroed reservation carries
    /// no lineage — a born channel always holds a formed basis, so it never packs all-zero); a
    /// nonzero row whose basis rotor cannot form is equally no channel.
    ///
    /// # Safety
    ///
    /// `at..at + CHANNEL_WORDS` must be a live row in `w`.
    #[inline(always)]
    pub unsafe fn unpack_unchecked_with<S: WordSeam>(
        w: &[u32],
        at: usize,
    ) -> Option<LineageChannel> {
        read_channel_once!(S, w, at, read => {
            if !read.has_word() {
                return None;
            }
            let basis = FormedRotor::of(read.basis_aim, read.basis_cross)?;
            Some(read.with_basis(basis))
        })
    }

    #[inline]
    pub fn unpack_with<S: WordSeam>(w: &[u32], at: usize) -> Option<LineageChannel> {
        if row_fits(w, at, CHANNEL_WORDS) {
            unsafe { LineageChannel::unpack_unchecked_with::<S>(w, at) }
        } else {
            None
        }
    }

    #[inline]
    pub fn unpack(w: &[u32], at: usize) -> Option<LineageChannel> {
        LineageChannel::unpack_with::<SliceWordSeam>(w, at)
    }

    /// Scalar proof used by storage substrates before a continuing cursor may enter the genesis
    /// fallback mouth. A born `K` always has a formed basis; an all-zero or unformed row does not.
    /// This intentionally reads only the two basis arms so shader ABIs need not transport an
    /// `Option<LineageChannel>` aggregate.
    ///
    /// # Safety
    ///
    /// `at..at + CHANNEL_WORDS` must be a live row in `w`.
    #[inline(always)]
    pub unsafe fn packed_basis_forms_unchecked_with<S: WordSeam>(w: &[u32], at: usize) -> bool {
        let aim = unsafe { num::read_cog_unchecked::<S>(w, at + 4 * COG_WORDS) };
        let cross = unsafe { num::read_cog_unchecked::<S>(w, at + 5 * COG_WORDS) };
        FormedRotor::arms_form(aim, cross)
    }

    /// Check one boundary row of `K` without inventing another codec. Every nested number must be
    /// canonical, the basis must form, and packing the typed construction must reproduce the exact
    /// row. An all-zero or malformed row is not a carried lineage.
    pub fn packed_row_is_canonical(w: &[u32], at: usize) -> bool {
        if !row_fits(w, at, CHANNEL_WORDS) {
            return false;
        }
        let mut cog = 0usize;
        while cog < 6 {
            if !num::packed_cog_is_canonical(w, at + cog * COG_WORDS) {
                return false;
            }
            cog += 1;
        }
        let winding = at + 6 * COG_WORDS;
        if !num::packed_rung_is_canonical(w, winding)
            || !num::packed_rung_is_canonical(w, winding + RUNG_WORDS)
        {
            return false;
        }
        let Some(channel) = LineageChannel::unpack(w, at) else {
            return false;
        };
        if channel.anchor == place::origin()
            || channel.winding.this_way.neg
            || channel.winding.that_way.neg
        {
            return false;
        }
        let mut word = 0usize;
        while word < CHANNEL_WORDS {
            if channel.packed_word(word) != w[at + word] {
                return false;
            }
            word += 1;
        }
        true
    }

    /// Read a carried channel when one is present, otherwise retain the supplied genesis. Keeping
    /// this choice beside K's own layout lets storage substrates resume a channel without moving an
    /// aggregate `Option<LineageChannel>` across a dynamically indexed carrier boundary.
    ///
    /// # Safety
    ///
    /// `at..at + CHANNEL_WORDS` must be a live row in `w`.
    #[inline(always)]
    pub unsafe fn unpack_or_unchecked_with<S: WordSeam>(
        w: &[u32],
        at: usize,
        genesis: LineageChannel,
    ) -> LineageChannel {
        read_channel_once!(S, w, at, read => {
            if !read.has_word() {
                return genesis;
            }
            if !FormedRotor::arms_form(read.basis_aim, read.basis_cross) {
                return genesis;
            }
            read.with_basis(FormedRotor::from_formed_arms(
                read.basis_aim,
                read.basis_cross,
            ))
        })
    }

    #[inline]
    pub fn unpack_or_with<S: WordSeam>(
        w: &[u32],
        at: usize,
        genesis: LineageChannel,
    ) -> LineageChannel {
        if row_fits(w, at, CHANNEL_WORDS) {
            unsafe { LineageChannel::unpack_or_unchecked_with::<S>(w, at, genesis) }
        } else {
            genesis
        }
    }

    #[inline]
    pub fn unpack_or(w: &[u32], at: usize, genesis: LineageChannel) -> LineageChannel {
        LineageChannel::unpack_or_with::<SliceWordSeam>(w, at, genesis)
    }
}

/// A bounded algebra/gauge witness for the pre-fold channel spelling. The public name is retained
/// for compatibility; `represents` establishes only the declared finite fixture, not prior-state
/// reconstruction or universal causal inversion.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ChannelCause {
    pub anchor: Place,
    pub sweep: Place,
    pub basis: RotorRatio,
    pub winding: OrientedWinding,
}

impl ChannelCause {
    /// Check this bounded pre-fold witness against one supplied channel fixture. This is not a
    /// universal inverse and does not ask the standing channel to encode its history.
    #[inline]
    pub fn represents(self, channel: LineageChannel) -> bool {
        self.anchor == channel.anchor
            && self.sweep == channel.sweep
            && self.winding == channel.winding
            && self
                .basis
                .represents(channel.basis.aim(), channel.basis.cross())
    }
}

#[inline]
fn is_forward(c: Cog) -> bool {
    c.mag != 0 && c.turn & 2 == 0
}

#[inline]
fn is_backward(c: Cog) -> bool {
    c.mag != 0 && c.turn & 2 != 0
}

/// Lift the basis phase to its universal cover. The positive real ray is the lineage's genesis
/// gauge. With each deed turn bounded to one half-turn by the swing, an oriented ray crossing is
/// exactly one integer circuit; endpoint magnitude never votes. Half-open sides count a reverse
/// circuit when it leaves the genesis ray and a forward circuit when it returns, avoiding a double
/// deposit at an endpoint.
fn circuit_crossing(old_aim: Cog, old_cross: Cog, new_aim: Cog, new_cross: Cog) -> WindingQuantum {
    let orientation = old_aim.mul(new_cross).sub(old_cross.mul(new_aim));
    if is_forward(orientation) && is_backward(old_cross) && !is_backward(new_cross) {
        WindingQuantum::ThisWay
    } else if is_backward(orientation) && !is_backward(old_cross) && is_backward(new_cross) {
        WindingQuantum::ThatWay
    } else {
        WindingQuantum::None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use core::sync::atomic::{AtomicU64, AtomicUsize, Ordering};

    static SEAM_READS: AtomicUsize = AtomicUsize::new(0);
    static SEAM_SLOTS: AtomicU64 = AtomicU64::new(0);

    struct CountingWordSeam;

    unsafe impl WordSeam for CountingWordSeam {
        unsafe fn read_u32_unchecked(words: &[u32], at: usize) -> u32 {
            SEAM_READS.fetch_add(1, Ordering::Relaxed);
            SEAM_SLOTS.fetch_or(1u64 << at, Ordering::Relaxed);
            *words.get_unchecked(at)
        }

        unsafe fn store_u32_unchecked(_words: &mut [u32], _at: usize, _value: u32) {
            panic!("the channel fixture never stores through its read face")
        }
    }

    fn reset_seam_read() {
        SEAM_READS.store(0, Ordering::Relaxed);
        SEAM_SLOTS.store(0, Ordering::Relaxed);
    }

    fn rotor(aim: i64, cross: i64) -> FormedRotor {
        FormedRotor::of(Cog::lit(aim), Cog::lit(cross)).expect("formed test rotor")
    }

    fn genesis() -> LineageChannel {
        LineageChannel::from_first_difference(place::extend(place::origin(), false))
            .expect("one dead extension is the first difference")
    }

    #[test]
    fn the_first_difference_is_the_first_frame() {
        assert!(LineageChannel::from_first_difference(place::origin()).is_none());
        let first = place::extend(place::origin(), false);
        let k =
            LineageChannel::from_first_difference(first).expect("the first difference emanates");
        assert_eq!(k.frame().tip(), first);
        assert_eq!(k.frame().basis, FormedRotor::identity());
    }

    #[test]
    fn fold_is_ordered_even_when_the_terminal_rotor_face_commutes() {
        let a = DeedEmanation::ride(rotor(1, 1));
        let b = DeedEmanation::ride(rotor(2, 0));
        let ab = genesis().fold(a).unwrap().fold(b).unwrap();
        let ba = genesis().fold(b).unwrap().fold(a).unwrap();
        assert_eq!(
            ab.frame().basis,
            ba.frame().basis,
            "the local complex face commutes"
        );
        assert_ne!(
            ab.frame().tip(),
            ba.frame().tip(),
            "the lightning channel keeps worldline order"
        );
        assert_ne!(ab.turn_at(Cog::lit(7)).c, ba.turn_at(Cog::lit(7)).c);
    }

    #[test]
    fn a_closed_rotor_loop_returns_a_different_soul() {
        let quarter = DeedEmanation::ride(rotor(0, 1));
        let start = genesis();
        let mut forward = start;
        let mut i = 0;
        while i < 4 {
            forward = forward.fold(quarter).unwrap();
            i += 1;
        }
        assert_eq!(
            forward.frame().basis,
            start.frame().basis,
            "the clipped basis returns"
        );
        assert_eq!(
            (
                forward.frame().tip().0.face(),
                forward.frame().tip().1.face()
            ),
            (start.frame().tip().0.face(), start.frame().tip().1.face()),
            "the clipped tip face returns"
        );
        assert_eq!(
            forward.turn_at(Cog::lit(1)).c.winding.this_way().face(),
            Some(1)
        );
        assert_ne!(forward, start, "the directed loop deposits a winding");

        let reverse_quarter = DeedEmanation::ride(rotor(0, -1));
        let mut returned = forward;
        let mut j = 0;
        while j < 4 {
            returned = returned.fold(reverse_quarter).unwrap();
            j += 1;
        }
        let winding = returned.turn_at(Cog::lit(1)).c.winding;
        assert_eq!(winding.this_way().face(), Some(1));
        assert_eq!(winding.that_way().face(), Some(1));
        assert_ne!(
            returned, start,
            "the opposite loop cannot un-deposit the first passage"
        );
    }

    #[test]
    fn the_fold_bounded_restore_matches_the_flat_fixture() {
        let before = genesis().fold(DeedEmanation::ride(rotor(2, 1))).unwrap();
        let deed = DeedEmanation::found(rotor(3, -2), WindingQuantum::ThatWay)
            .expect("a founding has a hand");
        let after = before.fold(deed).expect("the deed forms the next basis");
        assert!(
            after
                .restore_before(deed)
                .expect("the bounded restore operands remain formed")
                .represents(before),
            "this flat channel fixture remains on the bounded restore section"
        );
    }

    #[test]
    fn small_formed_fold_fixtures_stay_on_the_bounded_restore_section() {
        let seed = genesis();
        for pa in -3i64..=3 {
            for pc in -3i64..=3 {
                let Some(prior_rotor) = FormedRotor::of(Cog::lit(pa), Cog::lit(pc)) else {
                    continue;
                };
                let Some(before) = seed.fold(DeedEmanation::ride(prior_rotor)) else {
                    continue;
                };
                for ea in -3i64..=3 {
                    for ec in -3i64..=3 {
                        let Some(emitted) = FormedRotor::of(Cog::lit(ea), Cog::lit(ec)) else {
                            continue;
                        };
                        let deeds = [
                            Some(DeedEmanation::ride(emitted)),
                            DeedEmanation::found(emitted, WindingQuantum::ThisWay),
                            DeedEmanation::found(emitted, WindingQuantum::ThatWay),
                        ];
                        for deed in deeds.into_iter().flatten() {
                            let Some(after) = before.fold(deed) else {
                                continue;
                            };
                            assert!(
                                after
                                    .restore_before(deed)
                                    .expect("the bounded restore operands remain formed")
                                    .represents(before),
                                "prior ({pa},{pc}) · emanation ({ea},{ec}) · {deed:?}"
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn reach_is_rejudged_and_darkness_folds_once() {
        let k = genesis();
        assert_ne!(k.turn_at(Cog::lit(3)).r, k.turn_at(Cog::lit(19)).r);
        assert_eq!(k.frame(), k.turn_at(Cog::lit(3)).c.into_frame());

        let after = k
            .fold(DeedEmanation::dark())
            .expect("one completed silence folds");
        assert_ne!(after, k);
        assert_eq!(
            after.frame().basis,
            k.frame().basis,
            "static linkage adds no turn"
        );
    }

    #[test]
    fn the_channel_crosses_a_seam_byte_exact() {
        // a folded channel — a ride, a founding, and one dark fold — round-trips exactly.
        let k = genesis()
            .fold(DeedEmanation::ride(rotor(2, 1)))
            .unwrap()
            .fold(
                DeedEmanation::found(rotor(3, -2), WindingQuantum::ThatWay)
                    .expect("a founding has a hand"),
            )
            .unwrap()
            .fold(DeedEmanation::dark())
            .unwrap();
        let mut row = [7u32; CHANNEL_WORDS + 2];
        k.pack(&mut row, 1);
        assert_eq!(
            LineageChannel::unpack(&row, 1),
            Some(k),
            "pack→unpack carries the folded channel byte-exact across the seam"
        );
        reset_seam_read();
        assert_eq!(
            LineageChannel::unpack_with::<CountingWordSeam>(&row, 1),
            Some(k),
            "the same canonical K reader crosses the supplied seam"
        );
        assert_eq!(SEAM_READS.load(Ordering::Relaxed), CHANNEL_WORDS);
        assert_eq!(
            SEAM_SLOTS.load(Ordering::Relaxed),
            ((1u64 << CHANNEL_WORDS) - 1) << 1,
            "each K word is read exactly once; neither canary crosses"
        );
        reset_seam_read();
        assert_eq!(
            LineageChannel::unpack_or_with::<CountingWordSeam>(&row, 1, genesis()),
            k
        );
        assert_eq!(
            SEAM_READS.load(Ordering::Relaxed),
            CHANNEL_WORDS,
            "unpack_or has no preliminary all-zero scan"
        );
        // the genesis channel's identity basis round-trips too (aim = 1, a formed rotor).
        let g = genesis();
        let mut grow = [0u32; CHANNEL_WORDS];
        g.pack(&mut grow, 0);
        assert_eq!(LineageChannel::unpack(&grow, 0), Some(g));
        // the all-zero row is the unborn reservation, never a channel.
        let unborn = [0u32; CHANNEL_WORDS];
        assert!(LineageChannel::unpack(&unborn, 0).is_none());

        let short = [u32::MAX; CHANNEL_WORDS - 1];
        reset_seam_read();
        assert!(LineageChannel::unpack_with::<CountingWordSeam>(&short, 0).is_none());
        assert_eq!(
            LineageChannel::unpack_or_with::<CountingWordSeam>(&short, 0, g),
            g
        );
        assert!(LineageChannel::unpack_with::<CountingWordSeam>(&short, usize::MAX).is_none());
        assert_eq!(
            SEAM_READS.load(Ordering::Relaxed),
            0,
            "a short K row is structural absence before the seam"
        );
    }

    impl ComposedTurn {
        fn into_frame(self) -> LivingFrame {
            LivingFrame {
                anchor: self.anchor,
                sweep: self.sweep,
                basis: self.basis,
            }
        }
    }

    /// CONSTRUCTION 2 — the deposit census. Both hands returned, neither divided; and the control
    /// that makes it a census rather than a magnitude: a circuit followed by its OPPOSITE must
    /// remain two deposited passages, never a return to zero.
    ///
    /// **The falsifier arm below is the WEAKER of the two it should have.** It requires that two
    /// different histories return different censuses, and that holds here. It does NOT establish the
    /// converse, and the converse is false: an exhibited collision — `FoundThat(2+2i)` against
    /// `Ride(−2−i); Ride(−1)` from `basis = 1` — returns the identical census from different sweeps.
    /// That is why the carrier is a census and not an action, and the type now says so.
    #[test]
    fn the_deposit_census_keeps_the_two_hands_apart_and_never_nets_them() {
        let genesis = LineageChannel::from_located_first_difference((Cog::lit(3), Cog::lit(1)));
        let start = genesis.deposit_census();
        assert_eq!(start.deposits.this_way(), Rung::ZERO);
        assert_eq!(start.deposits.that_way(), Rung::ZERO);
        assert_eq!(start.basis, FormedRotor::identity());

        // one founding THIS way
        let this = genesis.fold_formed_hand_or_self(Cog::lit(1), Cog::lit(2), true, false);
        let after_this = this.deposit_census();
        // then its OPPOSITE, THAT way
        let both = this.fold_formed_hand_or_self(Cog::lit(1), Cog::lit(2), false, true);
        let after_both = both.deposit_census();

        // THE CONTROL. Depositing a passage and then its opposite must leave TWO passages standing.
        // A netted counter would return to zero here and the ledger would be a magnitude in disguise.
        assert_ne!(
            after_both.deposits.this_way(),
            Rung::ZERO,
            "the first passage survives its opposite"
        );
        assert_ne!(
            after_both.deposits.that_way(),
            Rung::ZERO,
            "the opposing passage is deposited, not subtracted"
        );
        assert_ne!(
            after_both.deposits, start.deposits,
            "a circuit and its opposite are not a return to zero"
        );

        // THE FALSIFIER'S ARM: two different histories must not return the same ledger, or the
        // reading cannot separate lineages and is not a ledger.
        assert_ne!(after_this.deposits, after_both.deposits);
        assert_ne!(start, after_this);

        // the remainder is the undivided rotor pair, and folding moved it off the identity
        assert_ne!(after_this.basis, FormedRotor::identity());
    }
}
