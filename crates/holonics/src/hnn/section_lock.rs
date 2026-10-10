//! **The lock reader and the joint period: a consumer of the dynamic section's stream** (second
//! rung of the acoustic line, item 4 and item 5 of its native list; the
//! [record](../../../../research/records/2026-10-09_A_MATCHED_WAVE_ENTERS_A_LOADED_RING_AND_ITS_STATE_CROSSES_ITS_OWN_SECTION.md),
//! §12; #148, #73, #386).
//!
//! [definition; agent-inferred, October 9] [`crate::hnn::dynamic_section::SectionReader`] emits, per
//! tick of one ring, the symbol `(class, advance, crossing)`. A ring **locks** to a periodic wave
//! when, after a declared settle tick, the symbols of a declared read window repeat exactly. The
//! reader sees only those symbols, never a sample or a state:
//!
//! ```text
//! window   ticks settle … settle + L − 1, the symbols s_k (exact equality, no tolerance)
//! τ        the least τ ≤ L/2 with s_k = s_(k+τ) for every k < L − τ     (else Unlocked)
//! W        (Σ_(k<τ) Δℓ_k) / 4, whole turns of the lift over one cycle    (else Fractional)
//! address  W/τ in lowest terms, the ring's turns per tick, signed
//! arrivals the signed crossings of the ring section within one cycle: the OBSERVED word
//! ```
//!
//! A period of at most half the window is a period the window shows at least twice. A window in
//! which no symbol advances the lift crossed no ray at all and is **Silent** (a ring at rest, the
//! origin, has no class and is never started: it is Silent by being at rest). A ring that crosses
//! rays but never the section, and repeats (`W = 0`), is not Silent: it is a lock without rotation
//! and keeps its cycle, with an empty arrival word. `W = 0` alone does not empty the word: a cycle
//! `(3, +1, +1), (0, −1, −1)` arrives and departs, and its signed arrivals cancel.
//!
//! [definition] **The observed word is the lock's content; the rate is a face.** The cycle's symbols
//! and the signed arrival word (which ticks of the cycle arrive at the section, and with which sign)
//! are kept as observed. A mean rate `W/τ` is a cycle face: [`Lock::mean_rate_face`] is
//! `aeon::TwoClocks::new(W/τ)` (with its `lock_address` and `convergents`) beside the word, present
//! only for `W > 0`, and never in its place. The arrival word of a ring need not be the
//! constant-rate word of its face (the ring `t = 2` of the record's §4.4: `W/τ = 2/7`, arrivals
//! `0101000`, gaps 2 and 5 where a balanced word has 3 and 4; Lean `Aeon/Clock/CarryWord.carry_balanced`),
//! and the face's lock period need not be the cycle's (`W/τ = 3/12 = 1/4` has the face period 4 on a
//! cycle of 12).
//!
//! [definition] **The joint period** ([`JointLock`]): over several rings read on one clock, the lcm of
//! the rings' cycles, with silent rings skipped. Each ring's `τ` divides it, and it is the least
//! period of the tuple of the rings' symbols and divides the wave's period (the wave is a source
//! the rings share). Any ring that is not locked refuses the joint, typed; if every ring is silent
//! the joint is silent. A joint period over half the window is refused: the window does not show it
//! twice.
//!
//! [definition] **A section word is admitted only with its chart relations** ([`SectionWord::new`]).
//! Each symbol has `class ∈ {0, 1, 2, 3}`, `Δℓ ∈ {−2, …, 2}` (a chord's advance,
//! [`crate::hnn::dynamic_section::chord`]) and `crossing = ⌊(class + Δℓ)/4⌋`, and consecutive symbols
//! keep the class recursion `class_(k+1) = class_k + Δℓ_k (mod 4)`. A word that breaks one is refused
//! [`LockRefusal::NotASectionWord`] at its first broken tick, before Silent or a period is read. The
//! reader's own stream satisfies all four by [`SectionReader::advance`]. A repeated class and a whole
//! net lift do not certify the crossings: `(0, 2, 0), (2, 2, 0)` repeated closes the class recursion
//! with `W = 1` and declares no arrival, while its second tick lands on `4` and crosses `+1`.
//!
//! [proved-derived] **The lift's net over a cycle is whole, and the signed arrivals sum to it.** By the
//! class recursion, `Σ_(k<τ) Δℓ_k = 4 Σ_(k<τ) crossing_k + class_τ − class_0`, and an admitted word of
//! period `τ ≤ L/2` has `class_τ = class_0`. So `W = Σ_(k<τ) crossing_k`: the winding is the signed
//! count of the observed arrivals (the half-turn-blind reading of the record's X3, which closes a
//! half-wave antisymmetric tone on half a turn, is refused at admission). Likewise the least period of
//! the tuple word is the lcm of the rings' least periods when
//! the lcm is at most half the window (Fine–Wilf: a window of length `τ_b + p` with periods `τ_b`
//! and `p` has period `gcd`); the joint reading checks it ([`JointRefusal::Disagrees`]).
//!
//! [definition] **The winding is read by the owners, at the consumer.** The cycle's `W` is
//! `geometry::winding::closed_loop_winding(4, (Δℓ_k)_(k<τ))` (Lean
//! `Geometry/PhaseCarry.closed_loop_has_integer_winding`: increments closing mod `n` sum to `n·w`): the
//! owner refuses a cycle whose lifted sum does not close, carrying the exact remainder
//! ([`LockRefusal::Winding`]), where the old reading divided and asserted. For an admitted word the
//! refusal is unreachable (the class recursion closes the cycle), and the owner's integer `W` is the
//! `i64` of [`Lock::winding`] without loss: `|Σ Δℓ| ≤ 2τ` and `τ ≤ L/2`, so `|W| ≤ L/4`, below
//! `i64::MAX` on any platform whose `usize` is at most 64 bits ([`LockRefusal::WindingBeyondCarrier`]
//! returns the exact winding rather than narrow it, were that ever false). The tick's own carry
//! (`crossing`, the landing class of the recursion) is `dynamic_section::land`'s, the owner's signed
//! carry law, called once at admission and once by the reader.
//!
//! [proved-derived] **Section words concatenate with the carry cocycle** ([`SectionWord::concat`]). The
//! winding of an open word `u` from class `c_u` with net lift `N_u` is the whole turns its lift gains,
//! `W(u) = windings(c_u/4 + N_u/4) = ⌊(c_u + N_u)/4⌋` ([`SectionWord::winding`], the signed carry law
//! applied once to the word's start class and its net lift), and the word lands on the class
//! `e(u) = (c_u + N_u) mod 4`. For words with `e(u) = c_v`,
//!
//! ```text
//! W(uv) = ⌊(c_u + N_u + N_v)/4⌋ = ⌊(c_u + N_u)/4⌋ + ⌊(e(u) + N_v)/4⌋ = W(u) + W(v)
//! ```
//!
//! (Lean `Aeon/Clock/Winding.windings_add`, `carry_cocycle`; along aeons `aeon_windings_concat`): the
//! carry at the junction vanishes because the junction phase is the class both words agree on. With
//! `e(u) ≠ c_v` the join is not a section word: it breaks the class recursion at `u`'s last tick and
//! is refused `NotASectionWord { relation: Recursion }`, not given a winding. The Lean statement of
//! this instance (the junction carry of two section words) is owed (#62).
//!
//! [definition] **What it is not.** It enumerates candidate periods `τ ≤ L/2` against the settled
//! symbol word: a least-period test on an exact word, the first-return test the record names, not a
//! period finder on samples and not learning (guard 17, failure 1): the symbols are the ring's own
//! section words, the rings are a declared bank, and nothing is located. A read window is the declared
//! finite read set of the lock (like a location's read set), not retention of the stream: the reader
//! holds at most `L` symbols and discards them with the reading.
//!
//! The computational object is the helical pair interaction. Of the winding guide's six general
//! objects this owner touches the **helix** (the cycle's net lift is whole turns; the winding is
//! the carry), **pair** (the address `W/τ` is the rate relation of a lock; two rings entrained by
//! one wave have rates `W_a/τ` and `W_b/τ`, and the contact that would read their ratio is not built),
//! **faces and placement** (the arrival word) and **cell holonomy** (the symbol cycle is the phase
//! carried across epochs). The tube and the tower thread stay attached.
//!
//! | Law | Lean | Rust |
//! |---|---|---|
//! | a closed class cycle has a whole winding, the signed count of its arrivals; the carry is kept | `Geometry/PhaseCarry.closed_loop_has_integer_winding` | owner `geometry::winding::closed_loop_winding`, called at [`Settled::lock`] (read by [`Lock::winding`]); the chart relations at [`SectionWord::new`] |
//! | the tick's crossing and landing class are the signed carry law of the lift | `Aeon/Clock/Winding.windings_add`, `carry_le_one`; `Geometry/PhaseCarry.winding_add` | owner `aeon::Reading::add` (over `geometry::winding::carry`) through [`crate::hnn::dynamic_section::land`], called at [`SectionWord::new`] and by the reader |
//! | words concatenate with the carry cocycle: `W(uv) = W(u) + W(v)` exactly when `u`'s landing class is `v`'s start class | `Aeon/Clock/Winding.windings_add`, `carry_cocycle`, `aeon_windings_concat`; the section-word instance owed (#62) | [`SectionWord::concat`], [`SectionWord::winding`] |
//! | the mean rate is a face, not the section word; a constant-rate word is balanced | `Aeon/Clock/CarryWord.carry_balanced`; `Aeon/Clock/Lock.lock_at_address` | [`Lock::mean_rate_face`], [`Lock::arrival_word`] |
//! | the joint period is the lcm of the rings' | owed (#62) | [`JointLock`] |

use num_bigint::BigInt;
use num_traits::Zero;
use thiserror::Error;

use crate::aeon::{Reading, TwoClocks};
use crate::geometry::winding::{WindingError, closed_loop_winding};
use crate::hnn::dynamic_section::{
    RAYS, SectionReader, SectionRefusal, SectionSymbol, land, quadrant,
};
use crate::ratio::Rat;

/// [definition] **Why a window has no lock.** Typed; a period is never invented.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum LockRefusal {
    /// No symbol of the window advances the lift: nothing crossed a ray (a ring at rest).
    #[error("the window holds no ray crossing: nothing to lock")]
    Silent,
    /// No period of at most half the window repeats the settled symbol word.
    #[error(
        "no period of at most {max_period} ticks (half the {length}-tick window) repeats the settled symbol word"
    )]
    Unlocked { max_period: usize, length: usize },
    /// The word breaks a chart relation of the section's symbols at `tick` (module header).
    #[error("the word is not a section word: tick {tick} breaks {relation:?}")]
    NotASectionWord {
        tick: usize,
        relation: SectionRelation,
    },
    /// The dynamic section refused a tick of the window (the origin, a chord through it).
    #[error(transparent)]
    Section(#[from] SectionRefusal),
    /// The winding owner refused the cycle: its lifted advances do not close on the circle of four
    /// rays, and the exact remainder is kept. Unreachable for an admitted word of period at most
    /// half the window (the class recursion closes the cycle); returned rather than assumed.
    #[error(transparent)]
    Winding(#[from] WindingError),
    /// Unreachable: the owner's integer winding does not fit the lock's `i64` (module header bound
    /// `|W| ≤ L/4`). Returned with the exact winding rather than narrowed.
    #[error("the cycle's winding {winding} does not fit the lock's carrier")]
    WindingBeyondCarrier { winding: BigInt },
    /// The ring was at rest at the settle tick and left rest inside the window.
    #[error(
        "the ring was at rest at tick {settle} and left rest inside the window: it had not settled"
    )]
    NotSettled { settle: usize },
    /// The states offered do not fill the declared window.
    #[error("the window needs {need} states and holds {have}")]
    Incomplete { have: usize, need: usize },
    /// The declared window cannot show any period twice.
    #[error("a window of {length} ticks cannot show a period twice")]
    Window { length: usize },
}

/// [definition] **The chart relation a section word breaks** (module header).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum SectionRelation {
    /// `class ∉ {0, 1, 2, 3}`.
    Class,
    /// `Δℓ ∉ {−2, …, 2}`: no chord passes more than two rays.
    Advance,
    /// `crossing ≠ ⌊(class + Δℓ)/4⌋`.
    Crossing,
    /// `class_(k+1) ≠ class_k + Δℓ_k (mod 4)`: the next tick does not start where this one lands.
    Recursion,
}

/// [definition] **A section word**: one ring's symbols, one per tick, admitted only when every chart
/// relation holds (module header). Its symbols are private: a word is built by
/// [`SectionWord::new`], by [`SectionWord::concat`] of two words whose classes meet, or by the
/// [`LockReader`] from the ring's own states (admitted by [`SectionWord::new`] as well).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SectionWord {
    symbols: Vec<SectionSymbol>,
}

impl SectionWord {
    /// **Admit a word** of symbols, refused at the first tick that breaks a chart relation.
    ///
    /// The crossing and the landing class a tick owes are `dynamic_section::land`'s, the owner's signed
    /// carry law (module header); the class recursion compares the next tick's class with the landing.
    pub fn new(symbols: Vec<SectionSymbol>) -> Result<Self, LockRefusal> {
        for (tick, symbol) in symbols.iter().enumerate() {
            let broken = |relation| LockRefusal::NotASectionWord { tick, relation };
            if symbol.class >= RAYS {
                return Err(broken(SectionRelation::Class));
            }
            if !(-2..=2).contains(&symbol.advance) {
                return Err(broken(SectionRelation::Advance));
            }
            let (crossing, landed) = land(symbol.class, symbol.advance)?;
            if symbol.crossing != crossing {
                return Err(broken(SectionRelation::Crossing));
            }
            if let Some(next) = symbols.get(tick + 1)
                && next.class != landed
            {
                return Err(broken(SectionRelation::Recursion));
            }
        }
        Ok(Self { symbols })
    }

    /// The symbols, one per tick.
    pub fn symbols(&self) -> &[SectionSymbol] {
        &self.symbols
    }

    /// The class the word starts from: its first symbol's class (`None` for the empty word).
    pub fn start_class(&self) -> Option<u8> {
        self.symbols.first().map(|symbol| symbol.class)
    }

    /// **The word's winding** `W(u)`: the whole turns its lift gains, `⌊(c + N)/4⌋` for the start class
    /// `c` and the net lift `N = Σ Δℓ_k` (module header). It is the owner's signed carry law applied once
    /// to the word as a whole: the aeon's reading of `c/4`, carried by `Reading::add` with the reading of
    /// `N/4`, less the reading of `c/4` (whose winding is zero). It does not sum the symbols'
    /// `crossing` fields; that the two agree is the telescoped per-tick law, asserted at the consumers.
    /// The empty word has winding `0`.
    pub fn winding(&self) -> BigInt {
        let Some(start) = self.start_class() else {
            return BigInt::zero();
        };
        let net: BigInt = self
            .symbols
            .iter()
            .map(|symbol| BigInt::from(symbol.advance))
            .sum();
        let turns = |rays: BigInt| Reading::of_turns(&Rat::new(rays, BigInt::from(RAYS)));
        let behind = turns(BigInt::from(start));
        behind.add(&turns(net)).windings() - behind.windings()
    }

    /// **Concatenation** `uv`, the carry cocycle at its consumer (module header): the word of `self`'s
    /// symbols followed by `other`'s, with `W(uv) = W(u) + W(v)`. It is admitted exactly when `self`'s
    /// last tick lands on the class `other` starts from; otherwise it is refused
    /// `NotASectionWord { tick, relation: Recursion }` at `self`'s last tick, the tick whose landing the
    /// next does not start from. An empty word is the identity.
    pub fn concat(&self, other: &Self) -> Result<Self, LockRefusal> {
        if let (Some(last), Some(first)) = (self.symbols.last(), other.symbols.first()) {
            let (_, landed) = land(last.class, last.advance)?;
            if first.class != landed {
                return Err(LockRefusal::NotASectionWord {
                    tick: self.symbols.len() - 1,
                    relation: SectionRelation::Recursion,
                });
            }
        }
        let mut symbols = self.symbols.clone();
        symbols.extend_from_slice(&other.symbols);
        Ok(Self { symbols })
    }
}

/// [definition] **The declared read window**: the settle tick and the number of ticks read after it.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct LockWindow {
    settle: usize,
    length: usize,
}

impl LockWindow {
    /// The window of `length` ticks read from tick `settle`; refused when it is shorter than two
    /// ticks (no period can repeat).
    pub fn new(settle: usize, length: usize) -> Result<Self, LockRefusal> {
        if length < 2 {
            return Err(LockRefusal::Window { length });
        }
        Ok(Self { settle, length })
    }

    /// The tick the ring is declared settled at: the first state read.
    pub fn settle(&self) -> usize {
        self.settle
    }

    /// The ticks read.
    pub fn length(&self) -> usize {
        self.length
    }

    /// The largest period the window shows twice: half its length.
    pub fn max_period(&self) -> usize {
        self.length / 2
    }
}

/// [definition] **One ring's settled window**: its symbols, or the rest it stayed at.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Settled {
    /// The ring was at rest, the origin, through the whole window.
    Rest,
    /// The symbols of the window, one per tick, admitted as a section word.
    Word(SectionWord),
}

/// [definition] **An arrival at the section** within a cycle: the tick and the sign of the crossing.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Arrival {
    pub tick: usize,
    pub sign: i8,
}

/// [definition] **A lock**: the cycle as observed, its whole winding and address, and the mean-rate
/// face beside them (module header).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lock {
    start: usize,
    cycle: Vec<SectionSymbol>,
    winding: i64,
    address: Rat,
    rate_face: Option<TwoClocks>,
}

impl Lock {
    /// The tick the cycle starts at (the settle tick).
    pub fn start(&self) -> usize {
        self.start
    }

    /// `τ`, the cycle's length in ticks.
    pub fn period(&self) -> usize {
        self.cycle.len()
    }

    /// The observed symbols of one cycle, from the settle tick.
    pub fn cycle(&self) -> &[SectionSymbol] {
        &self.cycle
    }

    /// `W`, the whole signed turns of the lift over one cycle: `geometry::winding::closed_loop_winding`
    /// of the cycle's advances on the circle of four rays (module header).
    pub fn winding(&self) -> i64 {
        self.winding
    }

    /// `W/τ` in lowest terms: the ring's turns per tick, signed.
    pub fn address(&self) -> &Rat {
        &self.address
    }

    /// **The observed arrival word**: the signed crossing of the ring section at each tick of the
    /// cycle, as observed.
    pub fn arrival_word(&self) -> Vec<i8> {
        self.cycle.iter().map(|symbol| symbol.crossing).collect()
    }

    /// The arrivals of one cycle: the tick and sign of each nonzero crossing.
    pub fn arrivals(&self) -> Vec<Arrival> {
        self.cycle
            .iter()
            .enumerate()
            .filter(|(_, symbol)| symbol.crossing != 0)
            .map(|(offset, symbol)| Arrival {
                tick: self.start + offset,
                sign: symbol.crossing,
            })
            .collect()
    }

    /// **The mean-rate face**: `aeon::TwoClocks::new(W/τ)`, present only for `W > 0` (two clocks need
    /// a positive rate). It sits beside the observed word and never in its place.
    pub fn mean_rate_face(&self) -> Option<&TwoClocks> {
        self.rate_face.as_ref()
    }
}

impl Settled {
    /// **Read the lock** of a window (module header). Silent when nothing crossed a ray, Unlocked
    /// when no period of at most half the window repeats the word. The word was admitted with its
    /// chart relations, so the cycle's net lift is whole turns, and the owner of closed loops reads
    /// them (`cycle_winding`).
    pub fn lock(&self, window: &LockWindow) -> Result<Lock, LockRefusal> {
        let symbols = match self {
            Self::Rest => return Err(LockRefusal::Silent),
            Self::Word(word) => word.symbols(),
        };
        if symbols.len() != window.length {
            return Err(LockRefusal::Incomplete {
                have: symbols.len(),
                need: window.length,
            });
        }
        if symbols.iter().all(|symbol| symbol.advance == 0) {
            return Err(LockRefusal::Silent);
        }
        let period = least_period(symbols, window.max_period()).ok_or(LockRefusal::Unlocked {
            max_period: window.max_period(),
            length: window.length,
        })?;
        let cycle = symbols[..period].to_vec();
        let winding = cycle_winding(&cycle)?;
        let address = Rat::new(
            BigInt::from(winding),
            BigInt::from(u64::try_from(period).unwrap_or(u64::MAX)),
        );
        let rate_face = if winding > 0 {
            TwoClocks::new(address.clone()).ok()
        } else {
            None
        };
        Ok(Lock {
            start: window.settle,
            cycle,
            winding,
            address,
            rate_face,
        })
    }
}

/// **The cycle's winding, by the owner of closed loops** (module header): the lifted advances of one
/// cycle are the increments of a loop on the circle of four rays, and
/// `geometry::winding::closed_loop_winding` returns their integer winding or refuses the loop with the
/// exact remainder (`LockRefusal::Winding`). The `i64` is the owner's integer, not narrowed past its
/// carrier (`LockRefusal::WindingBeyondCarrier`).
fn cycle_winding(cycle: &[SectionSymbol]) -> Result<i64, LockRefusal> {
    let increments: Vec<BigInt> = cycle
        .iter()
        .map(|symbol| BigInt::from(symbol.advance))
        .collect();
    let winding = closed_loop_winding(&BigInt::from(RAYS), &increments)?;
    match i64::try_from(&winding) {
        Ok(whole) => Ok(whole),
        Err(_) => Err(LockRefusal::WindingBeyondCarrier { winding }),
    }
}

/// The least `τ ≤ max` with `word[k] = word[k + τ]` for every `k < len − τ`: exact equality.
fn least_period<T: PartialEq>(word: &[T], max: usize) -> Option<usize> {
    (1..=max).find(|&tau| (0..word.len() - tau).all(|k| word[k] == word[k + tau]))
}

fn gcd(a: usize, b: usize) -> usize {
    if b == 0 { a } else { gcd(b, a % b) }
}

/// [definition] **The reader of one ring's window from its stream of states**: it is offered the
/// ring's phase point `(w, u)` after each tick (tick 0 the state before any sample), ignores the
/// ticks before the settle tick, starts a [`SectionReader`] on the state at the settle tick, and
/// holds the window's symbols. A ring at rest at the settle tick (the origin, which has no class)
/// is read as [`Settled::Rest`] and stays so or is refused when it leaves rest.
#[derive(Debug)]
pub struct LockReader {
    window: LockWindow,
    seen: usize,
    stage: Stage,
    symbols: Vec<SectionSymbol>,
}

#[derive(Debug)]
enum Stage {
    Waiting,
    Rest,
    Reading(SectionReader),
}

impl LockReader {
    /// A reader of the declared window, before its first state.
    pub fn new(window: LockWindow) -> Self {
        Self {
            window,
            seen: 0,
            stage: Stage::Waiting,
            symbols: Vec::with_capacity(window.length),
        }
    }

    /// The states offered so far.
    pub fn seen(&self) -> usize {
        self.seen
    }

    /// **Offer the state after the next tick.** Atomic: a refused state is not counted. States
    /// after the window are ignored.
    pub fn observe(&mut self, point: [Rat; 2]) -> Result<(), LockRefusal> {
        let tick = self.seen;
        let first = self.window.settle;
        if tick >= first && tick <= first + self.window.length {
            match &mut self.stage {
                Stage::Waiting => {
                    self.stage = if quadrant(&point).is_none() {
                        Stage::Rest
                    } else {
                        Stage::Reading(SectionReader::at(point)?)
                    };
                }
                Stage::Rest => {
                    if quadrant(&point).is_some() {
                        return Err(LockRefusal::NotSettled { settle: first });
                    }
                }
                Stage::Reading(reader) => {
                    self.symbols.push(reader.advance(point)?);
                }
            }
        }
        self.seen += 1;
        Ok(())
    }

    /// **The window read**: its symbols, or the rest the ring stayed at. Refused until the declared
    /// window is full.
    pub fn finish(self) -> Result<Settled, LockRefusal> {
        let need = self.window.settle + self.window.length + 1;
        if self.seen < need {
            return Err(LockRefusal::Incomplete {
                have: self.seen,
                need,
            });
        }
        Ok(match self.stage {
            // the reader's own symbols keep every chart relation (`SectionReader::advance`, both
            // through `land`); the word is admitted rather than trusted
            Stage::Reading(_) => Settled::Word(SectionWord::new(self.symbols)?),
            Stage::Rest | Stage::Waiting => Settled::Rest,
        })
    }
}

/// [definition] **Why rings have no joint period.** Typed.
#[derive(Clone, Debug, PartialEq, Eq, Error)]
pub enum JointRefusal {
    /// Every ring is silent.
    #[error("every ring of the joint is silent")]
    Silent,
    /// A ring has no lock: the joint is refused, naming the first such ring.
    #[error("ring {ring} has no lock: {refusal}")]
    Ring { ring: usize, refusal: LockRefusal },
    /// The lcm of the rings' cycles is more than half the window: the window does not show it twice.
    #[error("the joint period {period} is more than half the window ({max_period})")]
    Beyond { period: usize, max_period: usize },
    /// The least period of the tuple word is not the lcm (unreachable under Fine–Wilf; a witness).
    #[error("the joint word has least period {word:?}, not the lcm {lcm}")]
    Disagrees { lcm: usize, word: Option<usize> },
}

/// [definition] **A joint period**: the lcm of the locked rings' cycles, with each ring's lock
/// (`None` for a silent ring), and the least period of the tuple of their symbols.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct JointLock {
    period: usize,
    rings: Vec<Option<Lock>>,
}

impl JointLock {
    /// **Read the joint period** of rings read on one clock and one window (module header).
    pub fn read(window: &LockWindow, rings: &[Settled]) -> Result<Self, JointRefusal> {
        let mut locks = Vec::with_capacity(rings.len());
        for (ring, settled) in rings.iter().enumerate() {
            match settled.lock(window) {
                Ok(lock) => locks.push(Some(lock)),
                Err(LockRefusal::Silent) => locks.push(None),
                Err(refusal) => return Err(JointRefusal::Ring { ring, refusal }),
            }
        }
        let periods: Vec<usize> = locks.iter().flatten().map(Lock::period).collect();
        if periods.is_empty() {
            return Err(JointRefusal::Silent);
        }
        let mut lcm = 1;
        for &period in &periods {
            lcm = match (lcm / gcd(lcm, period)).checked_mul(period) {
                Some(next) if next <= window.max_period() => next,
                Some(next) => {
                    return Err(JointRefusal::Beyond {
                        period: next,
                        max_period: window.max_period(),
                    });
                }
                None => {
                    return Err(JointRefusal::Beyond {
                        period: usize::MAX,
                        max_period: window.max_period(),
                    });
                }
            };
        }
        // the tuple of the locked rings' symbols, tick by tick
        let words: Vec<&[SectionSymbol]> = rings
            .iter()
            .filter_map(|settled| match settled {
                Settled::Word(word) if word.symbols().iter().any(|s| s.advance != 0) => {
                    Some(word.symbols())
                }
                _ => None,
            })
            .collect();
        let tuple: Vec<Vec<SectionSymbol>> = (0..window.length)
            .map(|k| words.iter().map(|word| word[k]).collect())
            .collect();
        let word = least_period(&tuple, window.max_period());
        if word != Some(lcm) {
            return Err(JointRefusal::Disagrees { lcm, word });
        }
        Ok(Self {
            period: lcm,
            rings: locks,
        })
    }

    /// The joint period: the lcm of the rings' cycles.
    pub fn period(&self) -> usize {
        self.period
    }

    /// Each ring's lock, `None` for a silent ring.
    pub fn rings(&self) -> &[Option<Lock>] {
        &self.rings
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A symbol `(class, advance)` with the crossing the class recursion gives.
    fn symbol(class: u8, advance: i8) -> SectionSymbol {
        let landed = class as i8 + advance;
        SectionSymbol {
            class,
            advance,
            crossing: if landed >= 4 {
                1
            } else if landed < 0 {
                -1
            } else {
                0
            },
        }
    }

    /// The cycle repeated over a window of `length`.
    fn word(cycle: &[(u8, i8)], length: usize) -> Settled {
        Settled::Word(
            SectionWord::new(
                (0..length)
                    .map(|k| {
                        let (class, advance) = cycle[k % cycle.len()];
                        symbol(class, advance)
                    })
                    .collect(),
            )
            .unwrap(),
        )
    }

    /// Symbols `(class, advance, crossing)` as declared, repeated over a window of `length`.
    fn declared(cycle: &[(u8, i8, i8)], length: usize) -> Vec<SectionSymbol> {
        (0..length)
            .map(|k| {
                let (class, advance, crossing) = cycle[k % cycle.len()];
                SectionSymbol {
                    class,
                    advance,
                    crossing,
                }
            })
            .collect()
    }

    /// The signed arrivals of a lock's cycle sum to its winding (module header).
    fn arrivals_sum_to_winding(lock: &Lock) {
        let sum: i64 = lock.arrival_word().iter().map(|&c| i64::from(c)).sum();
        assert_eq!(sum, lock.winding());
    }

    fn window() -> LockWindow {
        LockWindow::new(10, 24).unwrap()
    }

    /// The `(class, advance)` cycle of the given advances, the classes by the class recursion from
    /// class 0 (the net lift must be a multiple of 4 for the cycle to close).
    fn consistent(advances: &[i8]) -> Vec<(u8, i8)> {
        let mut class = 0i8;
        advances
            .iter()
            .map(|&advance| {
                let symbol = (class as u8, advance);
                class = (class + advance).rem_euclid(4);
                symbol
            })
            .collect()
    }

    #[test]
    fn a_repeating_word_locks_at_its_least_period_with_its_whole_winding() {
        // the record's ring t = 1: 1:+1 2:+1 3:+1 0:+1 1:+1 2:-2 0:+1, net lift 4
        let cycle = [(1, 1), (2, 1), (3, 1), (0, 1), (1, 1), (2, -2), (0, 1)];
        let lock = word(&cycle, 24).lock(&window()).unwrap();
        assert_eq!(lock.period(), 7);
        assert_eq!(lock.winding(), 1);
        assert_eq!(*lock.address(), Rat::new(1.into(), 7.into()));
        assert_eq!(lock.arrival_word(), [0, 0, 1, 0, 0, 0, 0]);
        assert_eq!(lock.arrivals(), [Arrival { tick: 12, sign: 1 }]);
        // the mean-rate face sits beside the word: the lock address of 1/7 has period 7
        let face = lock.mean_rate_face().unwrap();
        assert_eq!(
            face.lock_address().unwrap().period().unwrap(),
            BigInt::from(7)
        );
    }

    #[test]
    fn the_arrival_word_is_kept_where_the_mean_rate_would_lose_it() {
        // the record's ring t = 2: W = 2, τ = 7, arrivals 0101000 (a balanced word of 2/7 is not)
        let cycle = [(2, 1), (3, 1), (0, 2), (2, 2), (0, 1), (1, -1), (0, 2)];
        let lock = word(&cycle, 24).lock(&window()).unwrap();
        assert_eq!((lock.period(), lock.winding()), (7, 2));
        assert_eq!(lock.arrival_word(), [0, 1, 0, 1, 0, 0, 0]);
        assert_eq!(
            lock.arrivals(),
            [Arrival { tick: 11, sign: 1 }, Arrival { tick: 13, sign: 1 }]
        );
        assert_eq!(
            *lock.mean_rate_face().unwrap().ratio(),
            Rat::new(2.into(), 7.into())
        );
    }

    #[test]
    fn a_rocking_lock_that_never_reaches_the_section_has_an_empty_arrival_word() {
        // rocking between classes 1 and 2 across the ray 2, never the section: W = 0, no face
        let cycle = [(1, 1), (2, 0), (2, -1), (1, 0)];
        let lock = word(&cycle, 24).lock(&window()).unwrap();
        assert_eq!((lock.period(), lock.winding()), (4, 0));
        assert_eq!(lock.arrival_word(), [0, 0, 0, 0]);
        assert!(lock.arrivals().is_empty());
        assert_eq!(*lock.address(), Rat::new(0.into(), 1.into()));
        assert!(lock.mean_rate_face().is_none());
    }

    #[test]
    fn a_lock_without_rotation_can_arrive_and_depart() {
        // (3, +1, +1), (0, −1, −1): back to class 3, net lift 0, the arrivals +1 then −1 cancel
        let cycle = [(3, 1), (0, -1)];
        let lock = word(&cycle, 24).lock(&window()).unwrap();
        assert_eq!((lock.period(), lock.winding()), (2, 0));
        assert_eq!(lock.arrival_word(), [1, -1]);
        assert_eq!(
            lock.arrivals(),
            [
                Arrival { tick: 10, sign: 1 },
                Arrival { tick: 11, sign: -1 }
            ]
        );
        assert!(lock.mean_rate_face().is_none());
        arrivals_sum_to_winding(&lock);
    }

    #[test]
    fn the_signed_arrivals_of_a_cycle_sum_to_its_winding() {
        let cycles: [&[(u8, i8)]; 4] = [
            &[(1, 1), (2, 1), (3, 1), (0, 1), (1, 1), (2, -2), (0, 1)],
            &[(2, 1), (3, 1), (0, 2), (2, 2), (0, 1), (1, -1), (0, 2)],
            &[(2, 1), (3, 1), (0, 2), (2, 2), (0, 1), (1, -2), (3, -1)],
            &[(0, -1), (3, -2), (1, -1), (0, -1), (3, 1), (0, 1), (1, -1)],
        ];
        for cycle in cycles {
            arrivals_sum_to_winding(&word(cycle, 24).lock(&window()).unwrap());
        }
    }

    #[test]
    fn a_departure_back_across_the_section_is_a_negative_arrival() {
        // t = 3 of the record: 3 crossings per cycle, signed sum 1
        let cycle = [(2, 1), (3, 1), (0, 2), (2, 2), (0, 1), (1, -2), (3, -1)];
        let lock = word(&cycle, 24).lock(&window()).unwrap();
        assert_eq!((lock.period(), lock.winding()), (7, 1));
        assert_eq!(lock.arrival_word(), [0, 1, 0, 1, 0, -1, 0]);
    }

    #[test]
    fn nothing_crossed_is_silent_and_a_word_that_never_repeats_is_unlocked() {
        let still = word(&[(2, 0)], 24);
        assert_eq!(still.lock(&window()), Err(LockRefusal::Silent));
        assert_eq!(Settled::Rest.lock(&window()), Err(LockRefusal::Silent));
        // a cycle of 13 ticks is more than half the 24-tick window: not shown twice
        let thirteen = consistent(&[1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0]);
        assert_eq!(
            word(&thirteen, 24).lock(&window()),
            Err(LockRefusal::Unlocked {
                max_period: 12,
                length: 24
            })
        );
        // and one of exactly half the window is, at its least period
        let twelve = consistent(&[1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0]);
        let lock = word(&twelve, 24).lock(&window()).unwrap();
        assert_eq!((lock.period(), lock.winding()), (12, 1));
    }

    #[test]
    fn a_word_that_breaks_a_chart_relation_is_not_admitted() {
        let refused = |tick, relation| Err(LockRefusal::NotASectionWord { tick, relation });
        // the review's witness: (0, 2, 0), (2, 2, 0) repeated closes the class recursion with W = 1
        // and declares no arrival; its second tick lands on 4 and crosses +1
        assert_eq!(
            SectionWord::new(declared(&[(0, 2, 0), (2, 2, 0)], 4)),
            refused(1, SectionRelation::Crossing)
        );
        // with the crossing it owes, the same word is admitted and locks at τ = 2, W = 1
        let honest =
            Settled::Word(SectionWord::new(declared(&[(0, 2, 0), (2, 2, 1)], 24)).unwrap());
        let lock = honest.lock(&window()).unwrap();
        assert_eq!((lock.period(), lock.winding()), (2, 1));
        assert_eq!(lock.arrival_word(), [0, 1]);
        // a half-turn per tick from class 0 back to class 0 breaks the recursion (net lift 2)
        assert_eq!(
            SectionWord::new(declared(&[(0, 2, 0)], 24)),
            refused(0, SectionRelation::Recursion)
        );
        assert_eq!(
            SectionWord::new(declared(&[(4, 0, 1)], 2)),
            refused(0, SectionRelation::Class)
        );
        assert_eq!(
            SectionWord::new(declared(&[(0, 3, 0), (3, 1, 1)], 2)),
            refused(0, SectionRelation::Advance)
        );
        // the reader's own stream is admitted: one ray per tick around the circle
        let points = [[1, 0], [0, 1], [-1, 0], [0, -1], [1, 0]].map(|[w, u]| {
            [
                Rat::new(BigInt::from(w), 1.into()),
                Rat::new(BigInt::from(u), 1.into()),
            ]
        });
        let mut reader = SectionReader::at(points[0].clone()).unwrap();
        let stream: Vec<SectionSymbol> = points[1..]
            .iter()
            .map(|point| reader.advance(point.clone()).unwrap())
            .collect();
        assert!(SectionWord::new(stream).is_ok());
    }

    /// A section word of `(class, advance)` symbols, the crossings the owner's carry gives.
    fn admitted(cycle: &[(u8, i8)]) -> SectionWord {
        SectionWord::new(
            cycle
                .iter()
                .map(|&(class, advance)| symbol(class, advance))
                .collect(),
        )
        .unwrap()
    }

    #[test]
    fn a_cycles_winding_is_the_owners_and_an_open_cycle_is_refused_with_its_remainder() {
        let cycle = |advances: &[i8]| -> Vec<SectionSymbol> {
            consistent(advances)
                .iter()
                .map(|&(class, advance)| symbol(class, advance))
                .collect()
        };
        let open = |remainder: i64| {
            Err(LockRefusal::Winding(WindingError::LoopDoesNotClose {
                modulus: BigInt::from(4),
                remainder: BigInt::from(remainder),
            }))
        };
        // one turn forward, one back, two, and the arrive-and-depart cycle of winding zero
        assert_eq!(cycle_winding(&cycle(&[1, 1, 1, 1])), Ok(1));
        assert_eq!(cycle_winding(&cycle(&[-1, -1, -1, -1])), Ok(-1));
        assert_eq!(cycle_winding(&cycle(&[2, 2, 2, 2])), Ok(2));
        assert_eq!(cycle_winding(&cycle(&[1, -1])), Ok(0));
        // an advance sum that does not close on four rays is the owner's refusal, with the exact
        // remainder (truncated, the sign of the sum), never rounded to a turn
        assert_eq!(cycle_winding(&cycle(&[1])), open(1));
        assert_eq!(cycle_winding(&cycle(&[2, 1])), open(3));
        assert_eq!(cycle_winding(&cycle(&[-1])), open(-1));
    }

    #[test]
    fn words_concatenate_with_the_carry_cocycle_when_their_classes_meet() {
        // u lands on class 3 with winding 0; v starts at 3 and arrives at the section once
        let u = admitted(&[(1, 1), (2, 1)]);
        let v = admitted(&[(3, 1), (0, 1)]);
        assert_eq!(
            (u.winding(), v.winding()),
            (BigInt::from(0), BigInt::from(1))
        );
        let uv = u.concat(&v).unwrap();
        assert_eq!(uv, admitted(&[(1, 1), (2, 1), (3, 1), (0, 1)]));
        assert_eq!(uv.winding(), BigInt::from(1));
        assert_eq!(uv.winding(), u.winding() + v.winding());
        // a departure back across the section is a winding of -1, and meeting its return gives 0
        let back = admitted(&[(0, -1)]);
        let there = admitted(&[(3, 1)]);
        assert_eq!(back.winding(), BigInt::from(-1));
        assert_eq!(there.winding(), BigInt::from(1));
        assert_eq!(back.concat(&there).unwrap().winding(), BigInt::from(0));
        // a word starting on another class does not meet: refused at u's last tick, with no winding
        assert_eq!(
            u.concat(&admitted(&[(0, 1)])),
            Err(LockRefusal::NotASectionWord {
                tick: 1,
                relation: SectionRelation::Recursion
            })
        );
        // the empty word is the identity, with winding zero
        let empty = SectionWord::new(Vec::new()).unwrap();
        assert_eq!(empty.start_class(), None);
        assert_eq!(empty.winding(), BigInt::from(0));
        assert_eq!(u.concat(&empty).unwrap(), u);
        assert_eq!(empty.concat(&u).unwrap(), u);
        // the word's winding is the signed count of its arrivals
        for word in [&u, &v, &uv, &back, &there] {
            let count: i64 = word.symbols().iter().map(|s| i64::from(s.crossing)).sum();
            assert_eq!(word.winding(), BigInt::from(count));
        }
    }

    #[test]
    fn a_window_must_be_full_and_able_to_show_a_period_twice() {
        assert_eq!(
            LockWindow::new(0, 1),
            Err(LockRefusal::Window { length: 1 })
        );
        let short = word(&consistent(&[1, 1, 1, 1]), 5);
        assert_eq!(
            short.lock(&window()),
            Err(LockRefusal::Incomplete { have: 5, need: 24 })
        );
    }

    #[test]
    fn the_joint_period_is_the_lcm_and_every_ring_divides_it() {
        // periods 4 and 6 (net lift 4 each): joint 12, within half of a 24-tick window
        let four = [(0, 1), (1, 1), (2, 1), (3, 1)];
        let six = [(0, 1), (1, 0), (1, 1), (2, 1), (3, 1), (0, 0)];
        let rings = [word(&four, 24), word(&six, 24)];
        let joint = JointLock::read(&window(), &rings).unwrap();
        assert_eq!(joint.period(), 12);
        for lock in joint.rings().iter().flatten() {
            assert_eq!(joint.period() % lock.period(), 0);
        }
        // a silent ring is skipped; all silent is silent; an unlocked ring refuses the joint
        let rings = [word(&four, 24), Settled::Rest];
        assert_eq!(JointLock::read(&window(), &rings).unwrap().period(), 4);
        assert_eq!(
            JointLock::read(&window(), &[Settled::Rest, Settled::Rest]),
            Err(JointRefusal::Silent)
        );
        // twelve quarter-turns and then rest at class 0: no period of at most 12 repeats it
        let advances: Vec<i8> = (0..24).map(|k| if k < 12 { 1 } else { 0 }).collect();
        let aperiodic = consistent(&advances);
        let rings = [word(&four, 24), word(&aperiodic, 24)];
        assert!(matches!(
            JointLock::read(&window(), &rings),
            Err(JointRefusal::Ring { ring: 1, .. })
        ));
        // a joint period more than half the window is refused: 4 and 6 and 5 give 60
        let five = [(0, 1), (1, 1), (2, 1), (3, 1), (0, 0)];
        let rings = [word(&four, 24), word(&six, 24), word(&five, 24)];
        assert!(matches!(
            JointLock::read(&window(), &rings),
            Err(JointRefusal::Beyond { period: 60, .. })
        ));
    }
}
