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
//! and keeps its cycle, with an empty arrival word.
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
//! [proved-derived] **The lift's net over a cycle is whole by the class recursion.** The reader's own
//! symbols satisfy `class_(k+1) = class_k + Δℓ_k (mod 4)`, so a word that repeats in the class has a
//! net lift `≡ 0 (mod 4)`; [`LockRefusal::Fractional`] is the typed form of that law for hand-fed
//! symbols that break the recursion (the half-turn-blind reading of the record's X3, which closes a
//! half-wave antisymmetric tone on half a turn, would read here). It is unreachable from a reader's
//! stream. Likewise the least period of the tuple word is the lcm of the rings' least periods when
//! the lcm is at most half the window (Fine–Wilf: a window of length `τ_b + p` with periods `τ_b`
//! and `p` has period `gcd`); the joint reading checks it ([`JointRefusal::Disagrees`]).
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
//! | a closed class cycle has a whole winding; the carry is kept | `Geometry/PhaseCarry.closed_loop_has_integer_winding` | [`Lock::winding`], [`LockRefusal::Fractional`] |
//! | the mean rate is a face, not the section word; a constant-rate word is balanced | `Aeon/Clock/CarryWord.carry_balanced`; `Aeon/Clock/Lock.lock_at_address` | [`Lock::mean_rate_face`], [`Lock::arrival_word`] |
//! | the joint period is the lcm of the rings' | owed (#62) | [`JointLock`] |

use num_bigint::BigInt;
use thiserror::Error;

use crate::aeon::TwoClocks;
use crate::hnn::dynamic_section::{SectionReader, SectionRefusal, SectionSymbol, quadrant};
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
    /// The repeating cycle's net lift is not a multiple of four: not whole turns.
    #[error("the cycle of {period} ticks turns the lift by {net}, not a whole number of turns")]
    Fractional { period: usize, net: i64 },
    /// The dynamic section refused a tick of the window (the origin, a chord through it).
    #[error(transparent)]
    Section(#[from] SectionRefusal),
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
    /// The symbols of the window, one per tick.
    Word(Vec<SectionSymbol>),
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

    /// `W`, the whole signed turns of the lift over one cycle.
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
    /// when no period of at most half the window repeats the word, Fractional when the repeating
    /// cycle's net lift is not whole turns.
    pub fn lock(&self, window: &LockWindow) -> Result<Lock, LockRefusal> {
        let symbols = match self {
            Self::Rest => return Err(LockRefusal::Silent),
            Self::Word(symbols) => symbols,
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
        let net: i64 = cycle.iter().map(|symbol| i64::from(symbol.advance)).sum();
        if net % 4 != 0 {
            return Err(LockRefusal::Fractional { period, net });
        }
        let winding = net / 4;
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
            Stage::Reading(_) => Settled::Word(self.symbols),
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
        let words: Vec<&Vec<SectionSymbol>> = rings
            .iter()
            .filter_map(|settled| match settled {
                Settled::Word(symbols) if symbols.iter().any(|s| s.advance != 0) => Some(symbols),
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
            (0..length)
                .map(|k| {
                    let (class, advance) = cycle[k % cycle.len()];
                    symbol(class, advance)
                })
                .collect(),
        )
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
    fn a_lock_without_rotation_is_a_lock_with_an_empty_arrival_word() {
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
    fn a_cycle_that_is_not_whole_turns_is_fractional() {
        // hand-fed symbols that break the class recursion: net lift 2 per cycle
        let broken = Settled::Word(vec![
            SectionSymbol {
                class: 0,
                advance: 2,
                crossing: 0,
            };
            24
        ]);
        assert_eq!(
            broken.lock(&window()),
            Err(LockRefusal::Fractional { period: 1, net: 2 })
        );
    }

    #[test]
    fn a_window_must_be_full_and_able_to_show_a_period_twice() {
        assert_eq!(
            LockWindow::new(0, 1),
            Err(LockRefusal::Window { length: 1 })
        );
        let short = Settled::Word(vec![symbol(0, 1); 5]);
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
        let aperiodic: Vec<(u8, i8)> = (0..24)
            .map(|k| ((k % 4) as u8, 1 - (k / 12) as i8))
            .collect();
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
