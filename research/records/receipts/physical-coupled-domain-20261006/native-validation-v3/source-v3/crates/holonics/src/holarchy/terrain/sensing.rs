//! **The chase's observation channels: the lag, the faulty sensor, and the loop closure that locates
//! a channel's defect** (THE_REBUILD F6, the switches and the deposition law; the record
//! `2026-09-27_THE_LEARNER_MUST_MOVE_A_CHASE_TERRAIN_…`, §9, §12 items 7 and 10, §13 and §14.5;
//! campaign 4, #27). The terrain's side of the switches; the attribution that consumes them is the
//! machine's reception (`receiver::population::chaser`, "The attribution").
//!
//! [definition; agent-inferred] **The channels** ([`CHANNELS`]). In the action phase the chaser
//! reads the runner through three independent, time-aligned observation channels, each a sensor on
//! the chaser that reports directions in its own frame. Each reads the runner's cell at tick `τ` as
//! a [`Reading`]: the cell's kind (a move, a slip or a wall meeting, the ground contact's reading),
//! the **line of sight** `x_R(τ) − x_C(τ)` from the chaser to the runner as the tick opens, and the
//! runner's **heading**, its velocity after the tick; both are Gaussian integers. The cell follows
//! from the reading and the observed motion before it ([`Reading::cell`]: a move's change is
//! `v′ − v`, a slip keeps `v`, a wall applies the wall law), and the map from a cell to its reading is
//! injective, so with the switches off the channels deliver exactly the cells. A [`Reception`] is one
//! tick's three readings, stamped with that tick: the channels are time-aligned.
//!
//! [definition; agent-inferred] **The switches** ([`Switches`]), declared families whose truth the
//! terrain returns (the `Switching` pattern):
//! - **the lag**: every channel delivers the reading of tick `τ` once tick `τ + d` has moved, `d`
//!   declared (at most [`LAG_LIMIT`]); the receiver's ports declare it (`ChasePorts::lag`), as they
//!   declare the arena and the alphabet;
//! - **the faulty sensor** ([`FaultTruth`]): one channel, drawn uniformly on the three, reports a
//!   **rotated heading**: its frame turned by `i^a`, `a` drawn uniformly on the three quarter-turns
//!   other than the identity (the unit group `⟨i⟩ ≅ ℤ/4` of `ℤ[i]`, an exact rotation of the lattice,
//!   `geometry::motion::quarter_turn`), so it reports its line of sight and its heading both turned,
//!   on the **odd aeons** of a switch clock whose aeon lengths are drawn from a declared `AeonFamily`
//!   over the passage's tick cap (`SwitchTruth::drawn`: the aeons are the epochs of the tick clock's
//!   forward aeon at the fault's section, exactly as `Switching` reads its two sources). The fault's
//!   draw continues the chase's own (`Chase::draw_key`), so a seed names the same runner, arena and
//!   openings with the switches on or off.
//!
//! [agent-inferred] **Why the frame, not the velocity alone.** A turn of a zero velocity is zero, so a
//! sensor reporting only the runner's velocity makes no error while the runner stands (a cornered
//! runner stands for ticks at a time), and no loop closure can locate a fault that made no error. The
//! line of sight is never zero before capture (`Q > ρ² ≥ 0`), so a turned frame errs at every tick of
//! its active aeons, and the fault is observable on exactly those.
//!
//! [proved-derived; the record's §14.5] **The channel menu and its separation condition**
//! ([`ChannelMenu`]). Each channel is an edge from the observed frame to the runner's hidden
//! directions `x`, carrying its defect `e_k ∈ ℤ/4`: it reports `y_k = i^(e_k) x`. The pair contacts
//! between the channels are the menu's circuits: circuit `(j, k)` reads the ratio of two readings
//! carried as the undivided pair, `y_j = i^(s_jk) y_k` (one turn relating both directions), and its
//! syndrome is `s_jk = e_j − e_k`. With the circuit matrix `C` (a row per circuit, `+1` at `j` and
//! `−1` at `k`), `s = C e`. **A defect on at most `k` channels is located uniquely exactly when no
//! nonzero `v ∈ (ℤ/4)^n` of support at most `2k` has `C v = 0`** (two defects of support `≤ k` with one
//! syndrome differ by such a `v`, and such a `v` splits into two of them):
//! [`ChannelMenu::separation_witness`] checks it by enumeration and returns the kernel vector that
//! breaks it. The complete menu on `n` channels has `ker C = {(c, …, c)}`, the common mode (a turn of
//! the hidden directions themselves, `im d₀` of the multigraph of `n` parallel edges), of support `n`:
//! - **three channels, `k = 1`**: every nonzero `v` of support at most `2` (`3·3 + 3·9 = 36` of them)
//!   has `C v ≠ 0`, so one faulty channel is located, with its turn;
//! - two channels, `k = 1`: `(1, 1)` has support `2` and `C (1, 1) = 0`, so a fault is detected but not
//!   located; three channels, `k = 2`: `(1, 1, 1)` breaks it, so two faults are not located;
//! - [proved-derived] **the lag is a common mode**: the three channels are time-aligned, so a delay is
//!   the vector `(d, d, d)` in the time chart, in `ker C`: the channel menu cannot see it. Only the
//!   mover's loop, its prediction against its own motor record at the reading's tick, closes it
//!   (the record's §9; the machine's reception).
//!
//! [measured] On the switches' pinned population (the notebook's `hnn_chase switches`, 63 chased
//! seeds of `20261301 + s`, `d = 1`, aeons uniform on `1..=4`), the machine's closure located the
//! turned frame on 111 of the 111 active aeons read and on no inactive one: 264 of 264 active ticks
//! with the truth's channel and turn, no false alarm over 583 readings.
//!
//! [definition] The computational object is the helical pair interaction: the channels are pair
//! contacts between the observed frame and the runner's directions, each contact's slip a
//! quarter-turn, and their loop closure is the Bombe's pairwise closure over the menu of contacts: a
//! turn that closes every circuit but those through one channel names that channel. Of the winding
//! guide's six general objects this owner touches three: the **pair** (each channel's contact and its
//! slip `i^(e_k)`), the **cell holonomy** (the syndrome is the holonomy of each circuit of the menu,
//! expected to be the identity) and **faces and placement** (the readings are the channels' faces of
//! the runner's cell in their own frames). The **helix** (the switch clock's aeons, the tick clock's
//! winding), the **tube** (the lag is a span of the passage the channels withhold) and the **tower
//! thread** stay attached.

use super::chase::{Arena, Letter, Motion, Moves};
use super::switching::{AeonFamily, SwitchTruth};
use super::{Draw, TerrainError, refuse};
use crate::geometry::motion::{Point, quarter_turn, sub};

/// [definition] **The observation channels**: three, independent and time-aligned.
pub const CHANNELS: usize = 3;

/// [definition; agent-inferred] **A channel's declared reach of delay**: at most `2^3` ticks, so a
/// candidate's withheld cells stay a fixed-width word (`holarchy::terrain::pursuit::Pending`).
pub const LAG_LIMIT: usize = 1 << 3;

/// [definition] **The order of the lattice's rotation group** `⟨i⟩ ≅ ℤ/4`: a defect is a number of
/// quarter-turns modulo four.
pub const TURNS: u8 = 4;

/// [definition; agent-inferred] **A menu's declared reach**: at most `2^3` channels, so the
/// separation check's enumeration of `(ℤ/4)^n` stays at most `2^16` vectors.
pub const MENU_LIMIT: usize = 1 << 3;

/// [definition] **The switches** (module header): the channels' declared lag `d` and the faulty
/// sensor's declared aeon family, none when the sensor is sound.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Switches {
    pub lag: usize,
    pub fault: Option<AeonFamily>,
}

impl Switches {
    /// The switches off: no lag, every channel sound.
    pub const OFF: Switches = Switches {
        lag: 0,
        fault: None,
    };

    /// Refused at a lag past [`LAG_LIMIT`] or a fault family without `1 ≤ shortest ≤ longest`.
    pub fn check(&self) -> Result<(), TerrainError> {
        if self.lag > LAG_LIMIT {
            return Err(refuse(
                "a channel's lag",
                "it is at most the declared reach of 2^3 ticks",
            ));
        }
        if self
            .fault
            .as_ref()
            .is_some_and(|aeons| aeons.shortest == 0 || aeons.shortest > aeons.longest)
        {
            return Err(refuse(
                "a faulty sensor's aeon family",
                "its lengths need 1 ≤ shortest ≤ longest",
            ));
        }
        Ok(())
    }
}

/// **A point turned by `i^turns`**: `turns` quarter-turns, read modulo four.
pub fn turn(p: Point, turns: u8) -> Point {
    (0..turns % TURNS).fold(p, |q, _| quarter_turn(q))
}

/// [definition] **The faulty sensor's truth** (module header): the faulty channel, its turn `a`
/// (quarter-turns, `1 ≤ a ≤ 3`) and its switch clock, the fault active on the clock's odd aeons.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FaultTruth {
    pub channel: usize,
    pub turns: u8,
    pub clock: SwitchTruth,
}

impl FaultTruth {
    /// **The fault drawn** (module header) over a passage of at most `ticks ≥ 1` ticks: the channel
    /// uniform on the three, the turn uniform on the three nonidentity quarter-turns, the aeon
    /// lengths from the declared family until they cover the passage.
    pub fn draw(family: &AeonFamily, ticks: usize, draw: &mut Draw) -> Result<Self, TerrainError> {
        let channel = draw.below(CHANNELS);
        let turns = 1 + draw.below(usize::from(TURNS) - 1) as u8;
        let clock = SwitchTruth::drawn(ticks, family, draw)?;
        Ok(Self {
            channel,
            turns,
            clock,
        })
    }

    /// **The fault's aeon at a tick**: the epoch of the micro-state the tick leaves; none past the
    /// clock.
    pub fn aeon(&self, tick: usize) -> Option<usize> {
        self.clock.epochs.epoch_of(tick)
    }

    /// **Whether the fault is active at a tick**: its aeon is odd.
    pub fn active(&self, tick: usize) -> bool {
        self.clock.source(tick) == Some(1)
    }

    /// **The turn channel `k`'s frame carries at a tick**: `a` on the faulty channel while the fault
    /// is active, the identity otherwise.
    pub fn turns_of(&self, channel: usize, tick: usize) -> u8 {
        if channel == self.channel && self.active(tick) {
            self.turns
        } else {
            0
        }
    }
}

/// [definition] **A cell's kind** as a channel reads it: a realized move, a slip or a wall meeting.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum CellKind {
    Move,
    Slip,
    Wall,
}

/// [definition] **A channel's reading of a cell** (module header): its kind, the line of sight from
/// the chaser to the runner as the tick opens, and the runner's heading after it, the directions in
/// the channel's frame.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Reading {
    pub kind: CellKind,
    pub sight: Point,
    pub heading: Point,
}

impl Reading {
    /// **The reading of a cell** read from the runner's motion `before` and `after` it and the
    /// chaser's position as the tick opens; refused at a cell outside the alphabet.
    pub fn of(
        moves: &Moves,
        cell: usize,
        before: &Motion,
        chaser: Point,
        after: &Motion,
    ) -> Result<Self, TerrainError> {
        let kind = match moves.read(cell) {
            Some(Letter::Move(_)) => CellKind::Move,
            Some(Letter::Slip) => CellKind::Slip,
            Some(Letter::Wall) => CellKind::Wall,
            None => {
                return Err(refuse(
                    "a chase cell",
                    "it lies in the declared move alphabet",
                ));
            }
        };
        Ok(Self {
            kind,
            sight: sub(before.position, chaser),
            heading: after.velocity,
        })
    }

    /// **The reading in a frame turned** by `i^turns`: its line of sight and its heading rotated, its
    /// kind kept.
    pub fn turned(self, turns: u8) -> Self {
        Self {
            kind: self.kind,
            sight: turn(self.sight, turns),
            heading: turn(self.heading, turns),
        }
    }

    /// **The cell a reading names** after the runner's observed motion `before`, the chaser at
    /// `chaser` as the tick opens (module header): a move's letter is its change `v′ − v`, a slip's
    /// and a wall's their letters; refused unless the cell's own reading ([`Arena::observe`]) is this
    /// reading, so the map is inverted exactly.
    pub fn cell(
        &self,
        arena: &Arena,
        moves: &Moves,
        before: &Motion,
        chaser: Point,
    ) -> Result<usize, TerrainError> {
        let cell = match self.kind {
            CellKind::Move => moves
                .letter(sub(self.heading, before.velocity))
                .ok_or_else(|| {
                    refuse(
                        "a channel's reading",
                        "its heading names a move of the alphabet",
                    )
                })?,
            CellKind::Slip => moves.slip(),
            CellKind::Wall => moves.wall(),
        };
        let after = arena.observe(moves, before, cell)?;
        if Self::of(moves, cell, before, chaser, &after)? != *self {
            return Err(refuse(
                "a channel's reading",
                "it is the reading of the cell it names",
            ));
        }
        Ok(cell)
    }
}

/// [definition] **One tick's readings** (module header): the tick of the runner's cell they read,
/// and each channel's reading.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Reception {
    pub tick: usize,
    pub readings: [Reading; CHANNELS],
}

impl Reception {
    /// **The channels' readings of tick `tick`'s cell**, the runner's motion `before` and `after`
    /// it and the chaser's position as it opens: each the cell's reading, in a frame turned on the
    /// faulty channel while the fault is active.
    pub fn read(
        moves: &Moves,
        cell: usize,
        before: &Motion,
        chaser: Point,
        after: &Motion,
        tick: usize,
        fault: Option<&FaultTruth>,
    ) -> Result<Self, TerrainError> {
        let reading = Reading::of(moves, cell, before, chaser, after)?;
        let mut readings = [reading; CHANNELS];
        if let Some(fault) = fault {
            for (channel, reading) in readings.iter_mut().enumerate() {
                *reading = reading.turned(fault.turns_of(channel, tick));
            }
        }
        Ok(Self { tick, readings })
    }
}

/// [definition] **A located channel defect**: the channel and the turn its frame carries.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct ChannelDefect {
    pub channel: usize,
    pub turns: u8,
}

/// [definition] **A tick's loop closure over the channel menu**: the reading the menu attributes to
/// the runner (a channel outside the located defect's), and the located defect, none where every
/// circuit closes.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Closure {
    pub reading: Reading,
    pub defect: Option<ChannelDefect>,
}

/// [definition] **A syndrome's location** within a declared number of defects: the one defect
/// vector of that support with that syndrome, or the count of such vectors where it is not one.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Located {
    Unique(Vec<u8>),
    Unattributed(usize),
}

/// [definition] **The channel menu** (module header): `n` channels and the circuits between them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ChannelMenu {
    channels: usize,
    circuits: Vec<[usize; 2]>,
}

impl ChannelMenu {
    /// **The complete menu on `n` channels**, `2 ≤ n ≤` [`MENU_LIMIT`]: every pair `(j, k)`, `j < k`,
    /// a circuit, in lexicographic order.
    pub fn complete(channels: usize) -> Result<Self, TerrainError> {
        if !(2..=MENU_LIMIT).contains(&channels) {
            return Err(refuse(
                "a channel menu",
                "it holds at least two and at most 2^3 channels",
            ));
        }
        let circuits = (0..channels)
            .flat_map(|j| ((j + 1)..channels).map(move |k| [j, k]))
            .collect();
        Ok(Self { channels, circuits })
    }

    pub fn channels(&self) -> usize {
        self.channels
    }

    /// The circuits, each the pair of channels its contact joins.
    pub fn circuits(&self) -> &[[usize; 2]] {
        &self.circuits
    }

    /// **The circuit matrix** `C`: a row per circuit `(j, k)`, `+1` at `j`, `−1` at `k`.
    pub fn matrix(&self) -> Vec<Vec<i64>> {
        self.circuits
            .iter()
            .map(|&[j, k]| {
                let mut row = vec![0i64; self.channels];
                row[j] = 1;
                row[k] = -1;
                row
            })
            .collect()
    }

    /// **The syndrome** `s = C e` over `ℤ/4` of a defect vector (one turn a channel).
    pub fn syndrome(&self, defects: &[u8]) -> Vec<u8> {
        self.circuits
            .iter()
            .map(|&[j, k]| (TURNS + defects[j] % TURNS - defects[k] % TURNS) % TURNS)
            .collect()
    }

    /// Every vector of `(ℤ/4)^n` with its support, in lexicographic order.
    fn vectors(&self) -> impl Iterator<Item = (Vec<u8>, usize)> + '_ {
        let count = usize::from(TURNS).pow(self.channels as u32);
        (0..count).map(move |mut code| {
            let mut v = vec![0u8; self.channels];
            for entry in v.iter_mut().rev() {
                *entry = (code % usize::from(TURNS)) as u8;
                code /= usize::from(TURNS);
            }
            let support = v.iter().filter(|&&e| e != 0).count();
            (v, support)
        })
    }

    /// **The separation check** (module header) for defects on at most `k` channels: none when no
    /// nonzero vector of support at most `2k` lies in `ker C`; otherwise the first such vector, the
    /// witness that two defect vectors of support at most `k` share a syndrome.
    pub fn separation_witness(&self, k: usize) -> Option<Vec<u8>> {
        self.vectors()
            .filter(|(_, support)| (1..=2 * k).contains(support))
            .find(|(v, _)| self.syndrome(v).iter().all(|&s| s == 0))
            .map(|(v, _)| v)
    }

    /// **Whether the menu locates every defect on at most `k` channels**.
    pub fn separates(&self, k: usize) -> bool {
        self.separation_witness(k).is_none()
    }

    /// **The location of a syndrome** within defects on at most `k` channels: the defect vectors of
    /// support at most `k` whose syndrome it is, unique where the menu separates at `k`.
    pub fn locate(&self, syndrome: &[u8], k: usize) -> Located {
        let mut matches = self
            .vectors()
            .filter(|(v, support)| *support <= k && self.syndrome(v) == syndrome)
            .map(|(v, _)| v);
        match (matches.next(), matches.count()) {
            (Some(v), 0) => Located::Unique(v),
            (first, rest) => Located::Unattributed(usize::from(first.is_some()) + rest),
        }
    }

    /// **The turn relating two readings** `y_j = i^s y_k` (module header): the one turn carrying
    /// both of `y_k`'s directions to `y_j`'s, unique since the line of sight is never zero; none
    /// where no turn relates them.
    fn relating(a: &Reading, b: &Reading) -> Option<u8> {
        (0..TURNS).find(|&s| a.sight == turn(b.sight, s) && a.heading == turn(b.heading, s))
    }

    /// **The loop closure of one tick's readings** over the menu, locating a defect on at most one
    /// channel (module header): the syndrome of the readings' pair contacts, its location, and the
    /// reading of a channel the location clears. Refused where the readings' kinds disagree (a turned
    /// frame changes no kind), where a line of sight is zero (the chase is captured), where no turn
    /// relates two readings, or where the syndrome is not the syndrome of exactly one defect on at
    /// most one channel (the declared defect family is exceeded).
    pub fn close(&self, readings: &[Reading]) -> Result<Closure, TerrainError> {
        if readings.len() != self.channels {
            return Err(refuse(
                "a channel menu's readings",
                "there is one reading a channel",
            ));
        }
        if readings.windows(2).any(|pair| pair[0].kind != pair[1].kind)
            || readings.iter().any(|reading| reading.sight == [0, 0])
        {
            return Err(refuse(
                "a channel menu's readings",
                "the channels agree on the cell's kind, and each sights the runner",
            ));
        }
        let syndrome = self
            .circuits
            .iter()
            .map(|&[j, k]| Self::relating(&readings[j], &readings[k]))
            .collect::<Option<Vec<u8>>>()
            .ok_or_else(|| {
                refuse(
                    "a channel menu's readings",
                    "a quarter-turn relates every two readings",
                )
            })?;
        let Located::Unique(defects) = self.locate(&syndrome, 1) else {
            return Err(refuse(
                "a channel menu's syndrome",
                "it is the syndrome of one defect on at most one channel",
            ));
        };
        let defect = defects
            .iter()
            .position(|&e| e != 0)
            .map(|channel| ChannelDefect {
                channel,
                turns: defects[channel],
            });
        let clear = defects
            .iter()
            .position(|&e| e == 0)
            .expect("a menu of two or more channels with one defect clears a channel");
        Ok(Closure {
            reading: readings[clear],
            defect,
        })
    }
}
