//! **The moiré terrain: layers are rings, a cell is the layers' joint class** (the record's §5).
//!
//! [definition; agent-inferred] **The Holarchy.** `k` gratings, each a closing rotor ring of the
//! HNN's own kind (`navigator::Navigator::rotor`: the map `(· + 1)` on `ℤ/q`, keyed at the port
//! `c`), turning `p` of its `q` ports a tick, so its rate is `p/q` of a turn and its phase `c/q`.
//! The gratings exchange no power (no contact joins them), so what the Holarchy declares that the
//! terrain reads is its navigators and their joint clock torus, its parametric orientation
//! ([`Moire::parametric`], built as `holarchy::Holarchy::parametric` builds it). Each tick `t`
//! ring `i` stands at the port `(c_i + t p_i) mod q_i` (the rotor's port after `t p_i` ticks, Lean
//! `Holon/Navigator.map_pow_mod_order`), and its **sheet** is its half-turn side
//!
//! ```text
//! s_i(t) = ⌊2·frac(t p_i/q_i + c_i/q_i)⌋ = [2 ((c_i + t p_i) mod q_i) ≥ q_i]
//! ```
//!
//! the phase class at grain 2 (equivalently the parity of the doubled clock's windings,
//! `⌊2x⌋ − 2⌊x⌋`). The emitted cell is the joint class, declared ([`MoireClass`]) as the **parity
//! color** `Σ_i s_i mod 2` (the polarity that properly two-colors the layers' arrangement) or the
//! **sheet tuple** `Σ_i s_i 2^i`. A silent grating ([`Moire::emit_active`]) is a transparent layer:
//! its sheet reads `0` while its ring keeps turning.
//!
//! [proved-standard; implemented-exact] **The truth** ([`MoireTruth`]):
//! - **the keys**: each grating's rate `p_i/q_i` and phase `c_i/q_i`;
//! - **the joint period** `T = lcm(q_i)`: ring `i` returns to its port exactly at the multiples of
//!   `q_i` (`p_i` a unit of `ℤ/q_i`; Lean `Aeon/Clock/CarryWord.eventually_periodic_rational_iff`,
//!   `Aeon/Clock/Lock.cycle_iff_period_dvd`), so the forward aeon of `T` ticks on the joint torus
//!   is a cycle and no proper divisor's is (the tests close it with `aeon::Cycle::close`);
//! - **the emission's least period**, a divisor of `T` (the least period of a periodic word divides
//!   each of its periods), and its **determining depth**: the least `D` such that the `D` cells
//!   before every tick determine its cell, read on one cyclic period (the moiré's own context
//!   tree's depth, so a receiving tree shallower than it cannot code a period to zero);
//! - **each pair's lock** ([`PairLock`]): the rate ratio `r_i/r_j`, its Farey lock address and
//!   period (`aeon::TwoClocks::lock_address`, Lean `Aeon/Clock/Lock.lock_at_address`), and the
//!   contact law's reading over one joint period's whole windings (`hnn::contact::lock_address`,
//!   Lean `HNN/Contact.contact_lock_address`: the least-denominator rate of the fibre
//!   `(m_i/(m_j + 1), (m_i + 1)/m_j)`), which the HNN's contact letter would read;
//! - **the entropy rate zero**: the emission is periodic, so every bit a learner spends past its
//!   first period's worth is the cost of locating the keys and of its own learning;
//! - **the key description** `⌈log₂ |key space|⌉` of the declared draw family ([`MoireFamily`]):
//!   each grating drawn uniformly among `N_Q = Σ_(q=2)^Q q·φ(q)` triples `(p, q, c)`, `0 < p < q`,
//!   `gcd(p, q) = 1`, `0 ≤ c < q`, so `|key space| = N_Q^k`. Keys whose emissions agree (the
//!   emission's kernel) only lower the cost of naming the terrain.

use std::collections::HashMap;

use num_bigint::{BigInt, BigUint};
use num_traits::{One, Zero};

use super::{Draw, TerrainError, refuse};
use crate::aeon::{ClockLift, TwoClocks};
use crate::compression::cost::ceil_log2;
use crate::hnn::contact::{ContactLock, LockDeclaration, lock_address};
use crate::navigator::Navigator;
use crate::navigator::address::LockAddress;
use crate::ratio::Rat;
use crate::ratio::algebraic::ExactInterval;
use crate::ratio::gcd;
use crate::ratio::linear::vector::lcm;

/// [definition] **A grating**: a closing rotor ring of period `q ≥ 2` keyed at the port `c < q`,
/// turning `p` ports a tick, `0 < p < q`, `gcd(p, q) = 1`: rate `p/q`, phase `c/q`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Grating {
    numerator: u64,
    denominator: u64,
    phase: u64,
    rotor: Navigator,
}

impl Grating {
    /// The grating of rate `numerator/denominator` at phase `phase/denominator`; refused unless
    /// `0 < p < q`, `gcd(p, q) = 1` and `c < q` (a rate is a unit of `ℤ/q`, so the ring visits every
    /// port and its period is `q`).
    pub fn new(numerator: u64, denominator: u64, phase: u64) -> Result<Self, TerrainError> {
        if numerator == 0 || numerator >= denominator || phase >= denominator {
            return Err(refuse(
                "a grating",
                "its rate p/q needs 0 < p < q and its phase c < q",
            ));
        }
        if !gcd(&BigInt::from(numerator), &BigInt::from(denominator)).is_one() {
            return Err(refuse("a grating", "its rate p/q needs gcd(p, q) = 1"));
        }
        let rotor = Navigator::rotor(denominator, phase, Rat::one())?;
        Ok(Self {
            numerator,
            denominator,
            phase,
            rotor,
        })
    }

    /// `p`: the ports the ring turns a tick.
    pub fn numerator(&self) -> u64 {
        self.numerator
    }

    /// `q`: the ring's period.
    pub fn denominator(&self) -> u64 {
        self.denominator
    }

    /// `c`: the ring's key, its port at tick zero.
    pub fn phase(&self) -> u64 {
        self.phase
    }

    /// The rate `p/q` of a turn a tick.
    pub fn rate(&self) -> Rat {
        Rat::new(BigInt::from(self.numerator), BigInt::from(self.denominator))
    }

    /// The ring as its navigator: the rotor of period `q` keyed at `c`.
    pub fn rotor(&self) -> &Navigator {
        &self.rotor
    }

    /// **The ring's port at tick `t`**: the rotor's port after `t p` of its ticks, `(c + t p) mod q`.
    pub fn port(&self, tick: u64) -> u64 {
        let ticks = BigUint::from(tick) * BigUint::from(self.numerator);
        self.rotor
            .port_after(&ticks)
            .expect("a rotor keyed at one port has a port after every tick") as u64
    }

    /// **The half-turn sheet at tick `t`**: `2·port ≥ q`, the side of the half-turn the ring's phase
    /// lies on.
    pub fn sheet(&self, tick: u64) -> bool {
        2 * self.port(tick) >= self.denominator
    }
}

/// [definition] **The emitted joint class**: the parity color `Σ s_i mod 2`, or the sheet tuple
/// `Σ s_i 2^i`.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MoireClass {
    Parity,
    Sheets,
}

/// [definition] **The declared draw family**: `rings` gratings, each drawn uniformly among the
/// triples `(p, q, c)` with `2 ≤ q ≤ denominator`, `0 < p < q`, `gcd(p, q) = 1`, `0 ≤ c < q`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MoireFamily {
    pub rings: usize,
    pub denominator: u64,
}

impl MoireFamily {
    /// The units `0 < p < q` of `ℤ/q`, ascending.
    fn units(q: u64) -> Vec<u64> {
        (1..q)
            .filter(|p| gcd(&BigInt::from(*p), &BigInt::from(q)).is_one())
            .collect()
    }

    /// **One grating's key space** `N_Q = Σ_(q=2)^Q q·φ(q)`.
    pub fn gratings(&self) -> u64 {
        (2..=self.denominator)
            .map(|q| q * Self::units(q).len() as u64)
            .sum()
    }

    /// **The key space** `N_Q^k`.
    pub fn key_space(&self) -> BigUint {
        BigUint::from(self.gratings()).pow(
            u32::try_from(self.rings).expect("a count of rings within a machine word"),
        )
    }

    /// **The key description** `⌈log₂ N_Q^k⌉` bits.
    pub fn key_bits(&self) -> u64 {
        ceil_log2(&self.key_space())
    }

    /// The grating at `index < N_Q`, in the order `(q, p, c)` ascending.
    fn grating(&self, mut index: u64) -> Result<Grating, TerrainError> {
        for q in 2..=self.denominator {
            let units = Self::units(q);
            let block = q * units.len() as u64;
            if index < block {
                return Grating::new(units[(index / q) as usize], q, index % q);
            }
            index -= block;
        }
        Err(refuse(
            "a grating index",
            "it lies past the family's key space",
        ))
    }

    fn check(&self) -> Result<(), TerrainError> {
        if self.rings == 0 || self.denominator < 2 {
            return Err(refuse(
                "a moiré family",
                "it needs at least one ring and a denominator of at least 2",
            ));
        }
        Ok(())
    }
}

/// [definition] **A pair's lock** (module header): the rate ratio `r_i/r_j`, its Farey lock address
/// and period (the turns of ring `j` before the pair returns), and the contact law's reading over
/// one joint period's whole windings `(m_i, m_j)`, bounded by those windings (the horizon of one
/// joint period).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PairLock {
    pub rings: (usize, usize),
    pub ratio: Rat,
    pub address: LockAddress,
    pub period: BigInt,
    pub windings: (BigInt, BigInt),
    pub reading: ContactLock,
}

/// [definition] **The moiré's exact truth receipt** (module header).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MoireTruth {
    pub gratings: Vec<Grating>,
    pub joint_period: BigUint,
    pub least_period: usize,
    pub depth: usize,
    pub locks: Vec<PairLock>,
    pub rate: ExactInterval,
    pub key_space: BigUint,
    pub key_bits: u64,
}

/// [definition] **The moiré terrain** (module header): its gratings and its declared class.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Moire {
    gratings: Vec<Grating>,
    class: MoireClass,
}

impl Moire {
    /// The moiré of the declared gratings; refused without a grating, or with more gratings than a
    /// sheet tuple's code holds.
    pub fn new(gratings: Vec<Grating>, class: MoireClass) -> Result<Self, TerrainError> {
        if gratings.is_empty() || gratings.len() >= usize::BITS as usize {
            return Err(refuse(
                "a moiré",
                "it needs at least one grating, and fewer than a machine word's bits",
            ));
        }
        Ok(Self { gratings, class })
    }

    /// **The moiré drawn from its family** (module header): each grating uniform among the family's
    /// `N_Q` triples.
    pub fn draw(
        family: &MoireFamily,
        class: MoireClass,
        draw: &mut Draw,
    ) -> Result<Self, TerrainError> {
        family.check()?;
        let count = usize::try_from(family.gratings()).expect("a key space within a machine word");
        let gratings = (0..family.rings)
            .map(|_| family.grating(draw.below(count) as u64))
            .collect::<Result<Vec<_>, _>>()?;
        Self::new(gratings, class)
    }

    pub fn gratings(&self) -> &[Grating] {
        &self.gratings
    }

    pub fn class(&self) -> MoireClass {
        self.class
    }

    /// The cells' alphabet: `2` for the parity color, `2^k` for the sheet tuple.
    pub fn alphabet(&self) -> usize {
        match self.class {
            MoireClass::Parity => 2,
            MoireClass::Sheets => 1 << self.gratings.len(),
        }
    }

    /// **The Holarchy's parametric orientation**: the lift of the rings' joint clock torus, one
    /// circle of period `q_i` a ring (`aeon::ClockLift::of_clocks`, as `Holarchy::parametric`).
    pub fn parametric(&self) -> ClockLift {
        ClockLift::of_clocks(
            &self
                .gratings
                .iter()
                .map(|grating| grating.rotor.clock().clone())
                .collect::<Vec<_>>(),
        )
    }

    /// **The cell at tick `t`** with the active gratings' sheets; a silent grating's sheet reads 0.
    pub fn cell(&self, tick: u64, active: &[bool]) -> usize {
        let sheets = self
            .gratings
            .iter()
            .zip(active)
            .map(|(grating, on)| *on && grating.sheet(tick));
        match self.class {
            MoireClass::Parity => sheets.filter(|sheet| *sheet).count() % 2,
            MoireClass::Sheets => sheets
                .enumerate()
                .map(|(i, sheet)| usize::from(sheet) << i)
                .sum(),
        }
    }

    /// **The first `cells` cells**, every grating active.
    pub fn emit(&self, cells: usize) -> Vec<usize> {
        self.emit_active(cells, &vec![true; self.gratings.len()])
    }

    /// **The first `cells` cells** with the declared gratings active (the rest silent, still
    /// turning); `active` is read one flag a grating, a missing flag silent.
    pub fn emit_active(&self, cells: usize, active: &[bool]) -> Vec<usize> {
        let mut flags = active.to_vec();
        flags.resize(self.gratings.len(), false);
        (0..cells as u64)
            .map(|tick| self.cell(tick, &flags))
            .collect()
    }

    /// **The joint period** `lcm(q_i)`.
    pub fn joint_period(&self) -> BigUint {
        self.gratings
            .iter()
            .fold(BigInt::one(), |period, grating| {
                lcm(&period, &BigInt::from(grating.denominator))
            })
            .to_biguint()
            .expect("a least common multiple of periods is positive")
    }

    /// **The moiré's exact truth receipt** under its declared draw family (module header). It
    /// reads one joint period of cells; refused when a grating lies outside the family.
    pub fn truth(&self, family: &MoireFamily) -> Result<MoireTruth, TerrainError> {
        family.check()?;
        if self.gratings.len() != family.rings
            || self
                .gratings
                .iter()
                .any(|grating| grating.denominator > family.denominator)
        {
            return Err(refuse(
                "a moiré's truth",
                "its gratings are not a member of the declared family",
            ));
        }
        let joint_period = self.joint_period();
        let period = usize::try_from(&joint_period).map_err(|_| {
            refuse(
                "a moiré's truth",
                "its joint period exceeds the machine's address space",
            )
        })?;
        let word = self.emit(period);
        let least_period = least_period(&word);
        let depth = determining_depth(&word[..least_period]);
        let mut locks = Vec::new();
        for i in 0..self.gratings.len() {
            for j in i + 1..self.gratings.len() {
                locks.push(self.pair_lock(i, j, &joint_period)?);
            }
        }
        Ok(MoireTruth {
            gratings: self.gratings.clone(),
            joint_period,
            least_period,
            depth,
            locks,
            rate: ExactInterval::point(Rat::zero()),
            key_space: family.key_space(),
            key_bits: family.key_bits(),
        })
    }

    /// The pair `(i, j)`'s lock (module header).
    fn pair_lock(
        &self,
        i: usize,
        j: usize,
        joint_period: &BigUint,
    ) -> Result<PairLock, TerrainError> {
        let (first, second) = (&self.gratings[i], &self.gratings[j]);
        let ratio = first.rate() / second.rate();
        let clocks = TwoClocks::new(ratio.clone())?;
        let address = clocks.lock_address()?;
        let period = ratio.denom().clone();
        let windings = |grating: &Grating| {
            BigInt::from(joint_period.clone()) * BigInt::from(grating.numerator)
                / BigInt::from(grating.denominator)
        };
        let (m_i, m_j) = (windings(first), windings(second));
        let horizon = LockDeclaration {
            numerator: m_i.to_biguint().expect("whole windings of a forward aeon"),
            denominator: m_j.to_biguint().expect("whole windings of a forward aeon"),
        };
        let reading = lock_address(&m_i, &m_j, &horizon);
        Ok(PairLock {
            rings: (i, j),
            ratio,
            address,
            period,
            windings: (m_i, m_j),
            reading,
        })
    }
}

/// **The least period of a cyclic word**: the least divisor `d` of its length with
/// `w[t] = w[(t + d) mod n]` for every `t`.
pub(crate) fn least_period(word: &[usize]) -> usize {
    let n = word.len();
    (1..=n)
        .filter(|d| n.is_multiple_of(*d))
        .find(|&d| (0..n).all(|t| word[t] == word[(t + d) % n]))
        .unwrap_or(n)
}

/// **The determining depth of a cyclic word**: the least `D` such that the `D` letters before every
/// position (read cyclically) determine its letter. At most the word's length when the word is
/// primitive, since its rotations are then distinct.
pub(crate) fn determining_depth(word: &[usize]) -> usize {
    let n = word.len();
    let doubled: Vec<usize> = word.iter().chain(word).copied().collect();
    (0..=n)
        .find(|&depth| {
            let mut next: HashMap<&[usize], usize> = HashMap::new();
            (0..n).all(|t| {
                let window = &doubled[t + n - depth..t + n];
                *next.entry(window).or_insert(word[t]) == word[t]
            })
        })
        .unwrap_or(n)
}
