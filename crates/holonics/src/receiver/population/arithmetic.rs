//! **The arithmetic eggs: a record clock, the carry egg, the counter and the sieve, composed at
//! ports** (`holarchy::terrain::arithmetic`; the notebook's arithmetic receipts in
//! `research/notebook/hnn_design/README.md`, "What the arithmetic families need from the population
//! owner"; #73).
//!
//! [definition; agent-inferred] Each egg is keyed by the terrain's declared family only (its base,
//! digits, order, face width and window), never by a drawn value: the operands a product record
//! carries are drawn, so the carry egg pays their entropy exactly, and the counter's start is its
//! key, located from the cells.
//! - **The record clock** ([`RecordClock`], the keystone): a navigator on the record's period
//!   `R` (`4L + 3` for a product record, `L + 1` for a prime record), keyed by its offset
//!   `o ∈ [0, R)`, the phase of the passage's first cell. At tick `t` its port reads the phase
//!   `(o + t) mod R` and the records completed `(o + t) div R`: a helix, circle plus carry.
//! - **The carry egg** ([`CarryEgg`], reads the clock): on the operand phases uniform over the base
//!   (the operands are drawn, so their code is their entropy exactly); on the marks deterministic;
//!   on the product's phases deterministic from the operands' digits read at their phases, by the
//!   terrain's convolution and carry (`holarchy::terrain::arithmetic::digit_product`, Lean
//!   `RadixWindowReceiver.digit_product_is_carry_of_convolution`), least or most significant first
//!   as declared. A product phase whose operands it did not read whole (a key joining mid-record) is
//!   uniform over the base.
//! - **The counter** ([`Counter`], a keystone reading the clock): the odometer of `L` levels of
//!   radix `b`, keyed by its start `s ∈ [0, b^L)`; its port passes the clock's phase through and
//!   reads the integer `(s + records completed) mod b^L`, the odometer counting up by one a record
//!   with carry (its lowest wheel's winding).
//! - **The sieve** ([`Sieve`], reads the counter): on a digit phase the counter's digit at its place;
//!   on the primality phase the verdict of the gratings up to `√(b^L − 1)` laid over the counter's
//!   range, read after the base's cheap faces: the last digit reads the primes of `b`, the digit sum
//!   those of `b − 1`, the alternating sum those of `b + 1` (Lean `RadixWindowReceiver.cheap_faces`),
//!   then each grating `p` on the leading index, `p ∣ b^m k + r ⇔ k ≡ k_p(r) mod p`
//!   (`grating_class`, Lean `grating_on_digit_index`). Its description is the window's declaration:
//!   the verdicts over the range are computed once from that law ([`Sieve::verdict`]), the gratings
//!   laid over the window, and each integer's deciding face is its work ([`SieveFace`]).
//!
//! [definition; agent-inferred] **The composed eggs** ([`Composed::products`],
//! [`Composed::primes`]): `clock ⊳ carry` on a product terrain and `clock ⊳ (counter ⊳ sieve)` on a
//! prime stream; the reader at an unheld counter ([`Composed::primes_unheld_counter`]) is the
//! sieve without its keystone, the counter's value read against it. The record clock's value is
//! read at the population: without it neither the carry egg nor the counter has a port (both hold
//! state along the clock's phases), so the joint code without it is the population's other eggs.
//!
//! [definition] The computational object is the helical pair interaction as eggs joined at ports:
//! the clock's **helix** (the phase and its carry), the counter's odometer (its winding), **faces
//! and placement** (each phase's face, the cheap faces and the gratings placed on the leading
//! index) and the **tower thread** (a record's phases restrict a cell to its place). The **pair**
//! (the convolution pairs digit `i` with digit `j` at place `i + j`) is read through the terrain's
//! `digit_product`; the cell holonomy and the tube stay attached.

use std::sync::Arc;

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::composition::{
    Composed, Conditioned, Keystone, Port, PortPath, PortReader, PortedEmitters, Unheld,
};
use super::{
    Family, KeyFamily, KeyReadout, Likelihood, PopulationError, Readout, Survivors, refuse,
};
use crate::compression::landmark::context::PassageCode;
use crate::holarchy::terrain::arithmetic::{
    CheapFaces, DigitOrder, PrimeEmission, PrimeWindow, ProductFamily, digit_product, grating_class,
};
use crate::ratio::Rat;

/// **The Bombe a counter's key space is owed to** past the declared enumeration: its start read
/// from one record's digits at the located phase (the odometer's reading at its port).
pub const COUNTER_BOMBE: &str =
    "the counter's start read from one record's digits at the located clock phase; owed";

// -------------------------------------------------------------------------------------------
// the record clock

/// [definition] **The record clock** (module header): period `R`, keyed by its offset.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecordClock {
    period: u64,
}

impl RecordClock {
    /// The clock of a declared period; refused at an empty period.
    pub fn new(period: u64) -> Result<Self, PopulationError> {
        if period == 0 {
            return Err(refuse("a record clock", "its period holds a phase"));
        }
        Ok(Self { period })
    }

    /// **A product record's clock**, period `4L + 3`.
    pub fn products(family: &ProductFamily) -> Result<Self, PopulationError> {
        family.operands()?;
        Self::new(family.record_length() as u64)
    }

    /// **A prime record's clock**, period `L + 1`; refused for the indicator emission.
    pub fn primes(window: &PrimeWindow) -> Result<Self, PopulationError> {
        digit_window(window)?;
        Self::new(window.record_length() as u64)
    }

    /// `R`.
    pub fn period(&self) -> u64 {
        self.period
    }
}

impl Keystone for RecordClock {
    fn label(&self) -> String {
        format!("record clock of period {}", self.period)
    }

    fn keys(&self) -> u64 {
        self.period
    }

    fn port(&self, key: u64, upstream: Port) -> Port {
        let position = key + upstream.winding;
        Port {
            phase: position % self.period,
            winding: position / self.period,
        }
    }

    fn coordinates(&self, key: u64) -> Vec<u64> {
        vec![key]
    }
}

fn digit_window(window: &PrimeWindow) -> Result<(), PopulationError> {
    if window.emission != PrimeEmission::Digits {
        return Err(refuse(
            "a prime record's eggs",
            "they read the digit emission (digit cells and a primality cell)",
        ));
    }
    window.cheap_faces()?;
    Ok(())
}

// -------------------------------------------------------------------------------------------
// the carry egg

/// A product record's part at a phase: an operand's place, a mark, or a product place.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Part {
    Left(usize),
    Times,
    Right(usize),
    Equals,
    Product(usize),
    Record,
}

/// [definition] **The carry egg** (module header): reads the record clock's phase along its port
/// path; holds the record's operand digits read at their phases and, once both are whole, their
/// product's digit word.
pub struct CarryEgg {
    family: ProductFamily,
    upstream: PortPath,
    tick: u64,
    port: Port,
    left: Vec<Option<u64>>,
    right: Vec<Option<u64>>,
    product: Option<Vec<u64>>,
    passage: PassageCode,
    description: u64,
}

impl CarryEgg {
    /// The carry egg of a declared product family on a port path reading a product record's clock.
    pub fn new(
        family: &ProductFamily,
        upstream: PortPath,
        description: u64,
    ) -> Result<Self, PopulationError> {
        family.operands()?;
        let port = upstream.read(0);
        Ok(Self {
            family: family.clone(),
            upstream,
            tick: 0,
            port,
            left: vec![None; family.digits],
            right: vec![None; family.digits],
            product: None,
            passage: PassageCode::new(),
            description,
        })
    }

    fn part(&self) -> Part {
        let l = self.family.digits;
        let order = self.family.order;
        let phase = (self.port.phase % self.family.record_length() as u64) as usize;
        match phase {
            p if p < l => Part::Left(order.place(p, l)),
            p if p == l => Part::Times,
            p if p < 2 * l + 1 => Part::Right(order.place(p - l - 1, l)),
            p if p == 2 * l + 1 => Part::Equals,
            p if p < 4 * l + 2 => Part::Product(order.place(p - 2 * l - 2, 2 * l)),
            _ => Part::Record,
        }
    }

    /// **The egg's face of `cell`** at the current phase.
    fn face_of(&self, cell: usize) -> Rat {
        let base = self.family.base as usize;
        let uniform = || {
            if cell < base {
                Rat::new(BigInt::one(), BigInt::from(base))
            } else {
                Rat::zero()
            }
        };
        let mark = |at: usize| if cell == at { Rat::one() } else { Rat::zero() };
        match self.part() {
            Part::Left(_) | Part::Right(_) => uniform(),
            Part::Times => mark(self.family.times()),
            Part::Equals => mark(self.family.equals()),
            Part::Record => mark(self.family.record_mark()),
            Part::Product(place) => match &self.product {
                Some(word) => mark(word[place] as usize),
                None => uniform(),
            },
        }
    }

    /// The deposit of a cell the egg gave a positive face.
    fn deposit(&mut self, cell: usize) -> Result<(), PopulationError> {
        match self.part() {
            Part::Left(place) => self.left[place] = Some(cell as u64),
            Part::Right(place) => self.right[place] = Some(cell as u64),
            Part::Equals => {
                let whole =
                    |word: &[Option<u64>]| word.iter().copied().collect::<Option<Vec<u64>>>();
                if let (Some(left), Some(right)) = (whole(&self.left), whole(&self.right)) {
                    let mut word = digit_product(self.family.base, &left, &right)?.digits;
                    word.resize(2 * self.family.digits, 0);
                    self.product = Some(word);
                }
            }
            Part::Record => {
                self.left.fill(None);
                self.right.fill(None);
                self.product = None;
            }
            Part::Times | Part::Product(_) => {}
        }
        Ok(())
    }
}

impl Family for CarryEgg {
    fn label(&self) -> String {
        format!(
            "carry egg: base {}, L = {}, {}",
            self.family.base,
            self.family.digits,
            order_name(self.family.order)
        )
    }

    fn alphabet(&self) -> usize {
        self.family.alphabet()
    }

    fn description(&self) -> u64 {
        self.description
    }

    fn face(&self) -> Result<Vec<Rat>, PopulationError> {
        Ok((0..self.alphabet())
            .map(|cell| self.face_of(cell))
            .collect())
    }

    /// The face read before the deposit; a cell given zero deposits nothing.
    fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError> {
        let alphabet = self.alphabet();
        if cell >= alphabet {
            return Err(PopulationError::CellOutside { cell, alphabet });
        }
        let face = self.face_of(cell);
        if face.is_zero() {
            return Ok(face);
        }
        self.deposit(cell)?;
        self.tick += 1;
        self.port = self.upstream.read(self.tick);
        self.passage.face(&face)?;
        Ok(face)
    }

    fn likelihood(&self) -> Likelihood {
        Likelihood::Enclosed(self.passage)
    }

    /// The carry egg holds no key: its genome is the declaration.
    fn readout(&self) -> Readout<'_> {
        Readout::Keys(KeyReadout {
            spaces: Vec::new(),
            survivors: Vec::new(),
            masses: Vec::new(),
            dormant: Vec::new(),
        })
    }
}

fn order_name(order: DigitOrder) -> &'static str {
    match order {
        DigitOrder::LeastFirst => "least significant first",
        DigitOrder::MostFirst => "most significant first",
    }
}

// -------------------------------------------------------------------------------------------
// the counter

/// [definition] **The counter** (module header): an odometer of `L` levels of radix `b`, keyed by
/// its start, reading the clock's port.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Counter {
    base: u64,
    digits: usize,
    range: u64,
}

impl Counter {
    /// **The counter of a prime window's records**; refused for the indicator emission.
    pub fn of(window: &PrimeWindow) -> Result<Self, PopulationError> {
        digit_window(window)?;
        let range = u32::try_from(window.digits)
            .ok()
            .and_then(|digits| window.base.checked_pow(digits))
            .ok_or_else(|| refuse("a counter", "its range b^L fits a machine word"))?;
        Ok(Self {
            base: window.base,
            digits: window.digits,
            range,
        })
    }

    /// `b^L`, the odometer's range.
    pub fn range(&self) -> u64 {
        self.range
    }
}

impl Keystone for Counter {
    fn label(&self) -> String {
        format!(
            "counter: {} digits in base {}, keyed by its start",
            self.digits, self.base
        )
    }

    fn keys(&self) -> u64 {
        self.range
    }

    fn port(&self, key: u64, clock: Port) -> Port {
        Port {
            phase: clock.phase,
            winding: (key + clock.winding % self.range) % self.range,
        }
    }

    fn coordinates(&self, key: u64) -> Vec<u64> {
        vec![key]
    }
}

// -------------------------------------------------------------------------------------------
// the sieve

/// [definition] **The face that decides an integer's primality** (module header): below two, a
/// cheap face and its prime, a grating and its prime, or a gap of every grating (a prime).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum SieveFace {
    Unit,
    LastDigit(u64),
    DigitSum(u64),
    Alternating(u64),
    Grating(u64),
    Gap,
}

/// [definition] **The sieve** (module header): the counter's digits on the digit phases and the
/// gratings' verdict on the primality phase, over the counter's range.
pub struct Sieve {
    base: u64,
    digits: usize,
    order: DigitOrder,
    unit: u64,
    cheap: [Vec<u64>; 3],
    gratings: Vec<(u64, Vec<u64>)>,
    prime: Vec<bool>,
}

impl Sieve {
    /// **The sieve of a prime window's records**, its verdicts laid over the counter's range `b^L`;
    /// refused past the declared enumeration `admitted` or for the indicator emission.
    pub fn of(window: &PrimeWindow, admitted: u64) -> Result<Self, PopulationError> {
        let counter = Counter::of(window)?;
        let range = counter.range;
        if range > admitted {
            return Err(refuse(
                "a sieve",
                "its range b^L lies within the declared enumeration",
            ));
        }
        let unit = u32::try_from(window.trailing)
            .ok()
            .and_then(|trailing| window.base.checked_pow(trailing))
            .ok_or_else(|| refuse("a sieve", "b^m fits a machine word"))?;
        let cheap = CheapFaces::of(window.base)?.primes();
        let root = (1..)
            .take_while(|p: &u64| p * p < range)
            .last()
            .unwrap_or(1);
        let gratings = (2..=root)
            .filter(|&p| cheap.iter().all(|primes| !primes.contains(&p)))
            .filter_map(|p| {
                let classes = (0..unit)
                    .map(|residue| grating_class(window.base, window.trailing, residue, p))
                    .collect::<Option<Vec<u64>>>()?;
                Some((p, classes))
            })
            .collect();
        let mut sieve = Self {
            base: window.base,
            digits: window.digits,
            order: window.order,
            unit,
            cheap,
            gratings,
            prime: Vec::new(),
        };
        sieve.prime = (0..range).map(|n| sieve.verdict(n).0).collect();
        Ok(sieve)
    }

    /// The gratings `p` (primes up to `√(b^L − 1)` no cheap face reads) with their classes by
    /// residue.
    pub fn gratings(&self) -> impl Iterator<Item = u64> + '_ {
        self.gratings.iter().map(|(p, _)| *p)
    }

    /// The primes each cheap face reads: `[last digit, digit sum, alternating sum]`.
    pub fn cheap(&self) -> &[Vec<u64>; 3] {
        &self.cheap
    }

    /// **The verdict of the law** on `n` (module header): the cheap faces first, then the gratings;
    /// the deciding face beside it.
    pub fn verdict(&self, n: u64) -> (bool, SieveFace) {
        if n < 2 {
            return (false, SieveFace::Unit);
        }
        let b = self.base;
        let (mut sum, mut alternating, mut rest, mut place) = (0u64, 0i64, n, 0u32);
        while rest > 0 {
            let digit = rest % b;
            sum += digit;
            alternating += if place % 2 == 0 {
                digit as i64
            } else {
                -(digit as i64)
            };
            rest /= b;
            place += 1;
        }
        let [last, sums, alternatings] = &self.cheap;
        if let Some(&p) = last.iter().find(|&&p| (n % b) % p == 0) {
            return (n == p, SieveFace::LastDigit(p));
        }
        if let Some(&p) = sums.iter().find(|&&p| sum % p == 0) {
            return (n == p, SieveFace::DigitSum(p));
        }
        if let Some(&p) = alternatings
            .iter()
            .find(|&&p| alternating.rem_euclid(p as i64) == 0)
        {
            return (n == p, SieveFace::Alternating(p));
        }
        let (leading, residue) = (n / self.unit, (n % self.unit) as usize);
        for (p, classes) in &self.gratings {
            if leading % p == classes[residue] {
                return (n == *p, SieveFace::Grating(*p));
            }
        }
        (true, SieveFace::Gap)
    }
}

impl PortReader for Sieve {
    fn label(&self) -> String {
        format!(
            "sieve: base {}, the gratings up to √(b^L − 1) over [0, {}), the cheap faces first",
            self.base,
            self.prime.len()
        )
    }

    fn alphabet(&self) -> usize {
        self.base as usize + 2
    }

    fn emit(&self, port: Port) -> usize {
        let phase = port.phase as usize;
        if phase < self.digits {
            let place = self.order.place(phase, self.digits) as u32;
            return ((port.winding / self.base.pow(place)) % self.base) as usize;
        }
        let prime = self
            .prime
            .get(port.winding as usize)
            .copied()
            .unwrap_or(false);
        self.base as usize + usize::from(prime)
    }
}

// -------------------------------------------------------------------------------------------
// the composed eggs

impl Composed {
    /// **`clock ⊳ carry` on a declared product family** (module header).
    pub fn products(family: &ProductFamily, description: u64) -> Result<Self, PopulationError> {
        let clock = Arc::new(RecordClock::products(family)?);
        let declared = family.clone();
        let conditioned: Conditioned = Box::new(move |path| {
            Ok(Box::new(CarryEgg::new(&declared, path, 0)?) as Box<dyn Family>)
        });
        let label = format!(
            "{} ⊳ carry egg (base {}, L = {}, {})",
            clock.label(),
            family.base,
            family.digits,
            order_name(family.order)
        );
        let keys = clock.keys();
        Self::new(
            label,
            description,
            clock,
            &PortPath::tick(),
            &conditioned,
            keys,
        )
    }

    /// **`clock ⊳ (counter ⊳ sieve)` on a declared prime window** (module header): the counter's
    /// starts survivor filtered under each clock key, within the declared enumeration `admitted`.
    pub fn primes(
        window: &PrimeWindow,
        admitted: u64,
        description: u64,
    ) -> Result<Self, PopulationError> {
        let (clock, counter, sieve) = prime_eggs(window, admitted)?;
        let label = format!(
            "{} ⊳ ({} ⊳ {})",
            clock.label(),
            counter.label(),
            sieve.label()
        );
        let conditioned: Conditioned = Box::new(move |path| {
            let emitters = PortedEmitters::new(counter.clone(), sieve.clone(), path)?;
            let factor = Survivors::new(Box::new(emitters), admitted, COUNTER_BOMBE)?;
            Ok(Box::new(KeyFamily::new(
                "counter ⊳ sieve".to_string(),
                0,
                vec![factor],
            )?) as Box<dyn Family>)
        });
        let keys = clock.keys();
        Self::new(
            label,
            description,
            clock,
            &PortPath::tick(),
            &conditioned,
            keys,
        )
    }

    /// **`clock ⊳ (unheld counter ⊳ sieve)`** (module header): the sieve at the counter's unheld
    /// port under each clock key, the counter's value read against [`Composed::primes`].
    pub fn primes_unheld_counter(
        window: &PrimeWindow,
        admitted: u64,
        description: u64,
    ) -> Result<Self, PopulationError> {
        let (clock, counter, sieve) = prime_eggs(window, admitted)?;
        let label = format!(
            "{} ⊳ (unheld {} ⊳ {})",
            clock.label(),
            counter.label(),
            sieve.label()
        );
        let conditioned: Conditioned = Box::new(move |path| {
            let emitters = PortedEmitters::new(counter.clone(), sieve.clone(), path)?;
            Ok(Box::new(Unheld::new(
                "unheld counter ⊳ sieve".to_string(),
                0,
                emitters,
            )) as Box<dyn Family>)
        });
        let keys = clock.keys();
        Self::new(
            label,
            description,
            clock,
            &PortPath::tick(),
            &conditioned,
            keys,
        )
    }
}

type PrimeEggs = (Arc<RecordClock>, Arc<dyn Keystone>, Arc<dyn PortReader>);

fn prime_eggs(window: &PrimeWindow, admitted: u64) -> Result<PrimeEggs, PopulationError> {
    let clock = Arc::new(RecordClock::primes(window)?);
    let counter: Arc<dyn Keystone> = Arc::new(Counter::of(window)?);
    let sieve: Arc<dyn PortReader> = Arc::new(Sieve::of(window, admitted)?);
    Ok((clock, counter, sieve))
}
