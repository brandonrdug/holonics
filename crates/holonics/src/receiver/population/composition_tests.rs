//! Composition at ports checked exactly on small fixtures: the composed face is a face and its
//! product telescopes to the keystone's prior mixture (against the conditioned families stepped
//! apart in ℚ), the chain rule along the surviving keys, a reader keyed through a keystone against
//! brute force, the reader at an unheld port, and the arithmetic eggs: the sieve against primality,
//! the carry egg locating the record clock and paying the operands' entropy exactly, the counter
//! and sieve locating the start, and the partition's reading summing to the passage's code.

use std::sync::Arc;

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::composition::{
    Composed, Conditioned, Keystone, Port, PortPath, PortReader, PortedEmitters, Unheld,
};
use super::*;
use crate::compression::landmark::context::{
    Capacity, LandmarkDeclaration, LetterFamily, StopPrior,
};
use crate::holarchy::terrain::Draw;
use crate::holarchy::terrain::arithmetic::{
    DigitOrder, PrimeEmission, PrimeWindow, ProductCell, ProductFamily, Products,
};
use crate::ratio::algebraic::{ExactInterval, interval_difference};
use crate::ratio::primality::is_prime;
use crate::ratio::surprisal::SymbolicSurprisal;

fn rational(numerator: i64, denominator: i64) -> Rat {
    Rat::new(BigInt::from(numerator), BigInt::from(denominator))
}

/// Whether an enclosure of a code lies within `2^(−32)` of an exact form's enclosure.
fn encloses(code: &ExactInterval, truth: &SymbolicSurprisal) {
    let truth = truth.enclosure().expect("the truth's enclosure");
    let slack = Rat::new(BigInt::one(), BigInt::one() << 32);
    assert!(
        code.lower <= &truth.upper + &slack && code.upper >= &truth.lower - &slack,
        "code [{}, {}] against the truth [{}, {}]",
        code.lower,
        code.upper,
        truth.lower,
        truth.upper
    );
}

fn log2_of(value: i64) -> SymbolicSurprisal {
    SymbolicSurprisal::log2_of_ratio(&Rat::from_integer(BigInt::from(value))).expect("log₂")
}

/// A ring of `period` phases keyed by its offset, reading the passage's clock.
struct Ring(u64);

impl Keystone for Ring {
    fn label(&self) -> String {
        format!("ring of period {}", self.0)
    }
    fn keys(&self) -> u64 {
        self.0
    }
    fn port(&self, key: u64, upstream: Port) -> Port {
        Port {
            phase: (key + upstream.winding) % self.0,
            winding: (key + upstream.winding) / self.0,
        }
    }
    fn coordinates(&self, key: u64) -> Vec<u64> {
        vec![key]
    }
    fn declaration(&self) -> Declaration {
        Declaration::new("ring", vec![self.0])
    }
}

/// A family whose face is a declared table by the phase its port reads.
struct ByPhase {
    table: Vec<Vec<Rat>>,
    upstream: PortPath,
    tick: u64,
    likelihood: Rat,
}

impl ByPhase {
    fn new(table: Vec<Vec<Rat>>, upstream: PortPath) -> Self {
        Self {
            table,
            upstream,
            tick: 0,
            likelihood: Rat::one(),
        }
    }
    fn row(&self) -> &[Rat] {
        &self.table[self.upstream.read(self.tick).phase as usize]
    }
}

impl Family for ByPhase {
    fn label(&self) -> String {
        "by phase".to_string()
    }
    fn alphabet(&self) -> usize {
        self.table[0].len()
    }
    fn description(&self) -> u64 {
        0
    }
    fn face(&self) -> Result<Vec<Rat>, PopulationError> {
        Ok(self.row().to_vec())
    }
    fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError> {
        let face = self.row()[cell].clone();
        if !face.is_zero() {
            self.likelihood *= &face;
            self.tick += 1;
        }
        Ok(face)
    }
    fn likelihood(&self) -> Likelihood {
        Likelihood::Exact(self.likelihood.clone())
    }
    fn readout(&self) -> Readout<'_> {
        Readout::Keys(KeyReadout {
            spaces: Vec::new(),
            survivors: Vec::new(),
            masses: Vec::new(),
            dormant: Vec::new(),
        })
    }
    fn declaration(&self) -> Declaration {
        Declaration::new("by phase", vec![self.table.len() as u64])
    }
}

/// Phase 0 emits class 0, phase 1 is uniform over classes 1 and 2, phase 2 emits class 3.
fn table() -> Vec<Vec<Rat>> {
    let (zero, one, half) = (Rat::zero(), Rat::one(), rational(1, 2));
    vec![
        vec![one.clone(), zero.clone(), zero.clone(), zero.clone()],
        vec![zero.clone(), half.clone(), half, zero.clone()],
        vec![zero.clone(), zero.clone(), zero, one],
    ]
}

#[test]
fn the_composed_face_is_a_face_and_telescopes_to_the_keystone_mixture() {
    let ring: Arc<dyn Keystone> = Arc::new(Ring(3));
    let conditioned: Conditioned =
        Arc::new(|path| Ok(Box::new(ByPhase::new(table(), path)) as Box<dyn Family>));
    let mut composed = Composed::new(
        "ring ⊳ by phase".to_string(),
        0,
        Arc::clone(&ring),
        &PortPath::tick(),
        &conditioned,
        3,
    )
    .expect("a composed family");
    // The passage key 1 makes: phases 1, 2, 0, 1, 2, 0, … with the uniform phase's draws.
    let cells = [1, 3, 0, 2, 3, 0, 1, 3, 0, 1];
    let mut apart: Vec<ByPhase> = (0..3)
        .map(|key| ByPhase::new(table(), PortPath::tick().through(Arc::clone(&ring), key)))
        .collect();
    let mut product = Rat::one();
    for &cell in &cells {
        let face = composed.face().expect("its face");
        assert_eq!(
            face.iter().sum::<Rat>(),
            Rat::one(),
            "the composed face sums to one"
        );
        assert!(face.iter().all(|class| *class >= Rat::zero()));
        let before: Rat = apart
            .iter()
            .map(|family| family.likelihood.clone() / rational(3, 1))
            .sum();
        for family in &mut apart {
            if !family.likelihood.is_zero() {
                let face = family.row()[cell].clone();
                family.likelihood *= &face;
                if !face.is_zero() {
                    family.tick += 1;
                }
            }
        }
        let after: Rat = apart
            .iter()
            .map(|family| family.likelihood.clone() / rational(3, 1))
            .sum();
        let received = composed.receive(cell).expect("the cell");
        assert_eq!(
            received,
            &after / &before,
            "the composed face is the mixture's step"
        );
        assert_eq!(received, face[cell]);
        product *= received;
    }
    // The telescope: Σ_a π_a L_a, and one key survives: the chain rule's located key.
    let mixture: Rat = apart
        .iter()
        .map(|family| family.likelihood.clone() / rational(3, 1))
        .sum();
    assert_eq!(product, mixture);
    assert_eq!(composed.posterior(), vec![(1, Rat::one())]);
    // code = log₂ 3 (the keystone's key) + 4 bits (four uniform phases under the located key).
    let code = composed
        .likelihood()
        .code()
        .expect("a code")
        .expect("alive");
    encloses(&code, &log2_of(3).plus(&log2_of(16)));
}

/// A reader emitting the phase, keyed through a ring.
struct Phase(usize);

impl PortReader for Phase {
    fn label(&self) -> String {
        "phase".to_string()
    }
    fn alphabet(&self) -> usize {
        self.0
    }
    fn emit(&self, port: Port) -> usize {
        port.phase as usize
    }
    fn declaration(&self) -> Declaration {
        Declaration::new("phase", vec![self.0 as u64])
    }
}

#[test]
fn a_reader_keyed_through_a_keystone_is_survivor_filtering_and_unheld_it_reads_the_prior() {
    let ring: Arc<dyn Keystone> = Arc::new(Ring(5));
    let reader: Arc<dyn PortReader> = Arc::new(Phase(5));
    let emitters =
        PortedEmitters::new(Arc::clone(&ring), Arc::clone(&reader), PortPath::tick()).unwrap();
    let factor = Survivors::new(Box::new(emitters.clone()), 5, "none").unwrap();
    let mut family = KeyFamily::new("ring ⊳ phase".to_string(), 0, vec![factor]).unwrap();
    let mut unheld = Unheld::new("unheld".to_string(), 0, emitters);
    // Key 3 made the passage: phases 3, 4, 0, 1, …
    let cells: Vec<usize> = (0..12).map(|t| (3 + t) % 5).collect();
    for (t, &cell) in cells.iter().enumerate() {
        let located = family.receive(cell).unwrap();
        let prior = unheld.receive(cell).unwrap();
        assert_eq!(
            prior,
            rational(1, 5),
            "an unheld port reads the prior at every tick"
        );
        assert_eq!(located, if t == 0 { rational(1, 5) } else { Rat::one() });
    }
    assert_eq!(family.likelihood(), Likelihood::Exact(rational(1, 5)));
    let code = unheld.likelihood().code().unwrap().unwrap();
    encloses(
        &code,
        &log2_of(5).scaled(&Rat::from_integer(BigInt::from(12))),
    );
}

#[test]
fn the_sieve_reads_the_cheap_faces_then_the_gratings_and_agrees_with_primality() {
    for (base, digits) in [(10, 4), (6, 6), (2, 10), (16, 3)] {
        let window = PrimeWindow {
            base,
            start: 0,
            end: 100,
            digits,
            trailing: 1,
            order: DigitOrder::MostFirst,
            emission: PrimeEmission::Digits,
        };
        let sieve = Sieve::of(&window, 1 << 20).expect("a sieve");
        let range = base.pow(digits as u32);
        for n in 0..range {
            let (prime, face) = sieve.verdict(n);
            assert_eq!(prime, is_prime(n), "base {base}: {n}");
            match face {
                SieveFace::Unit => assert!(n < 2),
                SieveFace::Gap => assert!(prime),
                SieveFace::LastDigit(p)
                | SieveFace::DigitSum(p)
                | SieveFace::Alternating(p)
                | SieveFace::Grating(p) => assert_eq!(n % p, 0, "base {base}: {p} ∤ {n}"),
            }
        }
    }
}

#[test]
fn the_carry_egg_locates_the_clock_and_pays_the_operands_entropy_exactly() {
    for (base, order) in [
        (10, DigitOrder::LeastFirst),
        (10, DigitOrder::MostFirst),
        (2, DigitOrder::LeastFirst),
    ] {
        let family = ProductFamily {
            base,
            digits: 2,
            face: 1,
            order,
        };
        let records = 32usize;
        let products = Products::draw(&family, records, &mut Draw::new(7)).expect("products");
        let cells = products.emit();
        let classes = products.classes();
        let mut composed = Composed::products(&family, 1).expect("clock ⊳ carry");
        for (t, (&cell, class)) in cells.iter().zip(&classes).enumerate() {
            let face = composed.face().expect("its face");
            assert_eq!(face.iter().sum::<Rat>(), Rat::one());
            let received = composed.receive(cell).expect("the cell");
            if t >= family.record_length() {
                let expected = match class {
                    ProductCell::Operand => rational(1, base as i64),
                    _ => Rat::one(),
                };
                assert_eq!(received, expected, "cell {t}, {class:?}");
            }
        }
        assert_eq!(composed.posterior(), vec![(0, Rat::one())]);
        // code = log₂ (4L + 3) + records · 2L log₂ b, the key and the operands' entropy.
        let truth = log2_of(family.record_length() as i64)
            .plus(&log2_of(base as i64).scaled(&Rat::from_integer(BigInt::from(records * 4))));
        let code = composed.likelihood().code().unwrap().unwrap();
        encloses(&code, &truth);
    }
}

#[test]
fn the_counter_and_sieve_locate_the_start_under_the_clock() {
    for (base, digits, start, end) in [
        (10u64, 3usize, 0u64, 1000u64),
        (10, 3, 137, 900),
        (6, 4, 0, 1296),
    ] {
        let window = PrimeWindow {
            base,
            start,
            end,
            digits,
            trailing: 1,
            order: DigitOrder::MostFirst,
            emission: PrimeEmission::Digits,
        };
        let cells = window.emit().expect("cells");
        let mut composed = Composed::primes(&window, 1 << 20, 1).expect("clock ⊳ counter ⊳ sieve");
        for &cell in &cells {
            let face = composed.face().expect("its face");
            assert_eq!(face.iter().sum::<Rat>(), Rat::one());
            assert!(!composed.receive(cell).expect("the cell").is_zero());
        }
        let Readout::Keys(keys) = composed.readout() else {
            panic!("a key readout");
        };
        assert_eq!(keys.survivors, vec![vec![vec![0]], vec![vec![start]]]);
        // code = log₂ (L + 1) + log₂ b^L: the clock's key and the counter's.
        let truth = log2_of(digits as i64 + 1)
            .plus(&log2_of(base as i64).scaled(&Rat::from_integer(BigInt::from(digits))));
        encloses(&composed.likelihood().code().unwrap().unwrap(), &truth);
    }
}

#[test]
fn the_sieve_at_an_unheld_counter_reads_the_density() {
    let window = PrimeWindow {
        base: 10,
        start: 0,
        end: 1000,
        digits: 3,
        trailing: 1,
        order: DigitOrder::MostFirst,
        emission: PrimeEmission::Digits,
    };
    let cells = window.emit().expect("cells");
    let mut unheld = Composed::primes_unheld_counter(&window, 1 << 20, 1).expect("the unheld");
    for &cell in &cells {
        assert!(!unheld.receive(cell).unwrap().is_zero());
    }
    // The clock's key, the digits at log₂ 10 each, the primality at the range's density 168/1000.
    let (primes, range) = (168i64, 1000i64);
    let density = |count: i64| {
        SymbolicSurprisal::log2_of_ratio(&rational(range, count))
            .unwrap()
            .scaled(&Rat::from_integer(BigInt::from(count)))
    };
    let truth = log2_of(4)
        .plus(&log2_of(10).scaled(&Rat::from_integer(BigInt::from(3000))))
        .plus(&density(primes))
        .plus(&density(range - primes));
    encloses(&unheld.likelihood().code().unwrap().unwrap(), &truth);
}

fn tree(alphabet: usize, depth: usize, population: usize) -> Box<dyn Family> {
    Box::new(
        TreeFamily::new(
            LandmarkDeclaration {
                alphabet,
                depth,
                forced: 0,
                population: population as u64,
                grain: 16,
                family: LetterFamily::cells(),
                prior: StopPrior::half(),
                capacity: Capacity::Unbounded,
            },
            1,
        )
        .expect("a tree"),
    )
}

#[test]
fn the_partition_reads_the_passage_code_whole_and_selects_the_composed_egg() {
    let family = ProductFamily {
        base: 10,
        digits: 2,
        face: 1,
        order: DigitOrder::LeastFirst,
    };
    let products = Products::draw(&family, 64, &mut Draw::new(11)).expect("products");
    let cells = products.emit();
    let parts: Vec<usize> = products
        .classes()
        .iter()
        .map(|class| *class as usize)
        .collect();
    let mut population = Population::new(vec![
        tree(family.alphabet(), 2, cells.len()),
        Box::new(Composed::products(&family, 1).unwrap()),
    ])
    .unwrap();
    let (_, readings) = population.receive_partitioned(&cells, &parts, 5).unwrap();
    let receipt = population.receipt().unwrap();
    assert_eq!(receipt.selected, Some(1));
    let sum = |values: Vec<&ExactInterval>| {
        values
            .into_iter()
            .fold(ExactInterval::point(Rat::zero()), |total, value| {
                ExactInterval::new(&total.lower + &value.lower, &total.upper + &value.upper)
                    .unwrap()
            })
    };
    let slack = Rat::new(BigInt::one(), BigInt::one() << 32);
    let near = |a: &ExactInterval, b: &ExactInterval| {
        let difference = interval_difference(a, b).unwrap();
        assert!(difference.lower <= slack && difference.upper >= -&slack);
    };
    near(
        &sum(readings.iter().map(|part| &part.population).collect()),
        &receipt.code,
    );
    for (index, family) in receipt.families.iter().enumerate() {
        let parts = readings
            .iter()
            .map(|part| part.families[index].as_ref().expect("alive"))
            .collect();
        near(&sum(parts), family.code.as_ref().expect("alive"));
    }
    assert_eq!(
        readings.iter().map(|part| part.cells).sum::<usize>(),
        cells.len()
    );
    // The composed egg pays nothing on a determined cell once the clock is located (its faces
    // there are exactly one), so its code on the determined classes lies within its code on the
    // first record, where the clock is located.
    let mut first = Composed::products(&family, 1).unwrap();
    for &cell in &cells[..family.record_length()] {
        first.receive(cell).unwrap();
    }
    let bound = first.likelihood().code().unwrap().unwrap();
    let determined = sum([
        ProductCell::Mark,
        ProductCell::Trailing,
        ProductCell::Middle,
        ProductCell::Leading,
    ]
    .iter()
    .map(|class| readings[*class as usize].families[1].as_ref().unwrap())
    .collect());
    assert!(determined.upper <= &bound.upper + &slack);
}
