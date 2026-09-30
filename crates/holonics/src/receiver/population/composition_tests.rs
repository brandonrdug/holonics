//! Composition at ports checked exactly on small fixtures: the composed face is a face and its
//! product telescopes to the keystone's prior mixture (against the conditioned families stepped
//! apart in ℚ), the chain rule along the surviving keys, a reader keyed through a keystone against
//! brute force, the reader at an unheld port, and eggs of the machine's own kind composed at ports
//! (the arithmetic eggs that were these fixtures are retired as catered machinery, history at
//! `1b374d46`): a moiré's grating read at its port as its sheet, the first ring of a sheet tuple
//! as the keystone of the rest (the chain rule against the factorized grating family), a ring
//! stepped by a clock's carry (a nested composition locating both keys), and the stepped ring at an
//! unheld port (the keystone's value). The partition's reading (read by a tree beside the composed
//! egg) was retired with the byte-tree text line on September 30 (history at `f5fd8f3b`).

use std::sync::Arc;

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::composition::{
    Composed, Conditioned, Keystone, Port, PortPath, PortReader, PortedEmitters, Unheld,
};
use super::*;
use crate::compression::landmark::context::ratio_code_length;
use crate::holarchy::terrain::{Draw, Grating, Moire, MoireClass, MoireFamily};
use crate::ratio::algebraic::{ExactInterval, interval_difference};
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
    fn readout(&self) -> Readout {
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

// -------------------------------------------------------------------------------------------
// eggs of the machine's own kind: a moiré's rings as keystones and readers

/// `gcd(a, b)` of two machine words.
fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// Whether two enclosures lie within `2^(−32)` of each other.
fn near(a: &ExactInterval, b: &ExactInterval) {
    let slack = Rat::new(BigInt::one(), BigInt::one() << 32);
    let difference = interval_difference(a, b).expect("an enclosed difference");
    assert!(
        difference.lower <= slack && difference.upper >= -&slack,
        "[{}, {}] against [{}, {}]",
        a.lower,
        a.upper,
        b.lower,
        b.upper
    );
}

/// [definition; agent-inferred] **A moiré's ring as a keystone**: the declared family's gratings,
/// key `g` its `g`-th grating `(p, q, c)` (`MoireFamily::grating`), a rotor ring keyed at its port.
/// At the upstream port's winding `w` the ring stands at `c + w p`: its port reads the phase
/// `(c + w p) mod q` at the family's common grain `L = lcm(2, …, Q)` (the phase
/// `((c + w p) mod q) · L/q` of `L`, so a reader needs no key) and the winding `⌊(c + w p)/q⌋`, the
/// turns the ring has completed (the carry it passes up). Its coordinates are the grating's
/// `(p, q, c)`, as `GratingSheet` lays them out.
pub(super) struct GratingRing {
    gratings: Vec<Grating>,
    grain: u64,
    denominator: u64,
}

impl GratingRing {
    pub(super) fn new(family: &MoireFamily) -> Self {
        let gratings = (0..family.gratings())
            .map(|index| family.grating(index).expect("a grating of the family"))
            .collect();
        let grain = (2..=family.denominator).fold(1, |grain, q| grain / gcd(grain, q) * q);
        Self {
            gratings,
            grain,
            denominator: family.denominator,
        }
    }

    /// `L = lcm(2, …, Q)`.
    pub(super) fn grain(&self) -> u64 {
        self.grain
    }
}

impl Keystone for GratingRing {
    fn label(&self) -> String {
        format!("grating ring, q ≤ {}", self.denominator)
    }
    fn keys(&self) -> u64 {
        self.gratings.len() as u64
    }
    fn port(&self, key: u64, upstream: Port) -> Port {
        let grating = &self.gratings[key as usize];
        let q = grating.denominator();
        let position = grating.phase() + upstream.winding * grating.numerator();
        Port {
            phase: (position % q) * (self.grain / q),
            winding: position / q,
        }
    }
    fn coordinates(&self, key: u64) -> Vec<u64> {
        let grating = &self.gratings[key as usize];
        vec![grating.numerator(), grating.denominator(), grating.phase()]
    }
    fn declaration(&self) -> Declaration {
        Declaration::new("grating ring", vec![self.denominator])
    }
}

/// [definition] **A ring's half-turn sheet read at its port**: `[2 · phase ≥ L]` at the common
/// grain `L`, which is the grating's own sheet `[2 · port ≥ q]` (`Grating::sheet`).
pub(super) struct Sheet(pub(super) u64);

impl PortReader for Sheet {
    fn label(&self) -> String {
        "half-turn sheet".to_string()
    }
    fn alphabet(&self) -> usize {
        2
    }
    fn emit(&self, port: Port) -> usize {
        usize::from(2 * port.phase >= self.0)
    }
    fn declaration(&self) -> Declaration {
        Declaration::new("half-turn sheet", vec![self.0])
    }
}

/// A keystone of one key passing its port through.
pub(super) struct Pass;

impl Keystone for Pass {
    fn label(&self) -> String {
        "pass".to_string()
    }
    fn keys(&self) -> u64 {
        1
    }
    fn port(&self, _key: u64, upstream: Port) -> Port {
        upstream
    }
    fn coordinates(&self, key: u64) -> Vec<u64> {
        vec![key]
    }
    fn declaration(&self) -> Declaration {
        Declaration::new("pass", Vec::new())
    }
}

/// The seed of the drawn moirés (the release checks' seed).
pub(super) const SEED: u64 = 20_260_927;

/// The declared sheet tuple: two rings over `ℤ/q`, `q ≤ 5`, `N_5 = 36 = 2²·3²` gratings a ring.
pub(super) fn two_rings() -> MoireFamily {
    MoireFamily {
        rings: 2,
        denominator: 5,
    }
}

/// One ring over `ℤ/q`, `q ≤ 5`: the ring a clock steps.
pub(super) fn one_ring() -> MoireFamily {
    MoireFamily {
        rings: 1,
        denominator: 5,
    }
}

/// The drawn sheet tuple of [`two_rings`].
pub(super) fn drawn_sheets() -> Moire {
    Moire::draw(&two_rings(), MoireClass::Sheets, &mut Draw::new(SEED)).expect("a drawn moiré")
}

/// [proved-derived] **The horizon past which a ring's survivors are its species**: two sheet
/// words of periods `q` and `q′` agree at every tick exactly when they agree over `lcm(q, q′)`
/// consecutive ticks, so past `max lcm(q, q′)` ticks (`20 = 2²·5` for `q, q′ ≤ 5`) every surviving
/// grating emits the drawn ring's word forever.
pub(super) fn horizon(family: &MoireFamily) -> usize {
    let top = family.denominator;
    (2..=top)
        .flat_map(|a| (2..=top).map(move |b| a / gcd(a, b) * b))
        .max()
        .expect("a denominator of at least 2") as usize
}

/// **A ring's survivors by brute force**: the family's gratings whose sheet is bit `ring` of every
/// cell, ascending.
pub(super) fn ring_survivors(family: &MoireFamily, cells: &[usize], ring: usize) -> Vec<u64> {
    (0..family.gratings())
        .filter(|&index| {
            let grating = family.grating(index).expect("a grating of the family");
            cells
                .iter()
                .enumerate()
                .all(|(t, &cell)| usize::from(grating.sheet(t as u64)) == (cell >> ring) & 1)
        })
        .collect()
}

/// A grating's index in its family's order.
pub(super) fn index_of(family: &MoireFamily, grating: &Grating) -> u64 {
    let coordinates = |g: &Grating| (g.numerator(), g.denominator(), g.phase());
    (0..family.gratings())
        .find(|&index| {
            coordinates(&family.grating(index).expect("a grating of the family"))
                == coordinates(grating)
        })
        .expect("a grating of the family")
}

/// **The sheet tuple composed at its first ring** (`ring 0 ⊳ (its sheet, the other rings)`): ring
/// 0's gratings as the keystone ([`GratingRing`] on the passage's clock), and under each key the key
/// family reading bit 0 as that ring's sheet at its port (one key, [`Pass`] ⊳ [`Sheet`]) and each
/// other bit `i` by ring `i`'s gratings (`GratingSheet`), the cell the tuple of the factors'
/// classes, bit 0 least significant. Returns the keystone and the conditioned family's declaration,
/// so a key's conditioned family can be stepped apart.
pub(super) fn sheet_tuple(family: &MoireFamily) -> (Arc<dyn Keystone>, Conditioned) {
    let ring = GratingRing::new(family);
    let grain = ring.grain();
    let declared = family.clone();
    let conditioned: Conditioned = Arc::new(move |path| {
        let own = PortedEmitters::new(Arc::new(Pass), Arc::new(Sheet(grain)), path)?;
        let mut factors = vec![Survivors::new(Box::new(own), 1, "none")?];
        for _ in 1..declared.rings {
            let others = GratingSheet::new(&declared)?;
            let keys = others.keys();
            factors.push(Survivors::new(Box::new(others), keys, "none")?);
        }
        Ok(Box::new(KeyFamily::new(
            "ring 0's sheet at its port, the other rings' gratings".to_string(),
            0,
            factors,
        )?) as Box<dyn Family>)
    });
    (Arc::new(ring), conditioned)
}

/// [`sheet_tuple`] composed, named by `description` bits.
pub(super) fn sheet_tuple_egg(family: &MoireFamily, description: u64) -> Composed {
    let (ring, conditioned) = sheet_tuple(family);
    let keys = ring.keys();
    Composed::new(
        format!(
            "ring 0 ⊳ sheet tuple, k = {}, q ≤ {}",
            family.rings, family.denominator
        ),
        description,
        ring,
        &PortPath::tick(),
        &conditioned,
        keys,
    )
    .expect("the composed sheet tuple")
}

/// The declared stepped ring: rate `2/5` at phase `1/5`, stepped by a clock of three phases at
/// offset 2.
pub(super) fn stepped_truth() -> (Grating, u64, u64) {
    (Grating::new(2, 5, 1).expect("a grating"), 2, 3)
}

/// **A ring stepped by a clock's carry**, the terrain's truth read by `Grating::sheet`: the ring's
/// sheet at the clock's windings, `x_t = s(⌊(o + t)/R⌋)`.
pub(super) fn stepped_cells(
    grating: &Grating,
    offset: u64,
    period: u64,
    cells: usize,
) -> Vec<usize> {
    (0..cells as u64)
        .map(|t| usize::from(grating.sheet((offset + t) / period)))
        .collect()
}

/// **`clock ⊳ (grating ring ⊳ sheet)`**: the clock's offsets ([`Ring`]) as the keystone, and under
/// each the ring's gratings as a key family reading the sheet at the ring's port, which turns once
/// each time the clock completes a turn (an odometer's two wheels, a rotor machine's stepping).
pub(super) fn stepped_egg(family: &MoireFamily, period: u64, description: u64) -> Composed {
    let ring = GratingRing::new(family);
    let sheet: Arc<dyn PortReader> = Arc::new(Sheet(ring.grain()));
    let ring: Arc<dyn Keystone> = Arc::new(ring);
    let conditioned: Conditioned = Arc::new(move |path| {
        let emitters = PortedEmitters::new(Arc::clone(&ring), Arc::clone(&sheet), path)?;
        let keys = emitters.keys();
        let factor = Survivors::new(Box::new(emitters), keys, "none")?;
        Ok(Box::new(KeyFamily::new(
            "grating ring ⊳ sheet".to_string(),
            0,
            vec![factor],
        )?) as Box<dyn Family>)
    });
    Composed::new(
        format!("clock of {period} ⊳ (grating ring ⊳ sheet)"),
        description,
        Arc::new(Ring(period)),
        &PortPath::tick(),
        &conditioned,
        period,
    )
    .expect("the stepped ring")
}

/// **`clock ⊳ (unheld grating ring ⊳ sheet)`**: the stepped ring's sheet at the ring's unheld port.
fn stepped_unheld(family: &MoireFamily, period: u64) -> Composed {
    let ring = GratingRing::new(family);
    let sheet: Arc<dyn PortReader> = Arc::new(Sheet(ring.grain()));
    let ring: Arc<dyn Keystone> = Arc::new(ring);
    let conditioned: Conditioned = Arc::new(move |path| {
        let emitters = PortedEmitters::new(Arc::clone(&ring), Arc::clone(&sheet), path)?;
        Ok(Box::new(Unheld::new(
            "unheld grating ring ⊳ sheet".to_string(),
            0,
            emitters,
        )) as Box<dyn Family>)
    });
    Composed::new(
        format!("clock of {period} ⊳ (unheld grating ring ⊳ sheet)"),
        0,
        Arc::new(Ring(period)),
        &PortPath::tick(),
        &conditioned,
        period,
    )
    .expect("the unheld stepped ring")
}

/// A grating ring read at its ports through the sheet is the moiré's own grating: every key emits
/// `GratingSheet`'s class at every tick, with its coordinates, and the common grain of `q ≤ 5` is
/// `60 = 2²·3·5`.
#[test]
fn a_grating_ring_read_at_its_port_is_its_sheet() {
    let family = two_rings();
    let ring = GratingRing::new(&family);
    assert_eq!(ring.grain(), 60);
    let ring: Arc<dyn Keystone> = Arc::new(ring);
    let mut ported =
        PortedEmitters::new(Arc::clone(&ring), Arc::new(Sheet(60)), PortPath::tick()).unwrap();
    let mut sheets = GratingSheet::new(&family).unwrap();
    assert_eq!(ported.keys(), sheets.keys());
    for _ in 0..3 * horizon(&family) {
        for key in 0..sheets.keys() {
            assert_eq!(ported.emit(key), sheets.emit(key));
            assert_eq!(ring.coordinates(key), sheets.coordinates(key));
        }
        ported.advance(0).unwrap();
        sheets.advance(0).unwrap();
    }
}

/// **The sheet tuple composed at its first ring codes by the chain rule** (`chain_rule_of_species`):
/// on the drawn sheet tuple every composed face is a face and the received cell's face; ring 0's
/// keys die where their sheet contradicts bit 0, so its posterior is uniform over its brute-force
/// survivors, which hold the drawn ring and its mirror (`GratingSheet::mirror`); past the horizon
/// every face is one (the keys are located); and the code is the keystone's key less its surviving
/// fibre plus the conditioned family's code under the located species,
/// `2 log₂ 36 − log₂ #S_0 − log₂ #S_1` (here `log₂ 324`, `324 = 2²·3⁴`: each ring's species is its
/// grating and its mirror), the factorized grating family's code on the same cells.
#[test]
fn the_sheet_tuple_composed_at_its_first_ring_codes_by_the_chain_rule() {
    let family = two_rings();
    let moire = drawn_sheets();
    let reach = horizon(&family);
    let cells = moire.emit(3 * reach);
    let mut composed = sheet_tuple_egg(&family, 1);
    for (t, &cell) in cells.iter().enumerate() {
        let face = composed.face().expect("its face");
        assert_eq!(
            face.iter().sum::<Rat>(),
            Rat::one(),
            "the composed face sums to one"
        );
        assert!(face.iter().all(|class| *class >= Rat::zero()));
        let received = composed.receive(cell).expect("the cell");
        assert_eq!(received, face[cell]);
        assert!(!received.is_zero());
        if t >= reach {
            assert_eq!(received, Rat::one(), "tick {t}: past the horizon");
        }
    }
    let first = ring_survivors(&family, &cells, 0);
    let second = ring_survivors(&family, &cells, 1);
    for (ring, survivors) in [&first, &second].into_iter().enumerate() {
        let drawn = &moire.gratings()[ring];
        let mirror = GratingSheet::mirror(drawn).unwrap();
        assert!(survivors.contains(&index_of(&family, drawn)));
        assert!(survivors.contains(&index_of(&family, &mirror)));
    }
    assert_eq!(
        (first.len(), second.len()),
        (2, 2),
        "each ring and its mirror"
    );
    let share = Rat::new(BigInt::one(), BigInt::from(first.len()));
    assert_eq!(
        composed.posterior(),
        first
            .iter()
            .map(|&key| (key, share.clone()))
            .collect::<Vec<_>>()
    );
    let (keys, fibre) = (
        family.gratings() as i64,
        (first.len() * second.len()) as i64,
    );
    let truth = SymbolicSurprisal::log2_of_ratio(&rational(keys * keys, fibre)).unwrap();
    let code = composed
        .likelihood()
        .code()
        .expect("a code")
        .expect("alive");
    encloses(&code, &truth);
    let mut factorized = KeyFamily::gratings(&family, MoireClass::Sheets, 1 << 16, 1).unwrap();
    for &cell in &cells {
        factorized.receive(cell).unwrap();
    }
    assert_eq!(
        factorized.likelihood(),
        Likelihood::Exact(rational(fibre, keys * keys))
    );
}

/// **Nested composition locates both keys** (`clock ⊳ (grating ring ⊳ sheet)`): the stepped ring's
/// cells locate the clock's offset (the sheet can turn only where the clock completes a turn) and
/// the ring's species; the readout is the keystone's located key, then the conditioned family's
/// located keys; and the code is the joint key space's survivor code by the chain rule,
/// `log₂ 3 + log₂ 36 − log₂ #S`, every survivor counted by brute force over the joint key space.
#[test]
fn a_ring_stepped_by_a_clock_locates_the_offset_and_the_ring() {
    let family = one_ring();
    let (truth, offset, period) = stepped_truth();
    let cells = stepped_cells(
        &truth,
        offset,
        period,
        2 * period as usize * horizon(&family),
    );
    let mut composed = stepped_egg(&family, period, 1);
    for &cell in &cells {
        let face = composed.face().expect("its face");
        assert_eq!(face.iter().sum::<Rat>(), Rat::one());
        assert!(!composed.receive(cell).expect("the cell").is_zero());
    }
    let gratings = family.gratings();
    let joint: Vec<(u64, u64)> = (0..period)
        .flat_map(|o| (0..gratings).map(move |g| (o, g)))
        .filter(|&(o, g)| {
            let grating = family.grating(g).expect("a grating");
            stepped_cells(&grating, o, period, cells.len()) == cells
        })
        .collect();
    assert!(joint.iter().all(|&(o, _)| o == offset), "the offset");
    let ring = GratingRing::new(&family);
    let located: Vec<Vec<u64>> = joint.iter().map(|&(_, g)| ring.coordinates(g)).collect();
    let mirror = GratingSheet::mirror(&truth).unwrap();
    assert!(located.contains(&vec![2, 5, 1]));
    assert!(located.contains(&vec![
        mirror.numerator(),
        mirror.denominator(),
        mirror.phase()
    ]));
    let Readout::Keys(keys) = composed.readout();
    assert_eq!(keys.survivors, vec![vec![vec![offset]], located]);
    let truth =
        SymbolicSurprisal::log2_of_ratio(&rational((period * gratings) as i64, joint.len() as i64))
            .unwrap();
    encloses(&composed.likelihood().code().unwrap().unwrap(), &truth);
}

/// **The stepped ring at an unheld port reads the gratings' prior** (a keystone's value): each tick
/// the sheet meets `#{g : s_g(⌊(o + t)/R⌋) = x_t}/36` under each clock offset `o`, never filtered;
/// both sheets are emitted at every step, so no offset dies, and the code is exactly
/// `−log₂ ((1/3) Σ_o ∏_t #{…}/36)`. The ring's value, the code without it against with it, is
/// positive, decided.
#[test]
fn the_stepped_ring_at_an_unheld_port_reads_the_gratings_prior() {
    let family = one_ring();
    let (truth, offset, period) = stepped_truth();
    let cells = stepped_cells(
        &truth,
        offset,
        period,
        2 * period as usize * horizon(&family),
    );
    let mut unheld = stepped_unheld(&family, period);
    for &cell in &cells {
        let face = unheld.face().expect("its face");
        assert_eq!(face.iter().sum::<Rat>(), Rat::one());
        assert!(!unheld.receive(cell).unwrap().is_zero());
    }
    assert_eq!(unheld.posterior().len() as u64, period, "no offset dies");
    let gratings: Vec<Grating> = (0..family.gratings())
        .map(|index| family.grating(index).unwrap())
        .collect();
    let keys = BigInt::from(gratings.len());
    let mixture: Rat = (0..period)
        .map(|o| {
            cells
                .iter()
                .enumerate()
                .map(|(t, &cell)| {
                    let step = (o + t as u64) / period;
                    let count = gratings
                        .iter()
                        .filter(|grating| usize::from(grating.sheet(step)) == cell)
                        .count();
                    Rat::new(BigInt::from(count), keys.clone())
                })
                .product::<Rat>()
        })
        .sum::<Rat>()
        * Rat::new(BigInt::one(), BigInt::from(period));
    let truth_code: ExactInterval =
        ratio_code_length(mixture.numer().magnitude(), mixture.denom().magnitude()).unwrap();
    let code = unheld.likelihood().code().unwrap().unwrap();
    near(&code, &truth_code);
    let mut held = stepped_egg(&family, period, 1);
    for &cell in &cells {
        held.receive(cell).unwrap();
    }
    let held = held.likelihood().code().unwrap().unwrap();
    assert!(held.upper < code.lower, "the ring's value is positive");
}
