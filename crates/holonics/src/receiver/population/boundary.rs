//! **The part clock and the boundary egg: where a part ends is predicted by more than its bytes**
//! (campaign 5 on the population; #73, #148; Lean `Compression/Landmark/Context/Composition.
//! {stagedFace_nonneg, stagedFace_sum_one, staged_chain_rule, staged_code}`).
//!
//! [definition; agent-inferred] **The part clock** ([`PartClock`]) is a keystone of one key: the
//! declared section chart's clock, read from the coded past, so it locates nothing and its chain-rule
//! term `log₂ |K| − log₂ #S` is zero. Its port ([`PartPort`]) at the next cell is the open part's
//! section (channel and kind, read once at its letter), its **phase** `p` (the bytes since its
//! section letter), its **carry** `s` (the sentence closes among them: the clock winds by bytes and
//! carries at a sentence close) and the **last byte's class** `ℓ` ([`LastByte`]: none at the part's
//! opening, a line close `\n`, a sentence close `.`, `!` or `?`, a colon, a space, any other byte).
//! A section letter resets it. [agent-inferred, development counts] The byte classes are declared on
//! the exterior chart: on the curated development cells 1426 of the 1477 section letters follow a
//! `.`, and 1439 a sentence close.
//!
//! [definition; agent-inferred] **The hazard law** ([`Hazard`]): the probability that a section
//! letter comes next is a Krichevsky–Trofimov face over `{byte, letter}` per cell of a declared
//! partition of the port (Lean `Tree.{ktFace, ktFace_pos, ktFace_sum}`; `context::baseline::
//! kt_probability`):
//!
//! ```text
//! ⌊n⌋₂ = 0 at n = 0,   1 + ⌊log₂ n⌋ otherwise                        the dyadic class of a count
//! cell(port) = (c, k, ⌊p⌋₂, ⌊s⌋₂)   when ℓ is a sentence close          (channel, kind, phase, carry)
//!            = (c, ℓ)               otherwise                          (channel, last byte's class)
//! h_t(letter) = (2 n₁ + 1)/(2 n + 2),   h_t(byte) = (2 n₀ + 1)/(2 n + 2)
//! ```
//!
//! `n₁` letters and `n₀` bytes read in the cell before `t`, `n = n₀ + n₁`. Before any section is open
//! the chart's pin makes the letter certain (`h = 1` on letters, `0` on bytes: a cut opens at a
//! letter), and nothing is counted.
//!
//! [definition; agent-inferred] **The boundary egg** ([`BoundaryEgg`]) composes the part clock with
//! the byte tree (the typed tree, [`TreeFamily::sectioned`]) and the letter tree (the retired reader's
//! section navigator, now a conditioned egg): at each cell its face factors through the cell's stage
//! `σ(x) ∈ {byte, letter}`,
//!
//! ```text
//! q_t(x) = h_t(σ(x)) · r_t(x),   r_t(b) = q̂_T(b)/q̂_T(byte)   (the byte tree's face within the bytes)
//!                                 r_t(ℓ) = q̂_L(ℓ)              (the letter tree's face of the letter)
//! ```
//!
//! and `q̂_T(byte) = s/2^(M_p)` is the byte tree's root digit: the odometer's first digit splits the
//! bytes from the letters exactly when `B = 2^(⌈log₂|A|⌉ − 1)` (the chart's bytes fill the lower
//! half; `256` of `268`), so `r_t(b)` is the product of the byte's digits below the root. The staged
//! face is a face (Lean `stagedFace_nonneg`, `stagedFace_sum_one`: `h_t` and each stage's `r_t` are
//! faces), and **its code is the hazard's plus the conditioned faces', by the chain rule at every
//! tick** (`staged_chain_rule`, `staged_code`):
//!
//! ```text
//! −log₂ ∏_(t<n) q_t(x_t) = −log₂ ∏_(t<n) h_t(σ(x_t)) − log₂ ∏_(t<n) r_t(x_t)
//! ```
//!
//! The byte tree's own face factors the same way through its root digit, so the part clock's value
//! (the joint code without it against with it, `composition`'s keystone value) is exact: without
//! the clock the egg's port is unheld and the byte tree reads every cell alone ([`BoundaryReadout`]'s
//! unheld codes), `code(tree) − code(egg) = [code(root) − code(h)] + [code(q̂_T(ℓ)/q̂_T(letter)) −
//! code(r_L)]`, the boundary's and the letters' shares.
//!
//! [definition; agent-inferred] **The letter tree** reads the section epochs' clock (one tick a
//! letter, the letters' index `k·C + c`): the address of letter `j` is the preceding `D_L` letters,
//! newest first, each bundled with the part it opened, read at the section that closed it: that
//! part's length as its base-8 digits `⌈log₈(p + 1)⌉` (at most `⌈log₈(n* + 1)⌉`) and its last byte's
//! class. So a letter is predicted from the joint alternation of every port's sections and from how
//! the part it closes ran.
//!
//! [definition] The computational object is the helical pair interaction, read here as eggs joined
//! at a part's port. Of the winding guide's six general objects this owner touches four: the
//! **helix** (the part clock: its phase winds by bytes and carries at a sentence close), **faces and
//! placement** (the port and the staged face), the **tube** (a part's span, and the letters' own
//! clock) and the **tower thread** (the sections restrict the passage; the dyadic classes restrict
//! a count). The pair and the cell holonomy stay attached through the trees' owner.

use std::collections::{BTreeMap, VecDeque};

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::{
    Act, Declaration, Family, Likelihood, PopulationError, Readout, TreeFamily, Work, refuse,
};
use crate::compression::landmark::context::baseline::kt_probability;
use crate::compression::landmark::context::{
    Bundle, LandmarkDeclaration, Landmarks, Letter, LetterFamily, PassageCode, Section,
    SectionChart, odometer_digits,
};
use crate::ratio::Rat;

/// [definition; agent-inferred] **The last byte's class** (module header): the part clock's reading
/// of the byte before the next cell.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum LastByte {
    /// No byte yet in the part (its opening).
    None,
    /// `\n`.
    LineClose,
    /// `.`, `!` or `?`.
    SentenceClose,
    /// `:`.
    Colon,
    /// ` `.
    Space,
    /// Any other byte.
    Other,
}

impl LastByte {
    /// The declared classes, in order.
    pub const CLASSES: usize = 6;

    /// **A byte's class** on the exterior chart (module header).
    pub fn of(byte: usize) -> Self {
        match u8::try_from(byte) {
            Ok(b'\n') => LastByte::LineClose,
            Ok(b'.' | b'!' | b'?') => LastByte::SentenceClose,
            Ok(b':') => LastByte::Colon,
            Ok(b' ') => LastByte::Space,
            _ => LastByte::Other,
        }
    }

    /// The class's index in [`Self::CLASSES`].
    pub fn index(self) -> usize {
        self as usize
    }
}

/// [definition] **The dyadic class of a count**: `0` at zero, `1 + ⌊log₂ n⌋` otherwise.
pub fn dyadic_class(count: u64) -> u32 {
    if count == 0 { 0 } else { 1 + count.ilog2() }
}

/// [definition] **The part clock's port** (module header): the open part's section, its phase (bytes
/// since its letter), its carry (sentence closes among them) and the last byte's class; no section
/// before the cut's first letter.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct PartPort {
    pub section: Option<Section>,
    pub phase: u64,
    pub carry: u64,
    pub last: LastByte,
}

/// [definition; agent-inferred] **The part clock** (module header): a keystone of one key over the
/// declared section chart, read from the coded past.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PartClock {
    chart: SectionChart,
    port: PartPort,
}

impl PartClock {
    /// The clock over a chart, before any section.
    pub fn new(chart: SectionChart) -> Self {
        Self {
            chart,
            port: PartPort {
                section: None,
                phase: 0,
                carry: 0,
                last: LastByte::None,
            },
        }
    }

    /// The chart.
    pub fn chart(&self) -> &SectionChart {
        &self.chart
    }

    /// The port the next cell meets.
    pub fn port(&self) -> PartPort {
        self.port
    }

    /// **Advance by one received cell**: a section letter opens its part (phase, carry and class
    /// reset); a byte winds the phase, carries at a sentence close and sets the last byte's class.
    pub fn advance(&mut self, cell: usize) {
        match self.chart.section(cell) {
            Some(section) => {
                self.port = PartPort {
                    section: Some(section),
                    phase: 0,
                    carry: 0,
                    last: LastByte::None,
                };
            }
            None => {
                let last = LastByte::of(cell);
                self.port.phase += 1;
                if last == LastByte::SentenceClose {
                    self.port.carry += 1;
                }
                self.port.last = last;
            }
        }
    }
}

/// [definition; agent-inferred] **A cell of the hazard's declared partition** (module header).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum HazardCell {
    /// After a sentence close: the channel, the kind, the phase's and the carry's dyadic classes.
    Sentence {
        channel: usize,
        kind: usize,
        phase: u32,
        carry: u32,
    },
    /// Otherwise: the channel and the last byte's class.
    Other { channel: usize, last: LastByte },
}

impl HazardCell {
    /// **The partition's cell of an open part's port** (module header).
    pub fn of(section: Section, port: &PartPort) -> Self {
        if port.last == LastByte::SentenceClose {
            HazardCell::Sentence {
                channel: section.channel,
                kind: section.kind,
                phase: dyadic_class(port.phase),
                carry: dyadic_class(port.carry),
            }
        } else {
            HazardCell::Other {
                channel: section.channel,
                last: port.last,
            }
        }
    }
}

/// [definition; agent-inferred] **The hazard law** (module header): a Krichevsky–Trofimov face over
/// `{byte, letter}` per cell of the declared partition, its counts the only state it keeps.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Hazard {
    counts: BTreeMap<HazardCell, [u64; 2]>,
    deposits: u64,
}

impl Hazard {
    /// The empty law: every cell at `(½, ½)`.
    pub fn new() -> Self {
        Self::default()
    }

    /// **The face at a port**, `[h(byte), h(letter)]`, exact: the KT face of the port's cell, and
    /// before any section the chart's pin `[0, 1]`.
    pub fn face(&self, port: &PartPort) -> [Rat; 2] {
        match port.section {
            None => [Rat::zero(), Rat::one()],
            Some(section) => {
                let counts = self
                    .counts
                    .get(&HazardCell::of(section, port))
                    .copied()
                    .unwrap_or([0, 0]);
                let total = counts[0] + counts[1];
                [
                    kt_probability(counts[0], total, 2),
                    kt_probability(counts[1], total, 2),
                ]
            }
        }
    }

    /// **Count the stage that arrived** in the port's cell (nothing before any section).
    pub fn deposit(&mut self, port: &PartPort, letter: bool) {
        if let Some(section) = port.section {
            self.counts
                .entry(HazardCell::of(section, port))
                .or_insert([0, 0])[usize::from(letter)] += 1;
            self.deposits += 1;
        }
    }

    /// The partition's cells met so far.
    pub fn cells(&self) -> usize {
        self.counts.len()
    }
}

/// [definition; agent-inferred] **The boundary egg's readout** (module header): its code by stage
/// and channel, and the same cells' unheld codes (the byte tree alone, its own root digit and its
/// own letters), each a product of faces enclosed by `PassageCode`. A close is attributed to the
/// channel of the part it closes; the letter that opens the cut closes none (its hazard face is the
/// pin's `1`).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BoundaryReadout {
    /// Per channel: the bytes read on it, and the closes of its parts.
    pub bytes: Vec<u64>,
    pub closes: Vec<u64>,
    /// The hazard's faces: on each channel's bytes (`h(byte)`), at each channel's closes
    /// (`h(letter)`).
    pub hazard_bytes: Vec<PassageCode>,
    pub hazard_closes: Vec<PassageCode>,
    /// The byte tree's faces within the bytes, per channel (`r(b)`).
    pub within_bytes: Vec<PassageCode>,
    /// The letter tree's faces of the letters (`r(ℓ)`).
    pub letters: PassageCode,
    /// Unheld: the byte tree's root digit on each channel's bytes and at each channel's closes.
    pub root_bytes: Vec<PassageCode>,
    pub root_closes: Vec<PassageCode>,
    /// Unheld: the byte tree's faces of the letters within the letters (`q̂_T(ℓ)/q̂_T(letter)`), and
    /// its own face of the cut's opening letter.
    pub tree_letters: PassageCode,
    /// The partition's cells met by the hazard.
    pub hazard_cells: usize,
}

/// [definition; agent-inferred] **The letter tree** on the section epochs' clock (module header):
/// its tree, the letters before the pending one with their parts' bundles, and the pending letter
/// whose part is still open.
struct LetterTree {
    tree: Landmarks,
    family: LetterFamily,
    lengths: u64,
    past: VecDeque<Letter>,
    pending: Option<usize>,
    received: u64,
}

impl LetterTree {
    /// The bundle of the pending letter, its part closed at the port.
    fn closed(&self, letter: usize, port: &PartPort) -> Result<Letter, PopulationError> {
        let length = u64::from(port.phase.checked_ilog2().map_or(0, |log| log / 3 + 1))
            .min(self.lengths - 1);
        Ok(Letter::Bundle(Bundle {
            cell: letter,
            features: self.family.encode(&[length, port.last.index() as u64])?,
        }))
    }

    /// The address of the next letter, the pending one's part closed at the port.
    fn address(&self, port: &PartPort) -> Result<Vec<Letter>, PopulationError> {
        let depth = self.tree.declaration().depth;
        let mut newest = Vec::with_capacity(depth);
        if let Some(letter) = self.pending {
            newest.push(self.closed(letter, port)?);
        }
        let mut address: Vec<Letter> = newest
            .into_iter()
            .chain(self.past.iter().rev().copied())
            .take(depth)
            .collect();
        address.resize(depth, Letter::Boundary);
        Ok(address)
    }

    /// Receive a letter at the port that closes the pending part: its face, then the deposit.
    fn receive(&mut self, letter: usize, port: &PartPort) -> Result<Rat, PopulationError> {
        let address = self.address(port)?;
        let reading = self.tree.receive(&address, letter)?;
        if let Some(pending) = self.pending {
            let closed = self.closed(pending, port)?;
            self.past.push_back(closed);
            if self.past.len() > self.tree.declaration().depth {
                self.past.pop_front();
            }
        }
        self.pending = Some(letter);
        self.received += 1;
        Ok(reading.executed)
    }
}

/// [definition; agent-inferred] **The boundary egg** (module header): the part clock composed with
/// the byte tree and the letter tree through the hazard law.
pub struct BoundaryEgg {
    label: String,
    description: u64,
    chart: SectionChart,
    bytes: TreeFamily,
    clock: PartClock,
    hazard: Hazard,
    letters: LetterTree,
    passage: PassageCode,
    readout: BoundaryReadout,
}

impl BoundaryEgg {
    /// **Compose** the part clock over the byte tree's chart with the byte tree (a typed tree) and
    /// the letter tree declared by `letters` (its alphabet the chart's letters, its letter family
    /// the closed part's length digits and last byte's class, `lengths = ⌈log₈(n* + 1)⌉ + 1`).
    /// Refused unless the byte tree reads a section chart whose bytes fill the lower half of its
    /// odometer (its root digit is the boundary), and unless the letter tree's declaration is the
    /// letters' chart.
    pub fn new(
        label: String,
        description: u64,
        bytes: TreeFamily,
        chart: SectionChart,
        letters: LandmarkDeclaration,
    ) -> Result<Self, PopulationError> {
        let declared = bytes.tree().declaration();
        let digits = odometer_digits(declared.alphabet);
        if declared.alphabet != chart.alphabet()
            || digits == 0
            || chart.bytes() as u64 != 1u64 << (digits - 1)
        {
            return Err(refuse(
                "a boundary egg",
                "its byte tree reads the section chart, whose bytes fill the odometer's lower half",
            ));
        }
        let family = Self::letter_family(declared.population)?;
        let lengths = family.sizes()[0];
        if letters.alphabet != chart.letters() || letters.family != family {
            return Err(refuse(
                "a boundary egg's letter tree",
                "it reads the chart's letters bundled with the closed part's length digits and last byte's class",
            ));
        }
        let channels = chart.channels();
        let empty = vec![PassageCode::new(); channels];
        Ok(Self {
            label,
            description,
            chart,
            bytes,
            clock: PartClock::new(chart),
            hazard: Hazard::new(),
            letters: LetterTree {
                tree: Landmarks::new(letters)?,
                family,
                lengths,
                past: VecDeque::new(),
                pending: None,
                received: 0,
            },
            passage: PassageCode::new(),
            readout: BoundaryReadout {
                bytes: vec![0; channels],
                closes: vec![0; channels],
                hazard_bytes: empty.clone(),
                hazard_closes: empty.clone(),
                within_bytes: empty.clone(),
                letters: PassageCode::new(),
                root_bytes: empty.clone(),
                root_closes: empty,
                tree_letters: PassageCode::new(),
                hazard_cells: 0,
            },
        })
    }

    /// **The letter tree's declared family** at a population `n*` (module header): the closed
    /// part's length as its base-8 digits, `⌈log₈(n* + 1)⌉ + 1` letters (none to every digit a part
    /// within `n*` can hold), and its last byte's class.
    pub fn letter_family(population: u64) -> Result<LetterFamily, PopulationError> {
        let bits = population
            .checked_add(1)
            .and_then(u64::checked_next_power_of_two)
            .map_or(u64::BITS, u64::trailing_zeros);
        let lengths = u64::from(bits.div_ceil(3)) + 1;
        Ok(LetterFamily::new(vec![lengths, LastByte::CLASSES as u64])?)
    }

    /// The byte tree (its own likelihood is the egg's unheld reading).
    pub fn byte_tree(&self) -> &TreeFamily {
        &self.bytes
    }

    /// The part clock.
    pub fn clock(&self) -> &PartClock {
        &self.clock
    }

    /// The readout by stage and channel.
    pub fn stages(&self) -> &BoundaryReadout {
        &self.readout
    }

    /// The byte tree's root digit's side of a stage, `(numerator, M_p)`, from its split.
    fn root_side(&self, split: u64, letter: bool) -> (u64, u64) {
        let face = self.bytes.tree().widths().face;
        if letter {
            ((1u64 << face) - split, face)
        } else {
            (split, face)
        }
    }

    /// **One class's staged face, nothing moved**: `h(σ(x)) · r(x)`, exactly the entry of
    /// [`Family::face`] at `x`, read along one path (the admitted receivers' reading of a located
    /// byte, `admitted`).
    pub fn probability(&self, cell: usize) -> Result<Rat, PopulationError> {
        let alphabet = self.alphabet();
        if cell >= alphabet {
            return Err(PopulationError::CellOutside { cell, alphabet });
        }
        let port = self.clock.port();
        let [byte, letter] = self.hazard.face(&port);
        match self.chart.section(cell) {
            Some(_) => {
                let grain = self.letters.tree.declaration().grain;
                let face = self
                    .letters
                    .tree
                    .face(&self.letters.address(&port)?, grain)?;
                Ok(letter * &face.probabilities[cell - self.chart.bytes()])
            }
            None if byte.is_zero() => Ok(byte),
            None => {
                let digits = self.bytes.score_digits(cell)?;
                let root = digits
                    .digits
                    .iter()
                    .find(|digit| digit.dyadic == 1)
                    .ok_or_else(|| refuse("a boundary egg's byte tree", "its root digit splits"))?;
                let (side, exponent) = self.root_side(root.split, false);
                let root_face = Rat::new(BigInt::from(side), BigInt::one() << exponent as usize);
                Ok(byte * (&digits.reading.executed / &root_face))
            }
        }
    }
}

impl Family for BoundaryEgg {
    fn label(&self) -> String {
        self.label.clone()
    }

    fn alphabet(&self) -> usize {
        self.chart.alphabet()
    }

    fn description(&self) -> u64 {
        self.description
    }

    /// `q(x) = h(σ(x)) r(x)` over the chart, exact.
    fn face(&self) -> Result<Vec<Rat>, PopulationError> {
        let port = self.clock.port();
        let [byte, letter] = self.hazard.face(&port);
        let tree = self.bytes.face()?;
        let within: Rat = tree[..self.chart.bytes()].iter().sum();
        let mut face: Vec<Rat> = tree[..self.chart.bytes()]
            .iter()
            .map(|class| &byte * class / &within)
            .collect();
        let grain = self.letters.tree.declaration().grain;
        let letters = self
            .letters
            .tree
            .face(&self.letters.address(&port)?, grain)?;
        face.extend(letters.probabilities.iter().map(|class| &letter * class));
        Ok(face)
    }

    /// **Receive one cell** (module header): the hazard's face of its stage, the byte tree's face
    /// within the bytes or the letter tree's face of the letter, their product; then every
    /// constituent deposits and the clock advances.
    fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError> {
        let alphabet = self.alphabet();
        if cell >= alphabet {
            return Err(PopulationError::CellOutside { cell, alphabet });
        }
        let port = self.clock.port();
        let section = self.chart.section(cell);
        let letter = section.is_some();
        let [byte_face, letter_face] = self.hazard.face(&port);
        let stage = if letter { letter_face } else { byte_face };
        if stage.is_zero() {
            // A byte before any section: the chart's pin gives it zero, and nothing moves.
            return Ok(stage);
        }
        let digits = self.bytes.receive_digits(cell)?;
        let root = digits
            .digits
            .iter()
            .find(|digit| digit.dyadic == 1)
            .ok_or_else(|| refuse("a boundary egg's byte tree", "its root digit splits"))?;
        let (side, exponent) = self.root_side(root.split, letter);
        let root_face = Rat::new(BigInt::from(side), BigInt::one() << exponent as usize);
        let tree_within = &digits.reading.executed / &root_face;
        let within = if letter {
            let face = self.letters.receive(cell - self.chart.bytes(), &port)?;
            self.readout.letters.face(&face)?;
            match port.section {
                Some(open) => {
                    self.readout.hazard_closes[open.channel].face(&stage)?;
                    self.readout.root_closes[open.channel].side(side, exponent);
                    self.readout.closes[open.channel] += 1;
                    self.readout.tree_letters.face(&tree_within)?;
                }
                // The cut's opening letter: the pin's face is one; the tree's own face is its whole.
                None => self.readout.tree_letters.face(&digits.reading.executed)?,
            }
            face
        } else {
            let open = port.section.ok_or_else(|| {
                refuse("a boundary egg's byte", "a section is open before any byte")
            })?;
            self.readout.hazard_bytes[open.channel].face(&stage)?;
            self.readout.root_bytes[open.channel].side(side, exponent);
            self.readout.within_bytes[open.channel].face(&tree_within)?;
            self.readout.bytes[open.channel] += 1;
            tree_within
        };
        let face = &stage * &within;
        self.passage.face(&face)?;
        self.hazard.deposit(&port, letter);
        self.readout.hazard_cells = self.hazard.cells();
        self.clock.advance(cell);
        Ok(face)
    }

    /// Every constituent admits the passage: the byte tree's (its population and its sections), and
    /// the chart.
    fn admits(&self, cells: &[usize]) -> Result<(), PopulationError> {
        self.bytes.admits(cells)?;
        if self.letters.received + cells.len() as u64 > self.letters.tree.declaration().population {
            return Err(refuse(
                "a boundary egg's passage",
                "its letters stay within the letter tree's declared population",
            ));
        }
        Ok(())
    }

    fn likelihood(&self) -> Likelihood {
        Likelihood::Enclosed(self.passage)
    }

    fn readout(&self) -> Readout<'_> {
        Readout::Boundary(Box::new(self.readout.clone()))
    }

    /// The part clock's chart and the hazard's partition, with the byte tree's and the letter
    /// tree's declarations.
    fn declaration(&self) -> Declaration {
        let letters = self.letters.tree.declaration();
        let mut parameters = vec![
            letters.depth as u64,
            letters.forced as u64,
            letters.grain,
            self.letters.lengths,
        ];
        parameters.extend(letters.prior.rungs().iter().map(|&rung| u64::from(rung)));
        Declaration::new("boundary egg", Vec::new()).with(vec![
            Declaration::new(
                "part clock",
                vec![
                    self.chart.bytes() as u64,
                    self.chart.channels() as u64,
                    self.chart.kinds() as u64,
                    LastByte::CLASSES as u64,
                ],
            ),
            self.bytes.declaration(),
            Declaration::new("letter tree", parameters),
        ])
    }

    /// The byte tree's deposits and nodes, the letter tree's, and the hazard's counts.
    fn work(&self) -> Work {
        let mut work = self.bytes.work();
        work.add(Act::Deposit, self.letters.received);
        work.add(Act::Node, self.letters.tree.nodes() as u64);
        work.add(Act::Count, self.hazard.deposits);
        work
    }
}

#[cfg(test)]
#[path = "boundary_tests.rs"]
mod tests;
