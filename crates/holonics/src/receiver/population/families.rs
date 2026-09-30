//! **The declared navigator families a population weighs** (the module header of
//! `receiver::population`): the key families whose key spaces are the terrain's own declarations
//! (the receiving tree read as a family, over the cells or a curated stream's typed ticks, was
//! retired September 30 with the byte-tree text line; history at `f5fd8f3b`): a moiré's gratings
//! (`holarchy::terrain::MoireFamily`, each grating a rotor ring `navigator::Navigator::rotor`
//! emitting its half-turn sheet exactly as the terrain does) and a rotor crib's key, plugboard and
//! start (the field's ring as a reflector machine behind a plugboard, as
//! `holarchy::terrain::rotor_crib` produces it).
//!
//! [definition; agent-inferred] **The key families' layouts.**
//! - [`GratingSheet`]: one ring's key space, the family's `N_Q = Σ_(q=2)^Q q·φ(q)` gratings in the
//!   terrain's order `(q, p, c)` ascending (`MoireFamily::grating`); a key's coordinates are
//!   `(p, q, c)`, and it emits its sheet `[2((c + t p) mod q) ≥ q]`, read through its rotor over one
//!   cycle of `q` ticks (the ring returns to its port exactly at the multiples of `q`).
//!   [proved-derived] **A sheet cannot tell a ring from its mirror** ([`GratingSheet::mirror`]):
//!   the Swing of `ℤ/q` about the centre of the upper sheet arc `{m, …, q − 1}`, `m = ⌈q/2⌉`,
//!   `x ↦ m + q − 1 − x`, maps the arc onto itself and the port `c + tp` onto `c′ + t(q − p)`,
//!   `c′ = m + q − 1 − c mod q`; so `(p, q, c)` and `(q − p, q, c′)` emit one sheet word, and one
//!   ring's survivors keep that pair (the grating itself when `q = 2`).
//! - [`GratingParity`]: the joint key space of `k` rings, `N_Q^k` keys, ring `i` the `i`-th digit
//!   of the key in base `N_Q` (least significant first); it emits the parity color `Σ_i s_i mod 2`;
//!   coordinates `(p_0, q_0, c_0, p_1, …)`. [proved-derived; measured] **The parity class locates
//!   its word, neither the rates nor the rings.** Its survivors are every key emitting the same
//!   parity word, one species of the face map's quotient over generators, and that species is wider
//!   than a gauge orbit: the rings' permutations, each ring's mirror (below), the half-turn of a
//!   rate `p ↦ p + q/2` on an even `q` (it flips the sheet on the odd ticks, so two such rings
//!   cancel their flips), and coincidences across denominators. On the notebook's drawn moiré
//!   (`5/7 @ 0/7`, `3/8 @ 6/8`, `7/8 @ 6/8`) the `720 = 2⁴·3²·5` survivors split by denominators as
//!   `(7, 8, 8)` 384, `(3, 6, 7)` 144, `(2, 7, 7)` 96 and `(4, 4, 7)` 96: 336 of them hold no
//!   period-8 pair and 384 no `5/7` ring (for example `1/2 @ 1/2`, `1/7 @ 3/7`, `1/7 @ 5/7`); the test
//!   `the_parity_fibre_is_one_word_not_one_rate` counts them against a brute force.
//! - The sheet tuple's key space factorizes per ring (`KeyFamily::gratings`): one [`GratingSheet`]
//!   factor a ring, the cell's bit `i` read by factor `i`.
//! - [`RotorKeys`]: the start port, the key and the plugboard of ring `g`'s machine, `d · d · d!`
//!   keys for a ring of `d` ports, the plugboard least significant in the lexicographic order of
//!   `S_d`; coordinates `(start, key, S(0), …, S(d − 1))`. It emits `x_0 = start` and
//!   `x_(k+1) = S⁻¹ W_(key + T_k) S x_k`, `T_k` ring `g`'s ticks on the cells before `k` under the
//!   declared configurations (the field's selective law), exactly `rotor_crib`'s law. Its survivors
//!   keep the ring's rotor gauge (`(key + t, S − t)`, Lean `HNN/Keys.rotorGauge`).
//!
//! [definition; agent-inferred] **A declared enumeration.** Survivor filtering touches every key
//! once at the first cell, so each key family is declared with the largest key space it enumerates;
//! past it the family is refused with the Bombe that owns the larger space ([`MOIRE_BOMBE`], owed;
//! [`ROTOR_BOMBE`], built).

use num_bigint::{BigInt, BigUint};
use num_traits::ToPrimitive;

use super::dormancy::{Dormancy, DormantFamily, Layered};
use super::{AdmittedFuture, Declaration, Emitters, KeyFamily, PopulationError, Survivors, refuse};
use crate::hnn::field::Field;
use crate::holarchy::terrain::{Grating, MoireClass, MoireFamily};

/// **The Bombe a moiré's joint key space is owed to**: its phases located by loop closure over a
/// menu of parity relations on the joint clock torus (the audit record's §6.3).
pub const MOIRE_BOMBE: &str = "parity-constraint propagation on the joint clock torus, one parity relation a tick over at most Π q_i phase configurations once the rates are known; owed";

/// **The built Bombe of a rotor crib**: pairwise loop closure over the crib's menu.
pub const ROTOR_BOMBE: &str =
    "hnn::keys::locate_ring, pairwise loop closure over the crib's menu; built";

// -------------------------------------------------------------------------------------------
// the moiré's gratings

/// [definition] **One ring's key space** (module header): the declared family's gratings, each
/// emitting its half-turn sheet.
#[derive(Clone)]
pub struct GratingSheet {
    gratings: Vec<Grating>,
    words: Vec<Vec<bool>>,
    tick: u64,
    denominator: u64,
}

impl GratingSheet {
    /// The family's gratings, each with its sheets over one cycle read through its rotor.
    pub fn new(family: &MoireFamily) -> Result<Self, PopulationError> {
        let gratings = (0..family.gratings())
            .map(|index| family.grating(index))
            .collect::<Result<Vec<Grating>, _>>()?;
        let words = gratings
            .iter()
            .map(|grating| {
                (0..grating.denominator())
                    .map(|t| grating.sheet(t))
                    .collect()
            })
            .collect();
        Ok(Self {
            gratings,
            words,
            tick: 0,
            denominator: family.denominator,
        })
    }

    /// The gratings, in the family's order.
    pub fn gratings(&self) -> &[Grating] {
        &self.gratings
    }

    /// **A grating's mirror** (module header): `(q − p, q, ⌈q/2⌉ + q − 1 − c mod q)`, its Swing
    /// about the centre of its upper sheet arc, which emits the same sheet at every tick.
    pub fn mirror(grating: &Grating) -> Result<Grating, PopulationError> {
        let (p, q, c) = (grating.numerator(), grating.denominator(), grating.phase());
        let arc = q.div_ceil(2);
        Ok(Grating::new(q - p, q, (arc + 2 * q - 1 - c) % q)?)
    }

    /// Grating `index`'s sheet at the current tick.
    fn sheet(&self, index: usize) -> bool {
        self.sheet_at(index, self.tick)
    }

    /// Grating `index`'s sheet at tick `tick`: its ring winds without the cells.
    fn sheet_at(&self, index: usize, tick: u64) -> bool {
        let word = &self.words[index];
        word[(tick % word.len() as u64) as usize]
    }

    fn coordinates_of(&self, index: usize) -> [u64; 3] {
        let grating = &self.gratings[index];
        [grating.numerator(), grating.denominator(), grating.phase()]
    }
}

impl Emitters for GratingSheet {
    fn alphabet(&self) -> usize {
        2
    }

    fn keys(&self) -> u64 {
        self.gratings.len() as u64
    }

    fn emit(&self, key: u64) -> usize {
        usize::from(self.sheet(key as usize))
    }

    fn advance(&mut self, _cell: usize) -> Result<(), PopulationError> {
        self.tick += 1;
        Ok(())
    }

    fn coordinates(&self, key: u64) -> Vec<u64> {
        self.coordinates_of(key as usize).to_vec()
    }

    fn fork_at(&self, tick: u64) -> Option<Box<dyn Emitters>> {
        let mut fork = self.clone();
        fork.tick = tick;
        Some(Box::new(fork))
    }

    fn declaration(&self) -> Declaration {
        Declaration::new("grating sheet", vec![self.denominator])
    }

    fn ahead(&self, key: u64, ticks: u64) -> Option<usize> {
        Some(usize::from(self.sheet_at(key as usize, self.tick + ticks)))
    }

    /// A ring of denominator `q` returns to its port every `q` ticks.
    fn period(&self, key: u64) -> Option<u64> {
        Some(self.words[key as usize].len() as u64)
    }
}

/// One ring is one layer: its sheet sounds when active and reads `0` when dormant.
impl Layered for GratingSheet {
    fn layers(&self) -> usize {
        1
    }

    fn sounding(&self, key: u64) -> usize {
        usize::from(self.sheet(key as usize))
    }

    fn class(&self, sounding: usize, active: usize) -> usize {
        sounding & active & 1
    }

    fn wind(&mut self, ticks: u64) {
        self.tick += ticks;
    }
}

/// [definition] **The parity color's joint key space** (module header): `k` rings over the family's
/// gratings.
#[derive(Clone)]
pub struct GratingParity {
    ring: GratingSheet,
    rings: u32,
    keys: u64,
}

impl GratingParity {
    /// The joint key space `N_Q^k`; refused when it passes a machine word.
    pub fn new(family: &MoireFamily) -> Result<Self, PopulationError> {
        let ring = GratingSheet::new(family)?;
        let rings = u32::try_from(family.rings)
            .map_err(|_| refuse("a parity key space", "its rings fit a machine word"))?;
        let keys = (ring.gratings.len() as u64)
            .checked_pow(rings)
            .ok_or_else(|| refuse("a parity key space", "its keys fit a machine word"))?;
        Ok(Self { ring, rings, keys })
    }

    /// Key `key`'s gratings' indices, ring 0 first.
    fn digits(&self, mut key: u64) -> impl Iterator<Item = usize> {
        let base = self.ring.gratings.len() as u64;
        (0..self.rings).map(move |_| {
            let digit = key % base;
            key /= base;
            digit as usize
        })
    }
}

impl Emitters for GratingParity {
    fn alphabet(&self) -> usize {
        2
    }

    fn keys(&self) -> u64 {
        self.keys
    }

    fn emit(&self, key: u64) -> usize {
        self.digits(key)
            .filter(|&index| self.ring.sheet(index))
            .count()
            % 2
    }

    fn advance(&mut self, cell: usize) -> Result<(), PopulationError> {
        self.ring.advance(cell)
    }

    fn coordinates(&self, key: u64) -> Vec<u64> {
        self.digits(key)
            .flat_map(|index| self.ring.coordinates_of(index))
            .collect()
    }

    fn fork_at(&self, tick: u64) -> Option<Box<dyn Emitters>> {
        let mut fork = self.clone();
        fork.ring.tick = tick;
        Some(Box::new(fork))
    }

    fn declaration(&self) -> Declaration {
        Declaration::new(
            "grating parity",
            vec![u64::from(self.rings), self.ring.denominator],
        )
    }

    fn ahead(&self, key: u64, ticks: u64) -> Option<usize> {
        let tick = self.ring.tick + ticks;
        Some(
            self.digits(key)
                .filter(|&index| self.ring.sheet_at(index, tick))
                .count()
                % 2,
        )
    }

    /// The rings' joint period: the least common multiple of their denominators.
    fn period(&self, key: u64) -> Option<u64> {
        Some(self.digits(key).fold(1u64, |period, index| {
            let q = self.ring.words[index].len() as u64;
            period / gcd(period, q) * q
        }))
    }
}

/// `gcd(a, b)` of two machine words.
fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        (a, b) = (b, a % b);
    }
    a
}

/// Each ring is a layer: the parity of the active rings' sheets.
impl Layered for GratingParity {
    fn layers(&self) -> usize {
        self.rings as usize
    }

    fn sounding(&self, key: u64) -> usize {
        self.digits(key)
            .enumerate()
            .map(|(ring, index)| usize::from(self.ring.sheet(index)) << ring)
            .sum()
    }

    fn class(&self, sounding: usize, active: usize) -> usize {
        ((sounding & active).count_ones() % 2) as usize
    }

    fn wind(&mut self, ticks: u64) {
        self.ring.wind(ticks);
    }
}

// -------------------------------------------------------------------------------------------
// the rotor crib's keys

/// [definition] **A rotor crib's key space** (module header): the start, the key and the plugboard
/// of a declared field's ring, the earlier rings under their declared configurations.
pub struct RotorKeys {
    ports: usize,
    rotor: u64,
    stages: Vec<Vec<usize>>,
    boards: Vec<Vec<usize>>,
    inverses: Vec<Vec<usize>>,
    field: Field,
    ring: usize,
    /// The declared configurations, one per ring of the field: the identity's, never moved.
    configurations: Vec<u64>,
    /// The field's lift, stepped by each cell from the declared configurations.
    lift: Vec<BigInt>,
    taken: u64,
    last: Option<usize>,
}

impl RotorKeys {
    /// `d · d · d!`, the key space of a ring of `d` ports.
    pub fn key_space(ports: usize) -> BigUint {
        let boards: BigUint = (1..=ports).map(BigUint::from).product();
        BigUint::from(ports) * BigUint::from(ports) * boards
    }

    /// The key space of ring `ring` under the declared configurations, its stages read from the
    /// ring's machine and its plugboards enumerated; refused past the declared enumeration.
    pub fn new(
        field: &Field,
        ring: usize,
        configurations: &[u64],
        admitted: u64,
    ) -> Result<Self, PopulationError> {
        let Some(declared) = field.rings().get(ring) else {
            return Err(refuse("a rotor key space", "it names a ring of the field"));
        };
        if configurations.len() != field.rings().len() {
            return Err(refuse(
                "a rotor key space",
                "its configurations name one per ring of the field",
            ));
        }
        let ports = usize::try_from(declared.period()).map_err(|_| {
            refuse(
                "a rotor key space",
                "its ring's ports fit the address space",
            )
        })?;
        let space = Self::key_space(ports);
        if space > BigUint::from(admitted) {
            return Err(PopulationError::Bombe {
                key_space: space,
                admitted: BigUint::from(admitted),
                bombe: ROTOR_BOMBE,
            });
        }
        let machine = declared.machine()?;
        let rotor = machine.period().to_u64().ok_or_else(|| {
            refuse(
                "a rotor key space",
                "its rotor's period fits a machine word",
            )
        })?;
        let stages = (0..rotor)
            .map(|position| {
                let stage = machine.stage(&BigUint::from(position))?;
                (0..ports).map(|port| stage.apply(port)).collect()
            })
            .collect::<Result<Vec<Vec<usize>>, _>>()?;
        let boards = permutations(ports);
        let inverses = boards
            .iter()
            .map(|board| {
                let mut inverse = vec![0; ports];
                for (port, &image) in board.iter().enumerate() {
                    inverse[image] = port;
                }
                inverse
            })
            .collect();
        Ok(Self {
            ports,
            rotor,
            stages,
            boards,
            inverses,
            field: field.clone(),
            ring,
            configurations: configurations.to_vec(),
            lift: configurations.iter().map(|&c| BigInt::from(c)).collect(),
            taken: 0,
            last: None,
        })
    }

    /// Key `key`'s `(start, key, plugboard)`.
    fn split(&self, key: u64) -> (usize, u64, usize) {
        let boards = self.boards.len() as u64;
        let board = (key % boards) as usize;
        let rest = key / boards;
        let ports = self.ports as u64;
        ((rest / ports) as usize, rest % ports, board)
    }
}

impl Emitters for RotorKeys {
    fn alphabet(&self) -> usize {
        self.ports
    }

    fn keys(&self) -> u64 {
        (self.ports * self.ports * self.boards.len()) as u64
    }

    fn emit(&self, key: u64) -> usize {
        let (start, rotor_key, board) = self.split(key);
        match self.last {
            None => start,
            Some(previous) => {
                let stage = &self.stages[((rotor_key + self.taken) % self.rotor) as usize];
                self.inverses[board][stage[self.boards[board][previous]]]
            }
        }
    }

    fn advance(&mut self, cell: usize) -> Result<(), PopulationError> {
        if let Some(previous) = self.last {
            let step = self.field.selective_step(&mut self.lift, previous)?;
            self.taken += u64::from(step.ticks[self.ring]);
        }
        self.last = Some(cell);
        Ok(())
    }

    fn coordinates(&self, key: u64) -> Vec<u64> {
        let (start, rotor_key, board) = self.split(key);
        [start as u64, rotor_key]
            .into_iter()
            .chain(self.boards[board].iter().map(|&image| image as u64))
            .collect()
    }

    /// The ring, its ports, its rotor's period, the declared configurations (as declared, never the
    /// lift a passage has stepped) and the machine's stages; the field's rings by their periods.
    fn declaration(&self) -> Declaration {
        let mut parameters = vec![self.ring as u64, self.ports as u64, self.rotor];
        parameters.extend(&self.configurations);
        parameters.extend(self.stages.iter().flatten().map(|&port| port as u64));
        Declaration::new("rotor keys", parameters).with(vec![Declaration::new(
            "field rings",
            self.field
                .rings()
                .iter()
                .map(|ring| ring.period())
                .collect(),
        )])
    }

    /// [definition; agent-inferred] **A rotor key's signature** (module header of `species`): its
    /// next class depends on the cell before it, so its signature is its transition table over one
    /// rotor period from the current stage, `S⁻¹ W_(key + T + j) S x` for every stage offset `j`
    /// and every cell `x` it steps from (its start first, before the first cell): sufficient for
    /// every future passage, whatever ticks the field takes.
    fn signature(&self, key: u64, _future: AdmittedFuture) -> Option<Vec<usize>> {
        let (start, rotor_key, board) = self.split(key);
        let mut word = Vec::with_capacity(1 + self.rotor as usize * self.ports);
        if self.last.is_none() {
            word.push(start);
        }
        for offset in 0..self.rotor {
            let stage = &self.stages[((rotor_key + self.taken + offset) % self.rotor) as usize];
            word.extend(
                (0..self.ports).map(|x| self.inverses[board][stage[self.boards[board][x]]]),
            );
        }
        Some(word)
    }
}

/// The permutations of `0..n` in lexicographic order.
fn permutations(n: usize) -> Vec<Vec<usize>> {
    let mut current: Vec<usize> = (0..n).collect();
    let mut all = vec![current.clone()];
    loop {
        let Some(i) = (1..n).rev().find(|&i| current[i - 1] < current[i]) else {
            return all;
        };
        let j = (i..n)
            .rev()
            .find(|&j| current[j] > current[i - 1])
            .expect("a successor exists past a rise");
        current.swap(i - 1, j);
        current[i..].reverse();
        all.push(current.clone());
    }
}

// -------------------------------------------------------------------------------------------
// the key families' declarations

impl KeyFamily {
    /// **The grating family of a declared moiré family and class** (module header): the parity
    /// color over the joint key space, refused past `admitted` with the Bombe it is owed to; the
    /// sheet tuple factorized, one ring a factor, each factor within `admitted`.
    pub fn gratings(
        family: &MoireFamily,
        class: MoireClass,
        admitted: u64,
        description: u64,
    ) -> Result<Self, PopulationError> {
        if family.rings == 0 || family.denominator < 2 {
            return Err(refuse(
                "a grating family",
                "it declares at least one ring and a denominator of at least 2",
            ));
        }
        match class {
            MoireClass::Parity => {
                let rings = u32::try_from(family.rings)
                    .map_err(|_| refuse("a grating family", "its rings fit a machine word"))?;
                let space = BigUint::from(family.gratings()).pow(rings);
                if space > BigUint::from(admitted) {
                    return Err(PopulationError::Bombe {
                        key_space: space,
                        admitted: BigUint::from(admitted),
                        bombe: MOIRE_BOMBE,
                    });
                }
                let factor =
                    Survivors::new(Box::new(GratingParity::new(family)?), admitted, MOIRE_BOMBE)?;
                Self::new(
                    format!(
                        "gratings k = {}, q ≤ {}, parity color (joint)",
                        family.rings, family.denominator
                    ),
                    description,
                    vec![factor],
                )
            }
            MoireClass::Sheets => {
                let factors = (0..family.rings)
                    .map(|_| {
                        Survivors::new(Box::new(GratingSheet::new(family)?), admitted, MOIRE_BOMBE)
                    })
                    .collect::<Result<Vec<Survivors>, _>>()?;
                Self::new(
                    format!(
                        "gratings k = {}, q ≤ {}, sheet tuple (per ring)",
                        family.rings, family.denominator
                    ),
                    description,
                    factors,
                )
            }
        }
    }

    /// **The rotor family of a declared field's ring** (module header): its start, key and
    /// plugboard, refused past `admitted` with the built Bombe.
    pub fn rotor(
        field: &Field,
        ring: usize,
        configurations: &[u64],
        admitted: u64,
        description: u64,
    ) -> Result<Self, PopulationError> {
        let keys = RotorKeys::new(field, ring, configurations, admitted)?;
        let label = format!(
            "rotor keys, ring {ring} of {} ports: start, key, plugboard",
            keys.ports
        );
        let factor = Survivors::new(Box::new(keys), admitted, ROTOR_BOMBE)?;
        Self::new(label, description, vec![factor])
    }
}

impl DormantFamily {
    /// **The dormant grating family of a declared moiré family and class** (module header of
    /// `dormancy`): the parity color over the joint key space, each ring a layer, refused past
    /// `admitted` key states with the Bombe it is owed to; the sheet tuple factorized, one ring a
    /// factor of one layer. Every layer shares the fixed share at `α = 2^(−rung)`.
    pub fn gratings(
        family: &MoireFamily,
        class: MoireClass,
        admitted: u64,
        rung: u32,
        description: u64,
    ) -> Result<Self, PopulationError> {
        if family.rings == 0 || family.denominator < 2 {
            return Err(refuse(
                "a dormant grating family",
                "it declares at least one ring and a denominator of at least 2",
            ));
        }
        match class {
            MoireClass::Parity => {
                let rings = u32::try_from(family.rings).map_err(|_| {
                    refuse("a dormant grating family", "its rings fit a machine word")
                })?;
                let space = BigUint::from(family.gratings()).pow(rings)
                    * (BigUint::from(1u32) << family.rings);
                if space > BigUint::from(admitted) {
                    return Err(PopulationError::Bombe {
                        key_space: space,
                        admitted: BigUint::from(admitted),
                        bombe: MOIRE_BOMBE,
                    });
                }
                let factor = Dormancy::new(
                    Box::new(GratingParity::new(family)?),
                    rung,
                    admitted,
                    MOIRE_BOMBE,
                )?;
                Self::new(
                    format!(
                        "dormant gratings k = {}, q ≤ {}, parity color (joint), α = 2^(−{rung})",
                        family.rings, family.denominator
                    ),
                    description,
                    vec![factor],
                )
            }
            MoireClass::Sheets => {
                let factors = (0..family.rings)
                    .map(|_| {
                        Dormancy::new(
                            Box::new(GratingSheet::new(family)?),
                            rung,
                            admitted,
                            MOIRE_BOMBE,
                        )
                    })
                    .collect::<Result<Vec<Dormancy>, _>>()?;
                Self::new(
                    format!(
                        "dormant gratings k = {}, q ≤ {}, sheet tuple (per ring), α = 2^(−{rung})",
                        family.rings, family.denominator
                    ),
                    description,
                    factors,
                )
            }
        }
    }
}
