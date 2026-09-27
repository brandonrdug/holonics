//! **The declared navigator families a population weighs** (the module header of
//! `receiver::population`): the receiving tree at a declared depth and stop prior, and the key
//! families whose key spaces are the terrain's own declarations: a moiré's gratings
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
//!   coordinates `(p_0, q_0, c_0, p_1, …)`. Its survivors keep the class's gauge: the rings'
//!   permutations, and two even gratings turned by a half-turn together (a half-turn flips a sheet).
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

use std::collections::VecDeque;

use num_bigint::{BigInt, BigUint};
use num_traits::ToPrimitive;

use super::{Emitters, Family, KeyFamily, Likelihood, PopulationError, Readout, Survivors, refuse};
use crate::compression::landmark::context::{
    LandmarkDeclaration, Landmarks, Letter, PassageCode, StopPrior,
};
use crate::hnn::field::Field;
use crate::holarchy::terrain::{Grating, MoireClass, MoireFamily};
use crate::ratio::Rat;

/// **The Bombe a moiré's joint key space is owed to**: its phases located by loop closure over a
/// menu of parity relations on the joint clock torus (the audit record's §6.3).
pub const MOIRE_BOMBE: &str = "parity-constraint propagation on the joint clock torus, one parity relation a tick over at most Π q_i phase configurations once the rates are known; owed";

/// **The built Bombe of a rotor crib**: pairwise loop closure over the crib's menu.
pub const ROTOR_BOMBE: &str =
    "hnn::keys::locate_ring, pairwise loop closure over the crib's menu; built";

// -------------------------------------------------------------------------------------------
// the receiving tree

/// [definition] **The tree family** (`compression::landmark::context`): the receiving tree over the
/// cell-only letters at a declared depth and stop prior, reading the address of the last `D` cells
/// (the shift navigator's address at the declared depth, its standing: Lean
/// `Compression/Landmark/Context/Standing.address_standing`), each cell scored at the current
/// standing by its executed face and then deposited, its likelihood the product of those faces
/// enclosed by `PassageCode` (as `hnn::reference::tree_prequential` scores it).
pub struct TreeFamily {
    label: String,
    description: u64,
    tree: Landmarks,
    past: VecDeque<usize>,
    passage: PassageCode,
}

impl TreeFamily {
    /// **The tree family of a declaration**; refused unless its letter family is the cell-only one.
    pub fn new(
        declaration: LandmarkDeclaration,
        description: u64,
    ) -> Result<Self, PopulationError> {
        if !declaration.family.is_empty() {
            return Err(refuse(
                "a tree family",
                "it reads the cell-only letters, the population's cells",
            ));
        }
        let prior = if declaration.prior == StopPrior::half() {
            "½"
        } else {
            "declared"
        };
        let label = format!("tree D = {}, stop prior {prior}", declaration.depth);
        Ok(Self {
            label,
            description,
            tree: Landmarks::new(declaration)?,
            past: VecDeque::new(),
            passage: PassageCode::new(),
        })
    }

    /// The tree.
    pub fn tree(&self) -> &Landmarks {
        &self.tree
    }

    /// The address of the next cell: the last `D` cells, newest first, `Boundary` before the first.
    fn address(&self) -> Vec<Letter> {
        let depth = self.tree.declaration().depth;
        (0..depth)
            .map(|back| {
                self.past
                    .len()
                    .checked_sub(back + 1)
                    .map_or(Letter::Boundary, |at| Letter::Cell(self.past[at]))
            })
            .collect()
    }
}

impl Family for TreeFamily {
    fn label(&self) -> String {
        self.label.clone()
    }

    fn alphabet(&self) -> usize {
        self.tree.declaration().alphabet
    }

    fn description(&self) -> u64 {
        self.description
    }

    fn face(&self) -> Result<Vec<Rat>, PopulationError> {
        let grain = self.tree.declaration().grain;
        Ok(self.tree.face(&self.address(), grain)?.probabilities)
    }

    fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError> {
        let reading = self.tree.receive(&self.address(), cell)?;
        self.passage.face(&reading.executed)?;
        self.past.push_back(cell);
        if self.past.len() > self.tree.declaration().depth {
            self.past.pop_front();
        }
        Ok(reading.executed)
    }

    fn likelihood(&self) -> Likelihood {
        Likelihood::Enclosed(self.passage)
    }

    fn readout(&self) -> Readout<'_> {
        Readout::Standing(&self.tree)
    }
}

// -------------------------------------------------------------------------------------------
// the moiré's gratings

/// [definition] **One ring's key space** (module header): the declared family's gratings, each
/// emitting its half-turn sheet.
pub struct GratingSheet {
    gratings: Vec<Grating>,
    words: Vec<Vec<bool>>,
    tick: u64,
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
        let word = &self.words[index];
        word[(self.tick % word.len() as u64) as usize]
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
}

/// [definition] **The parity color's joint key space** (module header): `k` rings over the family's
/// gratings.
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
