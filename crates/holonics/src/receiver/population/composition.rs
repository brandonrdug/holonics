//! **Composition at ports: eggs joined into a Holarchy of eggs** (`docs/ELEMENTARY_OBJECTS.md`, "The
//! egg: a generator read as a whole", keystones and their maintenance; rebuild step 4 item 6, #73;
//! Lean `Compression/Landmark/Context/Composition`).
//!
//! [definition; agent-inferred] **A keystone** ([`Keystone`]) is a declared finite key space of
//! navigators, each exposing its state at a port ([`Port`]: the phase on its circle and its winding,
//! the carry it has passed up; the arithmetic terrain's record clock exposes the record's phase and
//! the records completed). A **port path** ([`PortPath`]) is a chain of located keys, root first: it
//! reads the port a family meets at each tick from the passage's own clock ([`Port::tick`]) through
//! each keystone in turn, so a keystone can itself read an upstream port (the counter reads the
//! clock). A **conditioned family** is any [`Family`] built on a port path: its face is its face
//! given what the port reads. The composed family `A ⊳ B` ([`Composed`]) is the mixture over the
//! keystone's keys of the conditioned family built under each:
//!
//! ```text
//! P_(A⊳B)(x_t | past) = Σ_a P_A(a | past) · P_B(x_t | past, a),     P_A(a | past) ∝ π_a L_(B|a)(past)
//! ```
//!
//! exactly: the keystone's posterior is carried as exact rationals over its surviving keys, moved by
//! Bayes at each cell (`w′_a = w_a P_(B|a)(x)/q`), and a key whose conditioned family gives the
//! received cell zero dies, so **a deterministic keystone is survivor filtered by the family that
//! reads it**, like the other deterministic families (`Population.survivor_code`). The composed face
//! is a face wherever the constituents' are (Lean `Composition.{composedFace_nonneg,
//! composedFace_sum_one, composedFace_pos}`), its product telescopes to `Σ_a π_a L_(B|a)`
//! (`composed_telescope`), and under the uniform prior **the chain rule** holds along the surviving
//! keys (`chain_rule`, `chain_rule_of_species`):
//!
//! ```text
//! code(A⊳B) = (log₂ |K_A| − log₂ #S_A) + code(B | A),    code(B | A) = −log₂ (Σ_(a∈S_A) L_(B|a)/#S_A)
//! ```
//!
//! the keystone's key description less its surviving fibre, plus the conditioned family's code at
//! the mean of its likelihoods over the surviving keys (its code under the located key once one key
//! survives, or a species every admitted receiver reads alike). The composed family's likelihood is
//! the product of its composed faces, enclosed by `PassageCode`: the members' likelihoods can grow
//! past any exact carrier worth dividing (an operand cell's `1/b` a cell), while the posterior
//! stays small.
//!
//! [definition; agent-inferred] **A deterministic egg reading a port** ([`PortReader`]) emits one
//! class at each port reading. Keyed through a keystone it is a key space of emitters
//! ([`PortedEmitters`], `e_k(t) = R(port_A(k, upstream(t)))`), survivor filtered by `KeyFamily` like
//! any declared key family: the composition of two deterministic eggs is survivor filtering over the
//! keystone's keys, and its code is `log₂ |K_A| − log₂ #S`.
//!
//! [definition; agent-inferred] **A keystone's value** is the joint code without it against with it,
//! never its own bits (the egg's section in `ELEMENTARY_OBJECTS`). Without the keystone its port is
//! **unheld**: no key is located, so a stateless reader meets the keystone's prior pushed through the
//! port at every tick ([`Unheld`], `P(x_t) = #{k : R(port_A(k, t)) = x_t}/|K_A|`, never filtered).
//! That is the reader alone. A conditioned family that holds state along its port path (the carry
//! egg holds a record's operands, read at the clock's phases) has no reading at an unheld port: its
//! arch falls with the keystone, and the joint code without the keystone is the population's other
//! families (the notebook reads the population without the record clock as the tree alone).
//!
//! [definition] The computational object is the helical pair interaction, read as eggs joined at
//! ports. Of the winding guide's six general objects this owner touches three: the **helix** (a
//! port's phase and its winding: the clock's record phase and its carry, the counter's odometer),
//! **faces and placement** (the composed face and each constituent's face given its port) and the
//! **tower thread** (a record's phases restrict a cell to its place in the record). The pair, the
//! cell holonomy and the tube stay attached through the constituents' owners.

use std::sync::Arc;

use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use rayon::prelude::*;

use super::{Emitters, Family, KeyReadout, Likelihood, PopulationError, Readout, refuse};
use crate::compression::landmark::context::PassageCode;
use crate::ratio::Rat;

/// [definition] **A port's reading**: the phase on the exposing navigator's circle and its winding,
/// the carry it has passed up (module header).
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub struct Port {
    pub phase: u64,
    pub winding: u64,
}

impl Port {
    /// **The passage's own clock** at tick `t`: one winding a cell, phase zero.
    pub fn tick(tick: u64) -> Self {
        Self {
            phase: 0,
            winding: tick,
        }
    }
}

/// [definition] **A keystone** (module header): a declared finite key space of navigators, each
/// exposing its state at a port given the port it reads upstream.
pub trait Keystone: Send + Sync {
    /// The keystone's declaration, for a receipt.
    fn label(&self) -> String;
    /// `|K_A|`.
    fn keys(&self) -> u64;
    /// The port key `key` exposes when its upstream port reads `upstream`.
    fn port(&self, key: u64, upstream: Port) -> Port;
    /// Key `key`'s coordinates in the keystone's declared layout.
    fn coordinates(&self, key: u64) -> Vec<u64>;
}

/// [definition] **A port path** (module header): located keys of a chain of keystones, root first.
#[derive(Clone, Default)]
pub struct PortPath {
    links: Vec<(Arc<dyn Keystone>, u64)>,
}

impl PortPath {
    /// The passage's own clock: no keystone yet.
    pub fn tick() -> Self {
        Self::default()
    }

    /// The path extended through `keystone` at its key `key`.
    pub fn through(&self, keystone: Arc<dyn Keystone>, key: u64) -> Self {
        let mut links = self.links.clone();
        links.push((keystone, key));
        Self { links }
    }

    /// **The port read at tick `t`**: the passage's clock through every located keystone in turn.
    pub fn read(&self, tick: u64) -> Port {
        self.links
            .iter()
            .fold(Port::tick(tick), |port, (keystone, key)| {
                keystone.port(*key, port)
            })
    }

    /// The located keys, root first.
    pub fn keys(&self) -> Vec<u64> {
        self.links.iter().map(|(_, key)| *key).collect()
    }
}

/// [definition] **A deterministic egg reading a port** (module header): the class it emits at each
/// port reading.
pub trait PortReader: Send + Sync {
    /// The reader's declaration, for a receipt.
    fn label(&self) -> String;
    /// The emitted classes' alphabet.
    fn alphabet(&self) -> usize;
    /// The class emitted at a port reading.
    fn emit(&self, port: Port) -> usize;
}

// -------------------------------------------------------------------------------------------
// deterministic composition: a reader keyed through a keystone

/// [definition] **A reader keyed through a keystone** (module header): key `k` of the keystone
/// emits `R(port_A(k, upstream(t)))` at tick `t`, the upstream port read along the declared path.
#[derive(Clone)]
pub struct PortedEmitters {
    keystone: Arc<dyn Keystone>,
    reader: Arc<dyn PortReader>,
    upstream: PortPath,
    tick: u64,
    port: Port,
}

impl PortedEmitters {
    /// The reader keyed through the keystone on the upstream path; refused at an empty key space or
    /// alphabet.
    pub fn new(
        keystone: Arc<dyn Keystone>,
        reader: Arc<dyn PortReader>,
        upstream: PortPath,
    ) -> Result<Self, PopulationError> {
        if keystone.keys() == 0 || reader.alphabet() == 0 {
            return Err(refuse(
                "a reader keyed through a keystone",
                "its keystone holds a key and its reader a class",
            ));
        }
        let port = upstream.read(0);
        Ok(Self {
            keystone,
            reader,
            upstream,
            tick: 0,
            port,
        })
    }

    /// **The keys emitting `class`** at the current tick, counted over the whole key space on the
    /// host's cores (each key read once, no key written: the hardware law's shared immutable input).
    pub fn count(&self, class: usize) -> u64 {
        (0..self.keystone.keys())
            .into_par_iter()
            .filter(|&key| self.emit(key) == class)
            .count() as u64
    }

    /// The keystone.
    pub fn keystone(&self) -> &dyn Keystone {
        self.keystone.as_ref()
    }
}

impl Emitters for PortedEmitters {
    fn alphabet(&self) -> usize {
        self.reader.alphabet()
    }

    fn keys(&self) -> u64 {
        self.keystone.keys()
    }

    fn emit(&self, key: u64) -> usize {
        self.reader.emit(self.keystone.port(key, self.port))
    }

    fn advance(&mut self, _cell: usize) -> Result<(), PopulationError> {
        self.tick += 1;
        self.port = self.upstream.read(self.tick);
        Ok(())
    }

    fn coordinates(&self, key: u64) -> Vec<u64> {
        self.keystone.coordinates(key)
    }

    fn fork_at(&self, tick: u64) -> Option<Box<dyn Emitters>> {
        let mut fork = self.clone();
        fork.tick = tick;
        fork.port = fork.upstream.read(tick);
        Some(Box::new(fork))
    }
}

// -------------------------------------------------------------------------------------------
// the reader at an unheld port

/// [definition; agent-inferred] **A reader at an unheld port** (module header, "A keystone's
/// value"): the keystone's key is never located, so each tick the reader meets the keystone's prior
/// pushed through the port: `P(x_t) = #{k : R(port_A(k, t)) = x_t}/|K_A|`, never filtered. Its
/// likelihood is the product of those faces, enclosed.
pub struct Unheld {
    label: String,
    description: u64,
    emitters: PortedEmitters,
    passage: PassageCode,
}

impl Unheld {
    /// The reader of the emitters at their keystone's unheld port.
    pub fn new(label: String, description: u64, emitters: PortedEmitters) -> Self {
        Self {
            label,
            description,
            emitters,
            passage: PassageCode::new(),
        }
    }
}

impl Family for Unheld {
    fn label(&self) -> String {
        self.label.clone()
    }

    fn alphabet(&self) -> usize {
        self.emitters.alphabet()
    }

    fn description(&self) -> u64 {
        self.description
    }

    fn face(&self) -> Result<Vec<Rat>, PopulationError> {
        let keys = BigInt::from(self.emitters.keys());
        Ok((0..self.alphabet())
            .map(|class| Rat::new(BigInt::from(self.emitters.count(class)), keys.clone()))
            .collect())
    }

    fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError> {
        let alphabet = self.alphabet();
        if cell >= alphabet {
            return Err(PopulationError::CellOutside { cell, alphabet });
        }
        let face = Rat::new(
            BigInt::from(self.emitters.count(cell)),
            BigInt::from(self.emitters.keys()),
        );
        if face.is_zero() {
            return Ok(face);
        }
        self.emitters.advance(cell)?;
        self.passage.face(&face)?;
        Ok(face)
    }

    fn likelihood(&self) -> Likelihood {
        Likelihood::Enclosed(self.passage)
    }

    /// An unheld port locates no key: the readout holds no factor.
    fn readout(&self) -> Readout<'_> {
        Readout::Keys(KeyReadout {
            spaces: Vec::new(),
            survivors: Vec::new(),
            masses: Vec::new(),
            dormant: Vec::new(),
        })
    }
}

// -------------------------------------------------------------------------------------------
// the composed family

/// [definition] **A conditioned family's declaration**: the family built on a port path (its
/// keystone's key located on it).
pub type Conditioned =
    Box<dyn Fn(PortPath) -> Result<Box<dyn Family>, PopulationError> + Send + Sync>;

/// One surviving key of the keystone: the conditioned family built under it and its exact
/// posterior.
struct Held {
    key: u64,
    family: Box<dyn Family>,
    weight: Rat,
}

/// [definition; agent-inferred] **The composed family `A ⊳ B`** (module header): the keystone's
/// surviving keys, each with the conditioned family built on the path through it and the key's
/// exact posterior; the likelihood is the product of the composed faces, enclosed.
pub struct Composed {
    label: String,
    description: u64,
    alphabet: usize,
    keystone: Arc<dyn Keystone>,
    held: Vec<Held>,
    passage: PassageCode,
}

impl Composed {
    /// **Compose** the keystone, keyed on the upstream path, with the conditioned family built
    /// under each of its keys, under the uniform prior over the keys. Refused at an empty key
    /// space, past the declared enumeration `admitted`, and when the conditioned families read
    /// different alphabets.
    pub fn new(
        label: String,
        description: u64,
        keystone: Arc<dyn Keystone>,
        upstream: &PortPath,
        conditioned: &Conditioned,
        admitted: u64,
    ) -> Result<Self, PopulationError> {
        let keys = keystone.keys();
        if keys == 0 {
            return Err(refuse("a composed family", "its keystone holds a key"));
        }
        if keys > admitted {
            return Err(refuse(
                "a composed family",
                "its keystone's keys lie within the declared enumeration",
            ));
        }
        let weight = Rat::new(BigInt::from(1u32), BigInt::from(keys));
        let held = (0..keys)
            .map(|key| {
                Ok(Held {
                    key,
                    family: conditioned(upstream.through(Arc::clone(&keystone), key))?,
                    weight: weight.clone(),
                })
            })
            .collect::<Result<Vec<Held>, PopulationError>>()?;
        let alphabet = held[0].family.alphabet();
        if alphabet == 0
            || held
                .iter()
                .any(|member| member.family.alphabet() != alphabet)
        {
            return Err(refuse(
                "a composed family",
                "its conditioned families read one declared alphabet",
            ));
        }
        Ok(Self {
            label,
            description,
            alphabet,
            keystone,
            held,
            passage: PassageCode::new(),
        })
    }

    /// The keystone.
    pub fn keystone(&self) -> &dyn Keystone {
        self.keystone.as_ref()
    }

    /// **The keystone's posterior** over its surviving keys, exact, ascending by key.
    pub fn posterior(&self) -> Vec<(u64, Rat)> {
        self.held
            .iter()
            .map(|member| (member.key, member.weight.clone()))
            .collect()
    }

    /// The conditioned family built under a surviving key.
    pub fn conditioned(&self, key: u64) -> Option<&dyn Family> {
        self.held
            .iter()
            .find(|member| member.key == key)
            .map(|member| member.family.as_ref())
    }
}

impl Family for Composed {
    fn label(&self) -> String {
        self.label.clone()
    }

    fn alphabet(&self) -> usize {
        self.alphabet
    }

    fn description(&self) -> u64 {
        self.description
    }

    /// `q(c) = Σ_a w_a P_(B|a)(c)`, exact.
    fn face(&self) -> Result<Vec<Rat>, PopulationError> {
        let mut face = vec![Rat::zero(); self.alphabet];
        for member in &self.held {
            for (sum, class) in face.iter_mut().zip(member.family.face()?) {
                *sum += &member.weight * class;
            }
        }
        Ok(face)
    }

    /// **Receive one cell**: each surviving key's conditioned family reads it (on the host's cores,
    /// each writing only its own state), the composed face `q = Σ_a w_a P_(B|a)(x)` is returned, the
    /// keys whose family gave it zero die and the rest move by Bayes. At `q = 0` nothing moves: every
    /// conditioned family gave zero, and a conditioned family that gives a cell zero deposits nothing.
    fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError> {
        if cell >= self.alphabet {
            return Err(PopulationError::CellOutside {
                cell,
                alphabet: self.alphabet,
            });
        }
        let faces = self
            .held
            .par_iter_mut()
            .map(|member| member.family.receive(cell))
            .collect::<Result<Vec<Rat>, PopulationError>>()?;
        if faces.iter().any(|face| face.is_negative()) {
            return Err(refuse(
                "a conditioned family's face of a cell",
                "it is nonnegative",
            ));
        }
        let face: Rat = self
            .held
            .iter()
            .zip(&faces)
            .map(|(member, face)| &member.weight * face)
            .sum();
        if face.is_zero() {
            return Ok(face);
        }
        let held = std::mem::take(&mut self.held);
        self.held = held
            .into_iter()
            .zip(faces)
            .filter(|(_, conditioned)| !conditioned.is_zero())
            .map(|(member, conditioned)| Held {
                weight: &member.weight * &conditioned / &face,
                ..member
            })
            .collect();
        self.passage.face(&face)?;
        Ok(face)
    }

    fn likelihood(&self) -> Likelihood {
        Likelihood::Enclosed(self.passage)
    }

    /// The keystone's surviving keys with their posteriors (the first factor), then, once one key
    /// survives, its conditioned family's own located keys.
    fn readout(&self) -> Readout<'_> {
        let mut readout = KeyReadout {
            spaces: vec![self.keystone.keys()],
            survivors: vec![
                self.held
                    .iter()
                    .map(|member| self.keystone.coordinates(member.key))
                    .collect(),
            ],
            masses: vec![
                self.held
                    .iter()
                    .map(|member| member.weight.clone())
                    .collect(),
            ],
            dormant: Vec::new(),
        };
        if let [member] = self.held.as_slice()
            && let Readout::Keys(inner) = member.family.readout()
        {
            for (factor, survivors) in inner.survivors.into_iter().enumerate() {
                readout.spaces.push(inner.spaces[factor]);
                readout.survivors.push(survivors);
                readout
                    .masses
                    .push(inner.masses.get(factor).cloned().unwrap_or_default());
            }
        }
        Readout::Keys(readout)
    }

    fn admits(&self, cells: &[usize]) -> Result<(), PopulationError> {
        self.held
            .iter()
            .try_for_each(|member| member.family.admits(cells))
    }
}
