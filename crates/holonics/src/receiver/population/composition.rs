//! **Composition at ports: eggs joined into a Holarchy of eggs** (`docs/ELEMENTARY_OBJECTS.md`, "The
//! egg: a generator read as a whole", keystones and their maintenance; rebuild step 4 item 6, #73;
//! Lean `Compression/Landmark/Context/Composition`).
//!
//! [definition; agent-inferred] **A keystone** ([`Keystone`]) is a declared finite key space of
//! navigators, each exposing its state at a port ([`Port`]: the phase on its circle and its winding,
//! the carry it has passed up; a moiré's grating, a rotor ring keyed at its port, exposes its phase
//! and the turns it has completed). A **port path** ([`PortPath`]) is a chain of located keys, root
//! first: it reads the port a family meets at each tick from the passage's own clock
//! ([`Port::tick`]) through each keystone in turn, so a keystone can itself read an upstream port (a
//! ring stepped by another's carry, as an odometer's wheels and a rotor machine's rings step). A
//! **conditioned family** is any [`Family`] built on a port path: its face is its face
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
//! That is the reader alone. A conditioned family that holds state along its port path (one that
//! keeps what it read at earlier phases to face a later one) has no reading at an unheld port: its
//! arch falls with the keystone, and the joint code without the keystone is the population's other
//! families.
//!
//! [definition; agent-inferred] **Re-founding and species.** A port path is read from the passage's
//! cell at its start ([`PortPath::starting`]), so a composed egg's seed (its keystone's surviving
//! keys) is re-founded at a later cell, each conditioned family from its own seed or declared anew on
//! the path from that cell (`Composed`'s `reseed`). Its species (`receiver::population::species`)
//! are collapsed within each keystone key's conditioned family and across the keystone keys whose
//! conditioned families are certain with one signature; a merged member returns at a split from its
//! seed, declared anew on the path from the current cell and holding its seed's keys.
//!
//! [definition] The computational object is the helical pair interaction, read as eggs joined at
//! ports. Of the winding guide's six general objects this owner touches three: the **helix** (a
//! port's phase and its winding: a ring's phase and its carry, a stepped ring's odometer),
//! **faces and placement** (the composed face and each constituent's face given its port) and the
//! **tower thread** (a port path restricts each keystone to the carry of the one below it). The
//! pair, the cell holonomy and the tube stay attached through the constituents' owners.

use std::collections::BTreeMap;
use std::sync::Arc;

use num_bigint::BigInt;
use num_traits::{Signed, Zero};
use rayon::prelude::*;

use super::species::earliest;
use super::{
    Act, AdmittedFuture, Collapse, Declaration, Emitters, Family, KeyReadout, KeystoneMember,
    KeystoneSpecies, Likelihood, PopulationError, Readout, Work, refuse,
};
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
    /// **The keystone's declaration** (the population's identity, module header of `evolution`).
    fn declaration(&self) -> Declaration;
}

/// [definition] **A port path** (module header): located keys of a chain of keystones, root first,
/// read from the passage's clock at its start (a family founded at a later cell reads the passage's
/// clock from that cell: its keys wind without the cells).
#[derive(Clone, Default)]
pub struct PortPath {
    links: Vec<(Arc<dyn Keystone>, u64)>,
    start: u64,
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
        Self {
            links,
            start: self.start,
        }
    }

    /// **The same path read from the passage's cell `start`**: its tick zero is that cell.
    pub fn starting(&self, start: u64) -> Self {
        Self {
            links: self.links.clone(),
            start,
        }
    }

    /// The passage's cell the path's tick zero reads.
    pub fn start(&self) -> u64 {
        self.start
    }

    /// **The port read at tick `t`**: the passage's clock at `start + t` through every located
    /// keystone in turn.
    pub fn read(&self, tick: u64) -> Port {
        self.links
            .iter()
            .fold(Port::tick(self.start + tick), |port, (keystone, key)| {
                keystone.port(*key, port)
            })
    }

    /// The located keys, root first.
    pub fn keys(&self) -> Vec<u64> {
        self.links.iter().map(|(_, key)| *key).collect()
    }

    /// The keystones' declarations, root first (their keys are located, not declared).
    pub fn declarations(&self) -> Vec<Declaration> {
        self.links
            .iter()
            .map(|(keystone, _)| keystone.declaration())
            .collect()
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
    /// **The reader's declaration**.
    fn declaration(&self) -> Declaration;
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

    /// The emitters at the passage's cell `tick` (their path read from its start).
    fn fork_at(&self, tick: u64) -> Option<Box<dyn Emitters>> {
        let mut fork = self.clone();
        fork.tick = tick.checked_sub(self.upstream.start())?;
        fork.port = fork.upstream.read(fork.tick);
        Some(Box::new(fork))
    }

    fn declaration(&self) -> Declaration {
        let mut parts = self.upstream.declarations();
        parts.push(self.keystone.declaration());
        parts.push(self.reader.declaration());
        Declaration::new("reader keyed through a keystone", Vec::new()).with(parts)
    }

    /// The port winds without the cells: key `k`'s class `ticks` ahead is its reader's at the port
    /// read then.
    fn ahead(&self, key: u64, ticks: u64) -> Option<usize> {
        Some(
            self.reader.emit(
                self.keystone
                    .port(key, self.upstream.read(self.tick + ticks)),
            ),
        )
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
    reads: u64,
}

impl Unheld {
    /// The reader of the emitters at their keystone's unheld port.
    pub fn new(label: String, description: u64, emitters: PortedEmitters) -> Self {
        Self {
            label,
            description,
            emitters,
            passage: PassageCode::new(),
            reads: 0,
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
        self.reads += self.emitters.keys();
        if face.is_zero() {
            return Ok(face);
        }
        self.emitters.advance(cell)?;
        self.passage.face(&face)?;
        Ok(face)
    }

    fn declaration(&self) -> Declaration {
        Declaration::new("unheld port", Vec::new()).with(vec![self.emitters.declaration()])
    }

    /// Every key's emission read at every cell: the prior pushed through the port.
    fn work(&self) -> Work {
        let mut work = Work::default();
        work.add(Act::Read, self.reads);
        work
    }

    fn likelihood(&self) -> Likelihood {
        Likelihood::Enclosed(self.passage)
    }

    /// An unheld port locates no key: the readout holds no factor.
    fn readout(&self) -> Readout {
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
    Arc<dyn Fn(PortPath) -> Result<Box<dyn Family>, PopulationError> + Send + Sync>;

/// One surviving key of the keystone (a species' representative once collapsed): the conditioned
/// family built under it, its exact posterior, and the keystone keys it stands for.
struct Held {
    key: u64,
    family: Box<dyn Family>,
    weight: Rat,
    members: u64,
}

/// [definition; agent-inferred] **The composed family `A ⊳ B`** (module header): the keystone's
/// surviving keys, each with the conditioned family built on the path through it and the key's
/// exact posterior; the likelihood is the product of the composed faces, enclosed. It keeps its
/// declaration (the keystone's, the upstream path's and the conditioned family's), the path it
/// reads from, the cells received, the admitted future's end of a keystone collapse, and the work
/// of the conditioned families that died.
pub struct Composed {
    label: String,
    description: u64,
    alphabet: usize,
    keystone: Arc<dyn Keystone>,
    held: Vec<Held>,
    passage: PassageCode,
    conditioned: Conditioned,
    declared: Declaration,
    upstream: PortPath,
    ticks: u64,
    until: Option<u64>,
    spent: Work,
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
                    members: 1,
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
        let mut parts = upstream.declarations();
        parts.push(keystone.declaration());
        parts.push(held[0].family.declaration());
        Ok(Self {
            label,
            description,
            alphabet,
            keystone,
            held,
            passage: PassageCode::new(),
            conditioned: Arc::clone(conditioned),
            declared: Declaration::new("composed at a port", Vec::new()).with(parts),
            upstream: upstream.clone(),
            ticks: 0,
            until: None,
            spent: Work::default(),
        })
    }

    /// The keystone.
    pub fn keystone(&self) -> &dyn Keystone {
        self.keystone.as_ref()
    }

    /// **Each surviving keystone key's members** (the keys its species stands for), ascending by
    /// key.
    pub fn members(&self) -> Vec<(u64, u64)> {
        self.held
            .iter()
            .map(|member| (member.key, member.members))
            .collect()
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
        self.spent.add(Act::Weigh, self.held.len() as u64);
        let held = std::mem::take(&mut self.held);
        let mut kept = Vec::with_capacity(held.len());
        for (member, conditioned) in held.into_iter().zip(faces) {
            if conditioned.is_zero() {
                // A key that dies leaves the work its conditioned family spent.
                self.spent.absorb(&member.family.work());
                continue;
            }
            kept.push(Held {
                weight: &member.weight * &conditioned / &face,
                ..member
            });
        }
        self.held = kept;
        self.ticks += 1;
        self.passage.face(&face)?;
        Ok(face)
    }

    fn likelihood(&self) -> Likelihood {
        Likelihood::Enclosed(self.passage)
    }

    /// The keystone's surviving keys with their posteriors (the first factor), then, once one key
    /// survives, its conditioned family's own located keys.
    fn readout(&self) -> Readout {
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
        if let [member] = self.held.as_slice() {
            let Readout::Keys(inner) = member.family.readout();
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
        if self
            .until
            .is_some_and(|end| self.ticks + cells.len() as u64 > end)
        {
            return Err(refuse(
                "a collapsed composed egg's passage",
                "it stays within the admitted future its keystone's species were collapsed over (split them from their receipt first)",
            ));
        }
        self.held
            .iter()
            .try_for_each(|member| member.family.admits(cells))
    }

    fn declaration(&self) -> Declaration {
        self.declared.clone()
    }

    /// The keystone keys weighed and every conditioned family's work (the living and the dead).
    fn work(&self) -> Work {
        let mut work = self.spent.clone();
        for member in &self.held {
            work.absorb(&member.family.work());
        }
        work
    }

    /// [definition; agent-inferred] **The composed egg re-founded from its seed** at the passage's
    /// cell `at` (item 3 of the population's remaining terms): the keystone's keys wind without the
    /// cells, so each surviving key's port is read from `at`; each conditioned family is re-founded
    /// from its own seed where it has one, else declared anew on the path from `at` (a stateful
    /// conditioned family declared anew holds nothing it read before `at`).
    /// The prior is uniform over the keystone keys the seed stands for. None while a keystone
    /// collapse's admitted future holds, and none once a conditioned family's collapse's admitted
    /// future has ended at `at`, as a key family refuses (split its species first): declaring that
    /// family anew would relearn its key space.
    fn reseed(&self, at: usize) -> Option<Box<dyn Family>> {
        if self.until.is_some() {
            return None;
        }
        let upstream = self.upstream.starting(at as u64);
        let total: u64 = self.held.iter().map(|member| member.members).sum();
        let held = self
            .held
            .iter()
            .map(|member| {
                let ended = member
                    .family
                    .seed()
                    .is_some_and(|seed| seed.until.is_some_and(|end| at as u64 >= end));
                let family = match member.family.reseed(at) {
                    Some(family) => family,
                    None if ended => return None,
                    None => {
                        (self.conditioned)(upstream.through(Arc::clone(&self.keystone), member.key))
                            .ok()?
                    }
                };
                Some(Held {
                    key: member.key,
                    family,
                    weight: Rat::new(BigInt::from(member.members), BigInt::from(total)),
                    members: member.members,
                })
            })
            .collect::<Option<Vec<Held>>>()?;
        Some(Box::new(Composed {
            label: format!("{} (re-founded from its seed)", self.label),
            description: self.description,
            alphabet: self.alphabet,
            keystone: Arc::clone(&self.keystone),
            held,
            passage: PassageCode::new(),
            conditioned: Arc::clone(&self.conditioned),
            declared: self.declared.clone(),
            upstream,
            ticks: 0,
            until: None,
            spent: Work::default(),
        }))
    }

    /// **Species within a composed egg** (module header of `species`): each surviving key's
    /// conditioned family collapses its own keys; then the keystone keys whose conditioned
    /// families are certain over the admitted future with one signature are one species, kept as
    /// the least key's family at the summed weight, every member's seed in the receipt.
    fn collapse(&mut self, future: AdmittedFuture) -> Result<Option<Collapse>, PopulationError> {
        let mut conditioned = Vec::new();
        for member in &mut self.held {
            if let Ok(Some(collapse)) = member.family.collapse(future) {
                conditioned.push((member.key, collapse));
            }
        }
        let mut certain: BTreeMap<Vec<Vec<usize>>, Vec<usize>> = BTreeMap::new();
        let mut groups: Vec<Vec<usize>> = Vec::new();
        for (index, member) in self.held.iter().enumerate() {
            match member.family.certain(future) {
                Some(signature) => certain.entry(signature).or_default().push(index),
                None => groups.push(vec![index]),
            }
        }
        groups.extend(certain.into_values());
        groups.sort_by_key(|group| group[0]);
        let keystone: Vec<KeystoneSpecies> = groups
            .iter()
            .map(|group| {
                let posterior: Rat = group.iter().map(|&i| &self.held[i].weight).sum();
                KeystoneSpecies {
                    representative: self.held[group[0]].key,
                    members: group
                        .iter()
                        .map(|&i| {
                            let member = &self.held[i];
                            KeystoneMember {
                                key: member.key,
                                members: member.members,
                                share: &member.weight / &posterior,
                                seed: member.family.seed(),
                            }
                        })
                        .collect(),
                    posterior,
                }
            })
            .collect();
        let receipt = Collapse::Composed {
            future,
            keystone: keystone.clone(),
            conditioned,
            until: self.until,
            ticks: self.ticks,
        };
        if groups.iter().any(|group| group.len() > 1) {
            let mut held: Vec<Option<Held>> = std::mem::take(&mut self.held)
                .into_iter()
                .map(Some)
                .collect();
            let mut kept = Vec::with_capacity(groups.len());
            for (group, species) in groups.iter().zip(&keystone) {
                let mut representative = held[group[0]].take().expect("a held key");
                representative.weight = species.posterior.clone();
                representative.members = species.members.iter().map(|member| member.members).sum();
                for &i in &group[1..] {
                    let member = held[i].take().expect("a held key");
                    self.spent.absorb(&member.family.work());
                }
                kept.push(representative);
            }
            self.held = kept;
            self.until = earliest(self.until, future.end(self.ticks));
        }
        Ok(Some(receipt))
    }

    /// **Split a composed egg's species** from its receipt: every member of a surviving keystone
    /// species is declared anew on the path from the current cell and holds its seed, its clock wound
    /// by the cells received since the collapse, at its share of the species' weight; then each
    /// conditioned family splits its own species. Every member is built before anything moves.
    fn split(&mut self, collapse: &Collapse) -> Result<(), PopulationError> {
        let Collapse::Composed {
            keystone,
            conditioned,
            until,
            ticks,
            ..
        } = collapse
        else {
            return Err(refuse(
                "a composed egg's species split",
                "its receipt is a composed egg's collapse",
            ));
        };
        let Some(elapsed) = self.ticks.checked_sub(*ticks) else {
            return Err(refuse(
                "a composed egg's species split",
                "its receipt was read at or before the current cell",
            ));
        };
        let now = self.upstream.start() + self.ticks;
        let mut restored: Vec<Held> = Vec::new();
        let mut moved: Vec<(usize, Rat, u64)> = Vec::new();
        for species in keystone.iter().filter(|species| species.members.len() > 1) {
            let Some(position) = self
                .held
                .iter()
                .position(|member| member.key == species.representative)
            else {
                continue;
            };
            let weight = self.held[position].weight.clone();
            for member in &species.members {
                if member.key == species.representative {
                    moved.push((position, &weight * &member.share, member.members));
                    continue;
                }
                let seed = member.seed.as_ref().ok_or_else(|| {
                    refuse(
                        "a composed egg's species split",
                        "every merged member keeps its conditioned family's seed",
                    )
                })?;
                let mut family = (self.conditioned)(
                    self.upstream
                        .starting(now)
                        .through(Arc::clone(&self.keystone), member.key),
                )?;
                let mut wound = seed.clone();
                wound.tick += elapsed;
                family.restrict(&wound)?;
                restored.push(Held {
                    key: member.key,
                    family,
                    weight: &weight * &member.share,
                    members: member.members,
                });
            }
        }
        for (position, weight, members) in moved {
            self.held[position].weight = weight;
            self.held[position].members = members;
        }
        self.held.extend(restored);
        self.held.sort_by_key(|member| member.key);
        for (key, nested) in conditioned {
            if let Some(member) = self.held.iter_mut().find(|member| member.key == *key) {
                member.family.split(nested)?;
            }
        }
        self.until = *until;
        Ok(())
    }
}
