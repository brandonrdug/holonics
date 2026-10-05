//! **The chase's reception families: one per candidate runner** (`holarchy::terrain::chase`;
//! THE_REBUILD F6, the reception phase).
//!
//! [definition; agent-inferred] **A candidate's face** ([`ChaseFamily`]). A candidate of the
//! declared runner family (`holarchy::terrain::RunnerFamily`: its constitution, slip hold and
//! evasion navigator) reads the receiver's ports (the arena, the pursuer's position each tick, the
//! runner's opening motion) and the received cells, and emits exactly one letter a tick
//! (`Runner::cell` from the observed motion and its own slip counter). Its face is that law's,
//! smoothed by a declared **escape mass** `η = 2^(−j)` so faces stay positive:
//!
//! ```text
//! P_f(x | past) = 1 − η            x the candidate's own letter
//!               = η/(A − 1)        every other letter of the alphabet A
//! ```
//!
//! so a candidate the passage contradicts pays `−log₂(η/(A − 1))` bits at each contradiction and is
//! never killed, and the population's product telescopes as for every family. After the cell its
//! state follows the **received** cell (`Runner::receive`), never its own letter: the observed
//! motion is the cells' and the ports', and only the slip counter is the candidate's.
//!
//! [definition; agent-inferred] **Why `j = 12` in the receipts.** A contradiction then costs
//! `12 + log₂(A − 1)` bits, above the naming of the family's candidates (`⌈log₂ N⌉ = 6` bits for
//! the declared 40), so one contradiction moves the posterior past the prior; a candidate the passage
//! never contradicts pays `−log₂(1 − 2^(−12)) < 2^(−11)` bits a tick, less than one bit over `2^11`
//! ticks. The consistent candidates' likelihood `(1 − η)^n` exceeds every contradicted one's when
//! `δ = η/(A − 1) < 1 − η` (and a single contradiction's only then), that is `η < (A − 1)/A`, which
//! `2^(−12)` meets for every `A ≥ 2`.
//!
//! [proved-derived; formal-checked] **The population selects the surviving fibre** (Lean
//! `Compression/Landmark/Context/Population.escaped_fibre_is_mode`). Under the uniform prior of the
//! family's naming, the families of greatest posterior are exactly the candidates the passage never
//! contradicts (the terrain's `Chase::fibre`) whenever one is: [`selected_fibre`] reads them from
//! the exact likelihoods and priors. [measured] On the receipts' arenas the fibre's joint posterior
//! is decided above one half: a fibre of one member is the population's selected family, and a
//! plural fibre is the species the passage cannot split, above one half jointly while no member is.
//!
//! [definition] The computational object is the helical pair interaction read by a receiver: the
//! candidate's navigator meeting the arena's friction field at its contact, and its contact with the
//! pursuer. Of the winding guide's six objects this owner touches **faces and placement** (the
//! candidate's face on the move alphabet) and the **tube** (the passage, one cell a tick); the
//! **helix**, the **pair**, the **cell holonomy** and the **tower thread** stay attached through
//! the terrain's law it reads.

use std::sync::Arc;

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::{
    Act, Declaration, Family, KeyReadout, Likelihood, Population, PopulationError, Readout, Work,
    refuse,
};
use crate::holarchy::terrain::chase::{Caps, Chase, ChasePorts, Runner, RunnerFamily, RunnerState};
use crate::ratio::Rat;

/// [definition] **A candidate runner as a population family** (module header).
pub struct ChaseFamily {
    label: String,
    description: u64,
    index: usize,
    candidates: u64,
    runner: Runner,
    caps: Caps,
    ports: Arc<ChasePorts>,
    escape: u32,
    state: RunnerState,
    tick: usize,
    likelihood: Rat,
    reads: u64,
}

impl ChaseFamily {
    /// **The family of candidate `index`** of `candidates`, named by `description` bits, reading
    /// the ports with escape mass `2^(−escape)`; refused at an escape of zero (no mass would stay on
    /// the candidate's own letter) or past the bits a machine word's shift holds.
    pub fn new(
        ports: Arc<ChasePorts>,
        runner: Runner,
        index: usize,
        candidates: u64,
        description: u64,
        escape: u32,
    ) -> Result<Self, PopulationError> {
        if escape == 0 || escape >= 4096 {
            return Err(refuse(
                "a chase family's escape mass",
                "its exponent j gives 0 < 2^(−j) < 1",
            ));
        }
        runner.check()?;
        let caps = runner.law.caps(ports.arena.declaration())?;
        if caps.top() > ports.moves.cap() {
            return Err(refuse(
                "a chase family's alphabet",
                "it holds every change the candidate's traction admits",
            ));
        }
        let state = RunnerState::opening(&ports.arena, ports.opening.position)?;
        Ok(Self {
            label: format!("[{index}] {}", runner.label()),
            description,
            index,
            candidates,
            runner,
            caps,
            state,
            ports,
            escape,
            tick: 0,
            likelihood: Rat::one(),
            reads: 0,
        })
    }

    /// **Every candidate of the family** over a chase's ports, each named by the family's
    /// `⌈log₂ N⌉` bits, in the family's order.
    pub fn declare(
        chase: &Chase,
        family: &RunnerFamily,
        escape: u32,
    ) -> Result<Vec<Box<dyn Family>>, PopulationError> {
        Self::declare_on(&chase.ports, family, escape)
    }

    /// **Every candidate of the family** over a chase's ports, read as the chaser writes its port
    /// (the action phase: the machine's own population, `receiver::population::chaser`).
    pub fn declare_on(
        ports: &Arc<ChasePorts>,
        family: &RunnerFamily,
        escape: u32,
    ) -> Result<Vec<Box<dyn Family>>, PopulationError> {
        let description = family.description();
        (0..family.len())
            .map(|index| {
                Ok(Box::new(Self::new(
                    Arc::clone(ports),
                    family.candidate(index)?,
                    index,
                    family.len() as u64,
                    description,
                    escape,
                )?) as Box<dyn Family>)
            })
            .collect()
    }

    pub fn runner(&self) -> &Runner {
        &self.runner
    }

    /// The candidate's index in its family.
    pub fn index(&self) -> usize {
        self.index
    }

    /// **The candidate's own letter** at the current tick.
    fn own(&self) -> Result<usize, PopulationError> {
        let chaser = self.ports.chaser.get(self.tick).ok_or_else(|| {
            refuse(
                "a chase family's reading",
                "the pursuer's port holds the current tick",
            )
        })?;
        Ok(self.runner.cell(
            &self.ports.arena,
            &self.ports.moves,
            &self.caps,
            &self.state,
            chaser.position,
            self.tick as u64,
        )?)
    }

    /// The escape mass `η = 2^(−j)`.
    fn eta(&self) -> Rat {
        Rat::new(BigInt::one(), BigInt::one() << self.escape)
    }

    /// The face of `cell` when the candidate's own letter is `own`.
    fn face_of(&self, own: usize, cell: usize) -> Rat {
        let eta = self.eta();
        if cell == own {
            Rat::one() - eta
        } else {
            eta / Rat::from_integer(BigInt::from(self.ports.moves.alphabet() - 1))
        }
    }
}

impl super::Sealed for ChaseFamily {}

impl Family for ChaseFamily {
    fn label(&self) -> String {
        self.label.clone()
    }

    fn alphabet(&self) -> usize {
        self.ports.moves.alphabet()
    }

    fn description(&self) -> u64 {
        self.description
    }

    fn face(&self) -> Result<Vec<Rat>, PopulationError> {
        let own = self.own()?;
        Ok((0..self.alphabet())
            .map(|cell| self.face_of(own, cell))
            .collect())
    }

    fn receive(&mut self, cell: usize) -> Result<Rat, PopulationError> {
        let alphabet = self.alphabet();
        if cell >= alphabet {
            return Err(PopulationError::CellOutside { cell, alphabet });
        }
        let own = self.own()?;
        let face = self.face_of(own, cell);
        self.reads += 1;
        self.state =
            self.runner
                .receive(&self.ports.arena, &self.ports.moves, &self.state, cell)?;
        self.tick += 1;
        self.likelihood *= &face;
        Ok(face)
    }

    /// A passage of the alphabet's cells that stays within the pursuer's port.
    fn admits(&self, cells: &[usize]) -> Result<(), PopulationError> {
        let alphabet = self.alphabet();
        if let Some(&cell) = cells.iter().find(|&&cell| cell >= alphabet) {
            return Err(PopulationError::CellOutside { cell, alphabet });
        }
        if self.tick + cells.len() > self.ports.chaser.len() {
            return Err(refuse(
                "a chase family's passage",
                "it stays within the ticks the pursuer's port holds",
            ));
        }
        Ok(())
    }

    fn likelihood(&self) -> Likelihood {
        Likelihood::Exact(self.likelihood.clone())
    }

    /// The candidate as the one surviving key of its family's space.
    fn readout(&self) -> Readout {
        Readout::Keys(KeyReadout {
            spaces: vec![self.candidates],
            survivors: vec![vec![vec![self.index as u64]]],
            masses: Vec::new(),
            dormant: Vec::new(),
        })
    }

    /// The candidate's index, its speed and traction as numerator and denominator, its hold, its
    /// navigator's code and the escape exponent.
    fn declaration(&self) -> Declaration {
        let part = |value: &BigInt| u64::try_from(value).unwrap_or(u64::MAX);
        let law = &self.runner.law;
        let [kind, parameter] = self.runner.evasion.code();
        Declaration::new(
            "chase runner",
            vec![
                self.index as u64,
                part(law.speed.numer()),
                part(law.speed.denom()),
                part(law.traction.numer()),
                part(law.traction.denom()),
                self.runner.hold,
                kind,
                parameter,
                u64::from(self.escape),
            ],
        )
    }

    /// One candidate letter read against each received cell.
    fn work(&self) -> Work {
        let mut work = Work::default();
        work.add(Act::Read, self.reads);
        work
    }
}

/// **The population's selected fibre** (module header): the living families of exact likelihood
/// whose charged mass `π_f L_f` is the greatest, ascending; empty when none is positive.
pub fn selected_fibre(population: &Population) -> Vec<usize> {
    let masses: Vec<Option<Rat>> = population
        .families()
        .enumerate()
        .map(
            |(f, family)| match (family.likelihood(), population.prior(f)) {
                (Likelihood::Exact(value), Some(prior)) if population.died(f).is_none() => {
                    Some(prior * value)
                }
                _ => None,
            },
        )
        .collect();
    let Some(greatest) = masses.iter().flatten().max().cloned() else {
        return Vec::new();
    };
    if greatest.is_zero() {
        return Vec::new();
    }
    masses
        .iter()
        .enumerate()
        .filter(|(_, mass)| mass.as_ref() == Some(&greatest))
        .map(|(f, _)| f)
        .collect()
}
