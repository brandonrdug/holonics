//! **The evolved prior: a receiver's population learns its prior over families across aeons**
//! (`docs/ELEMENTARY_OBJECTS.md`, "Keys, locks and navigation": "it forgets no failure … across
//! aeons the population's prior over families learns from its own deaths and selections … a
//! retention of selection counts over families, never a tape of attempts"; #73; Lean
//! `Compression/Landmark/Context/Evolution`).
//!
//! [definition; agent-inferred] **Identity.** A family's identity across aeons is its declaration,
//! never its label: the generator family's kind and declared integers, with the declarations it is
//! built on ([`Declaration`]), and its description ([`Identity`]). A key family's declaration is its
//! key space's (a moiré's gratings by their rings, denominators and class; a rotor ring by its
//! machine); a receiving tree's is its depth, stop prior, grain and capacity, not the aeon's cell
//! alphabet (the alphabet is the receiver's chart of the aeon, and the tree reads any); a composed
//! egg's is its keystone's and its conditioned family's. A seed re-founded, or the same declaration
//! declared in a new aeon, carries the same identity.
//!
//! [definition; agent-inferred] **The retention.** Across aeons the receiver keeps, for each identity,
//! three counts read from the aeons' receipts ([`Tally`]): the aeons it was declared in `a`, selected
//! in `s` (the population's receipt selects it: its posterior decided above one half) and died in
//! `d` (every member of that identity at zero likelihood at the aeon's end). Nothing else is kept:
//! the counts are the only retained history ([`Selections`]), a future-sufficient quotient of the
//! aeons for the prior, never a list of attempts.
//!
//! [proved-derived; formal-checked] **The evolved prior** (Lean `Evolution.{dirichletFace_isPrior,
//! kt_face, evolved_isPrior, masses_total, evolved_code_le_face, evolved_code_le_description,
//! evolved_aeon_code}`). At an aeon's opening, over the declared families `F`:
//!
//! ```text
//! σ_f = (2(a_f − d_f) + 1)/(2(2a_f + 1))                    the survival pseudo-count, in (0, ½]
//! D(f) = (s_f + σ_f)/Σ_(g∈F) (s_g + σ_g)                    the Dirichlet face of the selections
//! π(f) = λ D(f) + (1 − λ) 2^(−ℓ_f)/M,   M = Σ_(g∈F) 2^(−ℓ_g)  λ ∈ [0, 1] declared
//! m_f = M π(f),   Σ_f m_f = M                               the declared masses; 1 − M reserved
//! −log₂ W ≤ −log₂ π(f) − log₂ L_f                           every living f, an aeon without births
//! −log₂ π(f) ≤ −log₂ λ − log₂ D(f),   −log₂ π(f) ≤ −log₂(1 − λ) + ℓ_f + log₂ M
//! ```
//!
//! [proved-derived; formal-checked] **The aeon's code bound with births.** A birth draws its mass `m_g` from the
//! reserve and renormalizes every prior over the founded mass `M_n = M + Σ_g m_g` (the population's
//! "Birth from reserved mass"), so a declared family's prior at `n` is `m_f/M_n = π(f) M/M_n`, and
//! over an aeon with births the bound is
//!
//! ```text
//! −log₂ W_n ≤ −log₂(m_f/M_n) − log₂ L_f = −log₂ π(f) + log₂(M_n/M) − log₂ L_f     every living declared f
//! ```
//!
//! (the birth telescope, Lean `Compression/Landmark/Context/Evolution.evolved_code_with_births`,
//! through the abstaining newborn's `founded_code`).
//! `evolved_aeon_code` proves the no-birth form (`M_n = M`). The no-birth form does not hold across
//! a birth: when every newborn dies, `W_n = Σ_f m_f L_f/M_n`, and the code exceeds it by up to
//! `log₂(M_n/M)` (one family at `M = ½, π = 1` and a newborn of mass `¼` that dies at the next
//! cell: the excess is `log₂(3/2)`, the test
//! `the_evolved_aeon_bound_with_a_birth_is_over_the_founded_mass`).
//!
//! With no deaths `σ = ½` and `D` is the Krichevsky–Trofimov (Dirichlet-½) face of the selection
//! counts; each death thins the pseudo-count (`survivalPseudo_death_lt`), so a family that keeps
//! winning is founded sooner and one that keeps dying later. [agent-inferred] Survival without
//! selection is no evidence for a family (every receiving tree survives every aeon), so only deaths
//! thin `σ`. The masses keep the static population's total `M`, so the reserve a birth draws from is
//! unchanged, and a candidate is founded at its evolved mass with
//! [`Population::found_with`]. [agent-inferred] The declared weight is `λ = ½`: the mixture then
//! costs at most one bit against the better of the Dirichlet face and the description prior, so a
//! family the counts have not yet seen is never charged more than one bit above its description.
//!
//! [definition] The computational object is the helical pair interaction read as a receiver's
//! population of eggs across aeons. Of the winding guide's six general objects this owner touches the
//! **tube** (the aeons, each a span whose receipt adds one count) and **faces and placement** (the
//! evolved prior on the declared families); the helix, pair, cell holonomy and tower thread stay
//! attached through the families' own owners.

use std::collections::{BTreeMap, BTreeSet};

use num_bigint::BigInt;
use num_traits::{One, Zero};

use super::{Family, Population, PopulationError, PopulationReceipt, kraft, refuse};
use crate::ratio::Rat;

/// [definition; agent-inferred] **A declaration** (module header, "Identity"): the generator
/// family's kind, its declared integers and the declarations it is built on.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Declaration {
    pub kind: &'static str,
    pub parameters: Vec<u64>,
    pub parts: Vec<Declaration>,
}

impl Declaration {
    /// A declaration of a kind and its integers.
    pub fn new(kind: &'static str, parameters: Vec<u64>) -> Self {
        Self {
            kind,
            parameters,
            parts: Vec::new(),
        }
    }

    /// The declaration built on `parts`.
    pub fn with(mut self, parts: Vec<Declaration>) -> Self {
        self.parts = parts;
        self
    }
}

/// [definition] **A family's identity across aeons**: its declaration and its description.
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub struct Identity {
    pub declaration: Declaration,
    pub description: u64,
}

/// [definition] **One identity's counts** (module header, "The retention"): the aeons it was
/// declared, selected and died in.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct Tally {
    pub declared: u64,
    pub selected: u64,
    pub died: u64,
}

impl Tally {
    /// **The survival pseudo-count** `σ = (2(a − d) + 1)/(2(2a + 1))`, in `(0, ½]`.
    pub fn pseudo(&self) -> Rat {
        let survived = self.declared.saturating_sub(self.died);
        Rat::new(
            BigInt::from(2 * survived + 1),
            BigInt::from(2 * (2 * self.declared + 1)),
        )
    }
}

/// [definition; agent-inferred] **The retention of selection counts** (module header): each
/// identity's [`Tally`] and the aeons read.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Selections {
    tallies: BTreeMap<Identity, Tally>,
    aeons: u64,
}

impl Selections {
    /// No aeon read yet.
    pub fn new() -> Self {
        Self::default()
    }

    /// The aeons read.
    pub fn aeons(&self) -> u64 {
        self.aeons
    }

    /// One identity's counts (zero when never declared).
    pub fn tally(&self, identity: &Identity) -> Tally {
        self.tallies.get(identity).copied().unwrap_or_default()
    }

    /// Every identity's counts, in the identities' order.
    pub fn tallies(&self) -> impl Iterator<Item = (&Identity, &Tally)> {
        self.tallies.iter()
    }

    /// **Read one aeon's receipt** (module header, "The retention"): each identity declared in it
    /// counts once, selected when the selected family carries it, died when every member carrying
    /// it is dead at the aeon's end.
    pub fn record(&mut self, receipt: &PopulationReceipt) {
        let mut living: BTreeMap<&Identity, bool> = BTreeMap::new();
        for family in &receipt.families {
            *living.entry(&family.identity).or_insert(false) |= family.died.is_none();
        }
        let selected = receipt
            .selected
            .map(|index| &receipt.families[index].identity);
        for (identity, alive) in living {
            let tally = self.tallies.entry(identity.clone()).or_default();
            tally.declared += 1;
            tally.selected += u64::from(selected == Some(identity));
            tally.died += u64::from(!alive);
        }
        self.aeons += 1;
    }

    /// **The Dirichlet face of the selections** over the declared identities (module header):
    /// `D(f) = (s_f + σ_f)/Σ_g (s_g + σ_g)`, exact. Refused at an empty declaration or a repeated
    /// identity.
    pub fn face(&self, declared: &[Identity]) -> Result<Vec<Rat>, PopulationError> {
        let distinct: BTreeSet<&Identity> = declared.iter().collect();
        if declared.is_empty() || distinct.len() != declared.len() {
            return Err(refuse(
                "an evolved prior",
                "it weighs at least one declared family, each identity once",
            ));
        }
        let weights: Vec<Rat> = declared
            .iter()
            .map(|identity| {
                let tally = self.tally(identity);
                Rat::from_integer(BigInt::from(tally.selected)) + tally.pseudo()
            })
            .collect();
        let total: Rat = weights.iter().sum();
        Ok(weights.into_iter().map(|weight| weight / &total).collect())
    }

    /// **The evolved prior** over the declared identities at the declared weight `λ ∈ [0, 1]`
    /// (module header): `π(f) = λ D(f) + (1 − λ) 2^(−ℓ_f)/M`, exact, summing to one.
    pub fn prior(&self, declared: &[Identity], weight: &Rat) -> Result<Vec<Rat>, PopulationError> {
        if *weight < Rat::zero() || *weight > Rat::one() {
            return Err(refuse(
                "an evolved prior's weight",
                "it lies in the unit interval",
            ));
        }
        let face = self.face(declared)?;
        let descriptions = declared
            .iter()
            .map(|identity| kraft(identity.description))
            .collect::<Result<Vec<Rat>, _>>()?;
        let mass: Rat = descriptions.iter().sum();
        let rest = Rat::one() - weight;
        Ok(face
            .into_iter()
            .zip(descriptions)
            .map(|(dirichlet, description)| weight * dirichlet + &rest * description / &mass)
            .collect())
    }
}

impl Population {
    /// **Declare the population at an aeon's opening under the evolved prior** (module header): the
    /// declared families at masses `m_f = M π(f)`, `M = Σ_f 2^(−ℓ_f)` (the static population's total,
    /// so the reserve is unchanged), `π` the evolved prior of the retained counts at weight `λ`.
    pub fn evolved(
        families: Vec<Box<dyn Family>>,
        selections: &Selections,
        weight: &Rat,
    ) -> Result<Self, PopulationError> {
        let declared: Vec<Identity> = families.iter().map(|family| family.identity()).collect();
        let prior = selections.prior(&declared, weight)?;
        let mass = declared
            .iter()
            .map(|identity| kraft(identity.description))
            .sum::<Result<Rat, _>>()?;
        if mass > Rat::one() {
            return Err(refuse(
                "a population's descriptions",
                "their Kraft sum passes one: they are no prefix code's lengths",
            ));
        }
        let masses = prior.into_iter().map(|share| &mass * share).collect();
        Self::with_masses(families, masses)
    }
}
