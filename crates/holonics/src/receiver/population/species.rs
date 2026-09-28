//! **Species collapse relative to the admitted future** (`docs/ELEMENTARY_OBJECTS.md`, "The egg": a
//! species is the class of eggs every admitted future receiver reads alike, the face map's quotient
//! over generators; #73; Lean `Compression/Landmark/Context/Evolution.{species_mixture, species_face,
//! species_collapse_code, species_split}`).
//!
//! [definition; agent-inferred] **The admitted future** ([`AdmittedFuture`]) is the receiver's
//! reading of the cells at each admitted tick: the next `h` ticks, or every future tick. Two surviving
//! keys of a family are **one species** when their conditioned faces agree for every admitted
//! receiver over it: a deterministic key's face at a tick is one on the class it emits, so two keys
//! are one species exactly when they emit one class at every admitted tick of every admitted passage.
//! The check is exact, over the key space's own declaration ([`super::Emitters::signature`]):
//! - a key whose clock winds without the cells emits a word read ahead of the current tick: over `h`
//!   ticks the word of `h` classes, over the whole future one least period of its declared period
//!   (two periodic words agree forever exactly when their least periods and one period's words
//!   agree);
//! - a rotor key's next class depends on the cell before it, so its signature is its whole
//!   transition table over its rotor's period (the stage a tick reads, the cell it steps from, the
//!   class it emits), sufficient for every future passage;
//! - a key space with neither declares no check, and its family does not collapse.
//!
//! The kernel of the linear face map (Lean `Compression/Core/FaceMap`) is the same quotient where the
//! family is linear; the key families here are not (a sheet is a threshold of a phase), so their
//! check is the exact word.
//!
//! [proved-derived; formal-checked] **The collapse changes no code for the admitted future.** One
//! member a species, carrying the summed posterior `W_s = Σ_(σ k = s) w_k` (a survivor family's:
//! its members' count), gives the population's face at every admitted tick and its product over every
//! admitted passage (Lean `species_face`, `species_collapse_code`): a factor's face counts each
//! held key by its members, and its likelihood `#S/|K|` is its members' count, both unchanged. The
//! receipt ([`Collapse`]) keeps every member's seed; a collapsed family refuses a cell past the
//! admitted future (its species are certified only over it), and [`super::Population::split`]
//! restores every member of a surviving species at its share (`species_split`: within the admitted
//! future a member's posterior is its species' times its prior share), so a wider admitted future
//! can collapse again and split what the narrower one merged. A species dies whole: its members agree
//! on every admitted tick, so a split restores exactly the members still alive.
//!
//! [proved-derived; formal-checked] **Its place in the retention contract**
//! ([objects §8](../../../../../docs/ELEMENTARY_OBJECTS.md#the-retention-contract), which owns the
//! contract; U2). The collapse is the standing law's instance through the keys' exact signatures:
//! Lean `Context/Evolution.species_collapse_standing` proves that the retention `(t, W)`, the tick and
//! each species' summed weight, is a `Foundation/Standing.StandingLaw` of the key family for every
//! cell word (a cell past the admitted future refused), reopened by the collapsed family. Every word
//! a release commits is a cell word, so the future is action-sufficient. Its recoverability
//! condition holds by construction: the receipt keeps every member's seed and share, and a split
//! restores them (`species_split`).
//!
//! [definition; agent-inferred] **Within a composed egg** (`Composed`) the keystone's surviving
//! keys are one species when their conditioned families are certain over the admitted future with one
//! signature (each factor's held keys share one signature, so the family gives face one on one class
//! at every admitted tick of every admitted passage it survives): the representative's family is kept
//! at the summed weight, and each member's seed (its key, its weight share within the species, its
//! conditioned family's held keys) stays in the receipt. Every conditioned family also collapses its
//! own keys. A conditioned family that holds state along its port (the carry egg) is never certain, so
//! its keystone keys stay apart.
//!
//! [definition] Of the winding guide's six objects this owner touches the **helix** (a key's clock
//! winding through the admitted future, read ahead) and **faces and placement** (the population's
//! face, unchanged); the tube, pair, cell holonomy and tower thread stay attached.

use std::collections::{BTreeMap, HashMap};

use num_bigint::BigInt;

use super::{KeyFamily, PopulationError, Survivors, refuse};
use crate::ratio::Rat;

/// [definition] **The admitted future** (module header): the next `h` ticks, or every future tick.
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum AdmittedFuture {
    Ticks(u64),
    Whole,
}

impl AdmittedFuture {
    /// The tick the future ends at, read from the current tick (none: it never ends).
    pub fn end(self, tick: u64) -> Option<u64> {
        match self {
            AdmittedFuture::Ticks(ticks) => Some(tick + ticks),
            AdmittedFuture::Whole => None,
        }
    }
}

/// The earlier of two ends (none: never).
pub(crate) fn earliest(a: Option<u64>, b: Option<u64>) -> Option<u64> {
    match (a, b) {
        (Some(a), Some(b)) => Some(a.min(b)),
        (end, None) | (None, end) => end,
    }
}

/// [definition] **One species of a key factor**: its representative (the least member key), every
/// member with its own members (one each unless an earlier collapse merged it), each member's
/// coordinates in the family's layout, and the species' posterior within the factor.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Species {
    pub representative: u64,
    pub members: Vec<(u64, u64)>,
    pub coordinates: Vec<Vec<u64>>,
    pub posterior: Rat,
}

/// [definition] **A factor's collapse**: the keys it held before, its species, and the admitted
/// future's end before the collapse (restored at a split).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct FactorSpecies {
    pub before: usize,
    pub species: Vec<Species>,
    pub until: Option<u64>,
}

/// [definition] **A key family's seed**: the keys it holds, per factor with each key's members, its
/// clock's reading and its admitted future's end.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Seed {
    pub keys: Vec<Vec<(u64, u64)>>,
    pub tick: u64,
    pub until: Option<u64>,
}

/// [definition] **One member of a keystone's species**: its key, its members, its weight share
/// within the species (`w_k/W_s`, exact), and its conditioned family's seed (none for a family that
/// holds no keys).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KeystoneMember {
    pub key: u64,
    pub members: u64,
    pub share: Rat,
    pub seed: Option<Seed>,
}

/// [definition] **One species of a composed egg's keystone keys** (module header): its
/// representative, every member, and the species' posterior (the summed weight).
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KeystoneSpecies {
    pub representative: u64,
    pub members: Vec<KeystoneMember>,
    pub posterior: Rat,
}

/// [definition] **A collapse's receipt** (module header): a key family's species per factor, or a
/// composed egg's keystone species with each surviving key's own collapse; each with the admitted
/// future it was read over.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Collapse {
    Keys {
        future: AdmittedFuture,
        factors: Vec<FactorSpecies>,
    },
    Composed {
        future: AdmittedFuture,
        keystone: Vec<KeystoneSpecies>,
        conditioned: Vec<(u64, Collapse)>,
        /// The composed egg's admitted future's end before the collapse.
        until: Option<u64>,
        /// The cells the composed egg had received at the collapse.
        ticks: u64,
    },
}

impl Collapse {
    /// **The members before** a collapse: the keys held (a key family's per factor, multiplied;
    /// a composed egg's keystone keys).
    pub fn before(&self) -> usize {
        match self {
            Collapse::Keys { factors, .. } => factors.iter().map(|factor| factor.before).product(),
            Collapse::Composed { keystone, .. } => {
                keystone.iter().map(|species| species.members.len()).sum()
            }
        }
    }

    /// **The members after**: one a species (multiplied across a key family's factors).
    pub fn after(&self) -> usize {
        match self {
            Collapse::Keys { factors, .. } => {
                factors.iter().map(|factor| factor.species.len()).product()
            }
            Collapse::Composed { keystone, .. } => keystone.len(),
        }
    }
}

/// **A factor's species**: the held keys' indices grouped by signature, each group ascending, the
/// groups ordered by their least key. Refused when a key's emitters declare no exact check.
fn group(factor: &Survivors, future: AdmittedFuture) -> Result<Vec<Vec<usize>>, PopulationError> {
    let keys = factor.survivors();
    let mut groups: BTreeMap<Vec<usize>, Vec<usize>> = BTreeMap::new();
    for (index, &key) in keys.iter().enumerate() {
        let signature = factor.emitters.signature(key, future).ok_or_else(|| {
            refuse(
                "a species collapse",
                "the key space declares an exact check over the admitted future",
            )
        })?;
        groups.entry(signature).or_default().push(index);
    }
    let mut groups: Vec<Vec<usize>> = groups.into_values().collect();
    groups.sort_by_key(|members| members[0]);
    Ok(groups)
}

/// **Commit a factor's species**: each species one held key at its members' count; the admitted
/// future's end moves only where a species merged keys.
fn apply(factor: &mut Survivors, groups: Vec<Vec<usize>>, future: AdmittedFuture) -> FactorSpecies {
    let (keys, members) = (factor.survivors(), factor.members());
    let total = BigInt::from(factor.count);
    let species: Vec<Species> = groups
        .iter()
        .map(|group| Species {
            representative: keys[group[0]],
            members: group.iter().map(|&i| (keys[i], members[i])).collect(),
            coordinates: group
                .iter()
                .map(|&i| factor.emitters.coordinates(keys[i]))
                .collect(),
            posterior: Rat::new(
                BigInt::from(group.iter().map(|&i| members[i]).sum::<u64>()),
                total.clone(),
            ),
        })
        .collect();
    let receipt = FactorSpecies {
        before: keys.len(),
        species: species.clone(),
        until: factor.until,
    };
    if groups.iter().any(|group| group.len() > 1) {
        let summed: Vec<u64> = species
            .iter()
            .map(|species| species.members.iter().map(|&(_, members)| members).sum())
            .collect();
        factor.members = summed.iter().any(|&members| members > 1).then_some(summed);
        factor.held = Some(
            species
                .iter()
                .map(|species| species.representative)
                .collect(),
        );
        factor.until = earliest(factor.until, future.end(factor.tick));
    }
    receipt
}

/// **Collapse a key family** (module header): every factor's species are read before any factor
/// moves, so a refusal moves nothing.
pub(super) fn collapse_keys(
    family: &mut KeyFamily,
    future: AdmittedFuture,
) -> Result<super::Collapse, PopulationError> {
    let groupings = family
        .factors
        .iter()
        .map(|factor| group(factor, future))
        .collect::<Result<Vec<_>, _>>()?;
    let factors = family
        .factors
        .iter_mut()
        .zip(groupings)
        .map(|(factor, groups)| apply(factor, groups, future))
        .collect();
    Ok(Collapse::Keys { future, factors })
}

/// **Split a key family's species** from its receipt (module header): every member of a species
/// whose representative is held returns with its own members; every factor is checked before any
/// moves.
pub(super) fn split_keys(
    family: &mut KeyFamily,
    collapse: &Collapse,
) -> Result<(), PopulationError> {
    let Collapse::Keys { factors, .. } = collapse else {
        return Err(refuse(
            "a key family's species split",
            "its receipt is a key family's collapse",
        ));
    };
    if factors.len() != family.factors.len() {
        return Err(refuse(
            "a key family's species split",
            "its receipt names every factor",
        ));
    }
    let mut restored = Vec::with_capacity(factors.len());
    for (factor, receipt) in family.factors.iter().zip(factors) {
        let by_representative: HashMap<u64, &Species> = receipt
            .species
            .iter()
            .map(|species| (species.representative, species))
            .collect();
        let mut keys: Vec<(u64, u64)> = Vec::new();
        for (key, members) in factor.survivors().into_iter().zip(factor.members()) {
            match by_representative.get(&key) {
                Some(species) => {
                    if species.members.iter().map(|&(_, m)| m).sum::<u64>() != members {
                        return Err(refuse(
                            "a key family's species split",
                            "each held species carries its receipt's members",
                        ));
                    }
                    keys.extend(&species.members);
                }
                None => keys.push((key, members)),
            }
        }
        keys.sort_unstable();
        restored.push((keys, receipt.until));
    }
    for (factor, (keys, until)) in family.factors.iter_mut().zip(restored) {
        factor.members = keys
            .iter()
            .any(|&(_, members)| members > 1)
            .then(|| keys.iter().map(|&(_, members)| members).collect());
        factor.held = Some(keys.into_iter().map(|(key, _)| key).collect());
        factor.until = until;
    }
    Ok(())
}
