//! Recover a material's codec from **exposure alone**.
//!
//! ## What this is, and what it is not
//!
//! [`holonic_engine::codec_recovery`] recovers a tokenizer from an oracle it may *call*: a boxed
//! `dyn Fn(&str) -> Vec<String>` that segments any query on demand. That instrument is exact and it
//! is driven, but its target is a function. **Real material is not a function.** A Lean source tree
//! answers no query; it is octets that happened.
//!
//! This module is the same operation with the oracle removed. The only admitted contact with the
//! material is **whether a word occurs in it**, and **whether it occurs more than once**. From that,
//! and from nothing else, the recovery returns the material's codec: which symbols stand alone,
//! which demand a continuation, which can only appear inside a unit, where the unit boundaries fall,
//! and what the material cannot distinguish.
//!
//! Brandon's framing, which fixes what the organ is allowed to know:
//!
//! > *"the units of information provided give way to complete reconstruction about the codec it was
//! > constructed with. Consider Morse code or Braille, not all beats or bumps are communication, but
//! > it's that once you identify a symbol that resonates with the units of a codec you can then begin
//! > to reconstruct what the symbols likely mean; it takes recurrence to determine that it is even
//! > language in the first place… and then simple exposure to the stimulus to collect and decode all
//! > of the information that is encoded."*
//!
//! and, in the same message, **"I am not telling you to implement a threshold."** There is no
//! threshold below. Every criterion here is a *structural* predicate — a set is empty or it is not,
//! a word occurs once or more than once, an implication holds over an exhausted family or it fails
//! with an exhibited witness. Nothing is compared against a magnitude.
//!
//! ## The declared query family, exhausted
//!
//! ```text
//!   Family(radius) = { w over the octets that occur : 1 <= |w| <= radius }
//! ```
//!
//! The alphabet itself is recovered by exhausting all **256** single-octet probes, so even the
//! alphabet is testimony rather than a declaration. The family is then exhausted, never sampled, so
//! every statement of the form *"no admitted word separates these"* is a theorem about the family.
//!
//! ## What is recovered, and by which rule
//!
//! **1. The refusal law.** A word `w` of length `k >= 2` is a **minimal refusal** when the material
//! refuses `w` while **recurring** on both of its `(k-1)`-factors. The recurrence is load-bearing and
//! it is Brandon's criterion: a factor seen once licenses nothing, so a word missing beside it is an
//! accident; a factor seen again and again licenses its neighbourhood, and a word still missing there
//! is a **rule**. The population of minimal refusals is the codec's rule set — a factorial language is
//! determined by its antidictionary — and its being **non-empty** is what establishes that there is a
//! codec at all. Uniform noise refuses nothing and the recovery says so.
//!
//! **2. The direct quotient.** Two octets are held together exactly when no admitted context
//! separates them, where a context is a family word with one hole and separation is a difference in
//! *occurrence*. This is the Nerode/Moore discipline of
//! [`holonic_engine::receiver_exact_compression`] at the finest possible grain, and on real material
//! it is **expected to return singletons**: that is a bound, not a failure, and each separated pair
//! carries the shortest context that separated it.
//!
//! **3. The unit reading.** The codec proper. Write `R(a)` for the octets that follow `a` somewhere
//! and `L(a)` for the octets that precede it. A set `C` of octets is **unit-internal** when, writing
//!
//! ```text
//!   D(C) = { x not in C : R(x) is non-empty and R(x) is contained in C }
//! ```
//!
//! for the octets every one of whose observed continuations lies in `C`, **every observed predecessor
//! of a member of `C` lies in `D(C) union C`**. In words: a unit-internal octet is never reached from
//! outside — the only way into `C` is through an octet that leads nowhere else. `D(C)` is then the
//! **demanding** class, the unit heads, and everything else **stands**: it is a unit by itself.
//!
//! The reading is computed as the downward fixed point of that condition, seeded at the octets that
//! do **not** open an exposure. Seeding is a frame, so the fixed point is taken **twice** — once from
//! the openings and once from the closings — and the two must agree. Where they disagree the reading
//! is refused by name. That is `CLAUDE.md` §0's fourth lesson used as an instrument rather than
//! quoted: *an invariant is only visible across two frames*, and the frames really do part company on
//! material whose reading is degenerate.
//!
//! **4. The boundary table and the gauge freedom.** A unit continues exactly across a unit-internal
//! octet, so `boundary[p][c] = Join` iff `c` is unit-internal, and `Cut` otherwise. The result is a
//! [`RecoveredCodec`] — the same carrier the oracle-driven organ returns — so it runs, it segments,
//! and it can be cross-checked against any other codec by
//! [`holonic_engine::codec_system::cross_check`]. Every class adjacency the material never realized
//! is returned as **gauge freedom**: flipping it changes no segmentation of this material, and the
//! shortest word that *would* separate the two readings is a word the material does not carry.
//!
//! ## What the organ is never told
//!
//! No grammar, no keyword list, no bracket table, no character classes, no encoding. It does not know
//! what Lean is, what UTF-8 is, or that its octets group at all. It is told a radius and a call
//! budget — both statements about the cpu, both declared by the caller, neither derivable from the
//! material — and nothing else.

use std::cell::Cell;
use std::collections::{BTreeMap, BTreeSet, HashMap};

use holonic_engine::codec_recovery::{Boundary, Emission, RecoveredCodec, Symbol, SymbolAlphabet};
use serde::{Deserialize, Serialize};

const RECOVERY_SCHEMA: &str = "life.exposure-codec-recovery.v1";
const CODEC_SCHEMA: &str = "holonic-engine.recovered-symbol-codec.v1";

// -------------------------------------------------------------------------------------------------
// The apertures
// -------------------------------------------------------------------------------------------------

/// The resource apertures one exposure recovery runs under, **declared by the caller**.
///
/// There is deliberately no `Default`. Neither number is derivable from the material — the radius is
/// how far this cpu can afford to look and the word budget is how many words it can afford to ask —
/// so neither is the organ's to pick. Past either, the recovery refuses by name and reports the width
/// the material required. `canon/THE_AUTHORED_LEVEL.md` §5.2 is the precedent: the same two levels
/// moved out of `codec_recovery` for the same reason.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
pub struct ExposureApertures {
    /// The longest word the recovery may ask about. Must reach two, or no adjacency is admitted.
    pub radius: usize,
    /// The largest declared query family this recovery may exhaust.
    pub family_words: u64,
}

impl ExposureApertures {
    /// Declare both. Named rather than constructed field-wise so a call site reads as a declaration.
    pub const fn declared(radius: usize, family_words: u64) -> Self {
        Self {
            radius,
            family_words,
        }
    }
}

// -------------------------------------------------------------------------------------------------
// The material, as a black box
// -------------------------------------------------------------------------------------------------

/// The exposed material.
///
/// It holds octets and answers four questions about them. There is no accessor for the octets, no
/// iterator over the exposures, and the [`std::fmt::Debug`] shows only how many contacts have been
/// made. The recovery below holds one of these and can do exactly what this surface permits.
pub struct ExposedMaterial {
    exposures: Vec<Vec<u8>>,
    /// Every factor up to the exposed radius, packed, carrying `1` for *occurred once* and `2` for
    /// *recurred*. Built once from the octets; it is the material's own testimony, indexed.
    factors: HashMap<u64, u8>,
    openings: BTreeSet<u8>,
    closings: BTreeSet<u8>,
    radius: usize,
    contacts: Cell<u64>,
    deep_scans: Cell<u64>,
}

/// The width of the packing carrier, read off `u64` rather than authored: one octet of length and
/// seven of word.
const fn packing_radius() -> usize {
    (u64::BITS as usize / 8) - 1
}

fn pack(word: &[u8]) -> u64 {
    let mut key = (word.len() as u64) << 56;
    for (position, octet) in word.iter().enumerate() {
        key |= (*octet as u64) << (48 - 8 * position);
    }
    key
}

impl ExposedMaterial {
    /// Expose a population of octet streams and index every factor up to `radius`.
    ///
    /// Exposures are separate streams: **no word crosses an exposure boundary**, because two files
    /// are not one file, and a codec recovered across the seam would have been recovered from an
    /// artifact of the concatenation order.
    pub fn expose(exposures: Vec<Vec<u8>>, radius: usize) -> Result<Self, ExposureRefusal> {
        if radius < 2 {
            return Err(ExposureRefusal::RadiusBelowAdjacency { radius });
        }
        if radius > packing_radius() {
            return Err(ExposureRefusal::RadiusExceedsCarrier {
                radius,
                carrier_radius: packing_radius(),
            });
        }
        let exposures: Vec<Vec<u8>> = exposures.into_iter().filter(|e| !e.is_empty()).collect();
        if exposures.is_empty() {
            return Err(ExposureRefusal::NoExposure);
        }
        let mut factors: HashMap<u64, u8> = HashMap::new();
        let mut openings = BTreeSet::new();
        let mut closings = BTreeSet::new();
        for exposure in &exposures {
            openings.insert(exposure[0]);
            closings.insert(exposure[exposure.len() - 1]);
            for start in 0..exposure.len() {
                let reach = radius.min(exposure.len() - start);
                for length in 1..=reach {
                    let slot = factors
                        .entry(pack(&exposure[start..start + length]))
                        .or_insert(0);
                    if *slot < 2 {
                        *slot += 1;
                    }
                }
            }
        }
        Ok(Self {
            exposures,
            factors,
            openings,
            closings,
            radius,
            contacts: Cell::new(0),
            deep_scans: Cell::new(0),
        })
    }

    fn contact(&self) {
        self.contacts.set(self.contacts.get().saturating_add(1));
    }

    /// The number of times this word was seen, saturating at two. The one primitive; everything else
    /// on this surface reads it.
    fn sightings(&self, word: &[u8]) -> u8 {
        self.contact();
        if word.is_empty() {
            return 0;
        }
        if word.len() <= self.radius {
            return self.factors.get(&pack(word)).copied().unwrap_or(0);
        }
        // A word past the exposed radius is still a lawful question; it costs a scan, and the scan is
        // counted separately so a recovery that wanders past its declared family cannot hide it.
        self.deep_scans.set(self.deep_scans.get().saturating_add(1));
        let mut seen = 0u8;
        for exposure in &self.exposures {
            if exposure.len() < word.len() {
                continue;
            }
            for start in 0..=exposure.len() - word.len() {
                if &exposure[start..start + word.len()] == word {
                    seen += 1;
                    if seen >= 2 {
                        return 2;
                    }
                }
            }
        }
        seen
    }

    /// Does this word occur in the material at all.
    pub fn occurs(&self, word: &[u8]) -> bool {
        self.sightings(word) >= 1
    }

    /// Does this word occur **more than once**. Recurrence, in the only sense the word has: it
    /// happened again. This is not a threshold and no other multiplicity is available from this
    /// surface — the counter saturates at two, so nothing downstream can rank by it.
    pub fn recurs(&self, word: &[u8]) -> bool {
        self.sightings(word) >= 2
    }

    /// Does some exposure begin with this octet.
    pub fn opens(&self, octet: u8) -> bool {
        self.contact();
        self.openings.contains(&octet)
    }

    /// Does some exposure end with this octet.
    pub fn closes(&self, octet: u8) -> bool {
        self.contact();
        self.closings.contains(&octet)
    }

    /// How many contacts have been made. A cost, reported rather than optimised away.
    pub fn contacts(&self) -> u64 {
        self.contacts.get()
    }

    /// How many contacts fell outside the exposed radius and cost a scan.
    pub fn deep_scans(&self) -> u64 {
        self.deep_scans.get()
    }

    /// The total octets exposed. A statement about the exposure, not about the recovery.
    pub fn extent(&self) -> u64 {
        self.exposures.iter().map(|e| e.len() as u64).sum()
    }

    /// How many separate streams were exposed.
    pub fn exposure_count(&self) -> usize {
        self.exposures.len()
    }
}

impl std::fmt::Debug for ExposedMaterial {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        formatter
            .debug_struct("ExposedMaterial")
            .field("contacts", &self.contacts.get())
            .field("deep_scans", &self.deep_scans.get())
            .finish_non_exhaustive()
    }
}

// -------------------------------------------------------------------------------------------------
// The returned structure
// -------------------------------------------------------------------------------------------------

/// The role an octet plays in the recovered codec.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum UnitRole {
    /// The octet is a unit by itself. It opens a unit and closes it.
    Standing,
    /// Every observed continuation of this octet is unit-internal, so it heads a longer unit.
    Demanding,
    /// The octet is never reached from outside a unit. It can only appear inside one.
    Internal,
}

impl UnitRole {
    pub const fn name(self) -> &'static str {
        match self {
            Self::Standing => "standing",
            Self::Demanding => "demanding",
            Self::Internal => "internal",
        }
    }
}

/// One minimal refusal: a word the material's own **recurring** factors license and the material
/// still refuses.
///
/// This is the artifact of the rule set, and it carries the two factors that licensed it so the
/// refusal can be read without consulting the material again.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct MinimalRefusal {
    pub word: Vec<u8>,
    /// The recurring prefix that licensed the left of it.
    pub licensing_prefix: Vec<u8>,
    /// The recurring suffix that licensed the right of it.
    pub licensing_suffix: Vec<u8>,
}

/// Why two octets are in different blocks of the direct quotient: the shortest admissible context
/// that separated them, and which side occurred there.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct OctetSeparation {
    pub left: u8,
    pub right: u8,
    pub prefix: Vec<u8>,
    pub suffix: Vec<u8>,
    /// Whether the left octet's word occurred in that context.
    pub left_occurs: bool,
    /// Whether the right octet's word occurred in that context.
    pub right_occurs: bool,
}

impl OctetSeparation {
    pub fn context_length(&self) -> usize {
        self.prefix.len() + 1 + self.suffix.len()
    }
}

/// What one length of the declared family returned.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
pub struct LengthCensus {
    pub length: usize,
    /// Words the family admits at this length.
    pub admitted: u64,
    /// Words that occur.
    pub realized: u64,
    /// Words that occur **more than once**.
    pub recurring: u64,
    /// Words the material's recurring factors license and the material refuses.
    pub refused: u64,
}

/// One frame's reading of the unit roles, before the frames are compared.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct FrameReading {
    /// What seeded the downward fixed point.
    pub frame: String,
    pub internal: BTreeSet<u8>,
    pub demanding: BTreeSet<u8>,
    pub standing: BTreeSet<u8>,
    /// How many removal rounds the fixed point took. A cost, exact.
    pub rounds: u64,
}

/// A returned obstruction. Each carries the material that produced it; none is an error.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub enum ExposureObstruction {
    /// The material refuses nothing its own recurring factors license. There is no rule to recover;
    /// this is what uniform noise returns and it is the negative control of the whole operation.
    NothingIsRefused { radius: usize },
    /// No word of length two or more recurs. Nothing happened twice, so nothing was established.
    NothingRecurs { radius: usize },
    /// The two seeding frames returned different readings. A reading that depends on which end of the
    /// exposure it was seeded from is a coordinate, not an invariant, and it is refused.
    FramesDisagree {
        opening: FrameReading,
        closing: FrameReading,
    },
    /// Every octet came back unit-internal, so nothing stands and the reading founds no unit at all.
    NothingStands { internal: u64, demanding: u64 },
}

/// What the recovery cost, in exact counts. No clock appears anywhere in this module.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExposureWork {
    /// The 256 probes that recovered the alphabet.
    pub alphabet_probes: u64,
    pub declared_family_words: u64,
    pub material_contacts: u64,
    pub deep_scans: u64,
    pub contexts_examined: u64,
    pub refusal_checks: u64,
    pub fixed_point_rounds: u64,
}

/// What an exposure recovery returns.
#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ExposureRecovery {
    pub schema: String,
    pub radius: usize,
    pub alphabet: Vec<u8>,
    pub census: Vec<LengthCensus>,
    /// Every minimal refusal, at every length. The codec's rule set.
    pub refusals: Vec<MinimalRefusal>,
    /// The finest quotient the family admits: two octets share a block only when no admitted context
    /// separates them.
    pub direct_quotient: Vec<BTreeSet<u8>>,
    /// Every pair the direct quotient separated, with the shortest context that did it.
    pub direct_separations: Vec<OctetSeparation>,
    pub opening_frame: FrameReading,
    pub closing_frame: FrameReading,
    /// The role of every octet, present only when the frames agreed.
    pub roles: BTreeMap<u8, UnitRole>,
    /// The codec, present exactly when `obstructions` is empty.
    pub codec: Option<RecoveredCodec>,
    /// The class adjacencies the material never realized. Their boundary entries are free: flipping
    /// one changes no segmentation of this material.
    pub gauge_freedom: Vec<(UnitRole, UnitRole)>,
    pub obstructions: Vec<ExposureObstruction>,
    pub work: ExposureWork,
}

impl ExposureRecovery {
    pub fn is_recovered(&self) -> bool {
        self.codec.is_some()
    }

    /// The octets carrying one role, in canonical order.
    pub fn octets_with(&self, role: UnitRole) -> Vec<u8> {
        self.roles
            .iter()
            .filter(|(_, carried)| **carried == role)
            .map(|(octet, _)| *octet)
            .collect()
    }
}

/// Why a recovery could not begin. Distinct from an obstruction: an obstruction is a return.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ExposureRefusal {
    NoExposure,
    RadiusBelowAdjacency {
        radius: usize,
    },
    RadiusExceedsCarrier {
        radius: usize,
        carrier_radius: usize,
    },
    FamilyExceedsAperture {
        words: u64,
        aperture: u64,
    },
    /// The material and the recovery were exposed at different radii, so the family the recovery
    /// declares is not the family the material indexed.
    RadiusDisagreesWithExposure {
        exposed: usize,
        declared: usize,
    },
}

impl std::fmt::Display for ExposureRefusal {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NoExposure => write!(formatter, "no non-empty exposure was supplied"),
            Self::RadiusBelowAdjacency { radius } => write!(
                formatter,
                "a radius of {radius} admits no adjacency; the family must reach two-octet words"
            ),
            Self::RadiusExceedsCarrier {
                radius,
                carrier_radius,
            } => write!(
                formatter,
                "a radius of {radius} exceeds the {carrier_radius}-octet packing carrier"
            ),
            Self::FamilyExceedsAperture { words, aperture } => write!(
                formatter,
                "the declared family holds {words} words, past the {aperture}-word aperture"
            ),
            Self::RadiusDisagreesWithExposure { exposed, declared } => write!(
                formatter,
                "the material was exposed at radius {exposed} and the recovery declares {declared}"
            ),
        }
    }
}

impl std::error::Error for ExposureRefusal {}

// -------------------------------------------------------------------------------------------------
// The recovery
// -------------------------------------------------------------------------------------------------

/// Recover the material's codec from exposure alone.
pub fn recover(
    material: &ExposedMaterial,
    apertures: ExposureApertures,
) -> Result<ExposureRecovery, ExposureRefusal> {
    if apertures.radius < 2 {
        return Err(ExposureRefusal::RadiusBelowAdjacency {
            radius: apertures.radius,
        });
    }
    if apertures.radius != material.radius {
        return Err(ExposureRefusal::RadiusDisagreesWithExposure {
            exposed: material.radius,
            declared: apertures.radius,
        });
    }
    let radius = apertures.radius;

    // 1. The alphabet, by exhausting every octet value. Even the alphabet is testimony.
    let mut alphabet: Vec<u8> = Vec::new();
    for value in 0u16..=255 {
        let octet = value as u8;
        if material.occurs(&[octet]) {
            alphabet.push(octet);
        }
    }
    let symbols = alphabet.len() as u64;
    let mut work = ExposureWork {
        alphabet_probes: 256,
        ..ExposureWork::default()
    };
    if alphabet.is_empty() {
        return Err(ExposureRefusal::NoExposure);
    }

    // The family's exact size before a single word is asked.
    let mut admitted_total: u64 = 0;
    let mut per_length: Vec<u64> = Vec::with_capacity(radius);
    let mut power: u64 = 1;
    for _ in 1..=radius {
        power = match power.checked_mul(symbols) {
            Some(next) => next,
            None => {
                return Err(ExposureRefusal::FamilyExceedsAperture {
                    words: u64::MAX,
                    aperture: apertures.family_words,
                })
            }
        };
        per_length.push(power);
        admitted_total = match admitted_total.checked_add(power) {
            Some(next) => next,
            None => {
                return Err(ExposureRefusal::FamilyExceedsAperture {
                    words: u64::MAX,
                    aperture: apertures.family_words,
                })
            }
        };
    }
    if admitted_total > apertures.family_words {
        return Err(ExposureRefusal::FamilyExceedsAperture {
            words: admitted_total,
            aperture: apertures.family_words,
        });
    }
    work.declared_family_words = admitted_total;

    // 2. The census and the refusal law, over the exhausted family.
    let mut census: Vec<LengthCensus> = Vec::with_capacity(radius);
    let mut refusals: Vec<MinimalRefusal> = Vec::new();
    // The adjacency, kept because every later step reads it and the family already paid for it.
    let mut follows: BTreeMap<u8, BTreeSet<u8>> = BTreeMap::new();
    let mut precedes: BTreeMap<u8, BTreeSet<u8>> = BTreeMap::new();
    let mut word = vec![0u8; radius];
    for length in 1..=radius {
        let admitted = per_length[length - 1];
        let mut realized = 0u64;
        let mut recurring = 0u64;
        let mut refused = 0u64;
        for ordinal in 0..admitted {
            let mut rest = ordinal;
            for position in (0..length).rev() {
                word[position] = alphabet[(rest % symbols) as usize];
                rest /= symbols;
            }
            let here = &word[..length];
            let sightings = material.sightings(here);
            if sightings >= 1 {
                realized += 1;
                if length == 2 {
                    follows.entry(here[0]).or_default().insert(here[1]);
                    precedes.entry(here[1]).or_default().insert(here[0]);
                }
            }
            if sightings >= 2 {
                recurring += 1;
            }
            if sightings == 0 && length >= 2 {
                work.refusal_checks += 1;
                let prefix = &here[..length - 1];
                let suffix = &here[1..];
                if material.recurs(prefix) && material.recurs(suffix) {
                    refused += 1;
                    refusals.push(MinimalRefusal {
                        word: here.to_vec(),
                        licensing_prefix: prefix.to_vec(),
                        licensing_suffix: suffix.to_vec(),
                    });
                }
            }
        }
        census.push(LengthCensus {
            length,
            admitted,
            realized,
            recurring,
            refused,
        });
    }

    // 3. The direct quotient. Contexts shortest first, so a recorded separator is the shortest one.
    let (direct_quotient, direct_separations, contexts) =
        direct_quotient(material, &alphabet, radius);
    work.contexts_examined = contexts;

    // 4. The unit reading, taken in two frames.
    let openings: BTreeSet<u8> = alphabet
        .iter()
        .copied()
        .filter(|octet| material.opens(*octet))
        .collect();
    let closings: BTreeSet<u8> = alphabet
        .iter()
        .copied()
        .filter(|octet| material.closes(*octet))
        .collect();
    let opening_frame = unit_reading(
        &alphabet,
        &follows,
        &precedes,
        &openings,
        "exposure-openings",
    );
    let closing_frame = unit_reading(
        &alphabet,
        &follows,
        &precedes,
        &closings,
        "exposure-closings",
    );
    work.fixed_point_rounds = opening_frame.rounds + closing_frame.rounds;

    // 5. The obstructions, in the order a reader needs them.
    let mut obstructions: Vec<ExposureObstruction> = Vec::new();
    if census.iter().skip(1).all(|row| row.recurring == 0) {
        obstructions.push(ExposureObstruction::NothingRecurs { radius });
    }
    if census.iter().all(|row| row.refused == 0) {
        obstructions.push(ExposureObstruction::NothingIsRefused { radius });
    }
    let frames_agree = opening_frame.internal == closing_frame.internal
        && opening_frame.demanding == closing_frame.demanding;
    if !frames_agree {
        obstructions.push(ExposureObstruction::FramesDisagree {
            opening: opening_frame.clone(),
            closing: closing_frame.clone(),
        });
    } else if opening_frame.standing.is_empty() {
        obstructions.push(ExposureObstruction::NothingStands {
            internal: opening_frame.internal.len() as u64,
            demanding: opening_frame.demanding.len() as u64,
        });
    }

    let mut roles: BTreeMap<u8, UnitRole> = BTreeMap::new();
    if frames_agree {
        for octet in &alphabet {
            let role = if opening_frame.internal.contains(octet) {
                UnitRole::Internal
            } else if opening_frame.demanding.contains(octet) {
                UnitRole::Demanding
            } else {
                UnitRole::Standing
            };
            roles.insert(*octet, role);
        }
    }

    // 6. The codec and its gauge freedom.
    let (codec, gauge_freedom) = if obstructions.is_empty() {
        let (codec, gauge) = assemble(&alphabet, &roles, &follows);
        (Some(codec), gauge)
    } else {
        (None, Vec::new())
    };

    work.material_contacts = material.contacts();
    work.deep_scans = material.deep_scans();
    Ok(ExposureRecovery {
        schema: RECOVERY_SCHEMA.to_owned(),
        radius,
        alphabet,
        census,
        refusals,
        direct_quotient,
        direct_separations,
        opening_frame,
        closing_frame,
        roles,
        codec,
        gauge_freedom,
        obstructions,
        work,
    })
}

/// The finest quotient the declared family admits.
///
/// A context is a family word with one hole; two octets separate at the first context where one
/// occurs and the other does not. Contexts are enumerated shortest-first and, within a length, by
/// hole position and then lexicographically, so the context a separation carries is the shortest that
/// does it and the choice among equally short ones is the enumeration's and not a preference.
fn direct_quotient(
    material: &ExposedMaterial,
    alphabet: &[u8],
    radius: usize,
) -> (Vec<BTreeSet<u8>>, Vec<OctetSeparation>, u64) {
    let symbols = alphabet.len();
    let mut block = vec![0usize; symbols];
    let mut separations: Vec<OctetSeparation> = Vec::new();
    let mut contexts = 0u64;
    let mut filled = vec![0u8; radius];
    'contexts: for length in 1..=radius {
        let fills = (symbols as u64).pow((length - 1) as u32);
        for hole in 0..length {
            for ordinal in 0..fills {
                if block.iter().collect::<BTreeSet<_>>().len() == symbols {
                    break 'contexts;
                }
                contexts += 1;
                let mut rest = ordinal;
                for position in (0..length - 1).rev() {
                    let digit = alphabet[(rest % symbols as u64) as usize];
                    rest /= symbols as u64;
                    filled[if position < hole {
                        position
                    } else {
                        position + 1
                    }] = digit;
                }
                let occurred: Vec<bool> = (0..symbols)
                    .map(|symbol| {
                        filled[hole] = alphabet[symbol];
                        material.occurs(&filled[..length])
                    })
                    .collect();
                for left in 0..symbols {
                    for right in left + 1..symbols {
                        if block[left] == block[right] && occurred[left] != occurred[right] {
                            separations.push(OctetSeparation {
                                left: alphabet[left],
                                right: alphabet[right],
                                prefix: filled[..hole].to_vec(),
                                suffix: filled[hole + 1..length].to_vec(),
                                left_occurs: occurred[left],
                                right_occurs: occurred[right],
                            });
                        }
                    }
                }
                let mut fresh: BTreeMap<(usize, bool), usize> = BTreeMap::new();
                let mut refined = vec![0usize; symbols];
                for symbol in 0..symbols {
                    let key = (block[symbol], occurred[symbol]);
                    let next = fresh.len();
                    refined[symbol] = *fresh.entry(key).or_insert(next);
                }
                block = refined;
            }
        }
    }
    let mut blocks: BTreeMap<usize, BTreeSet<u8>> = BTreeMap::new();
    for (symbol, index) in block.iter().enumerate() {
        blocks.entry(*index).or_default().insert(alphabet[symbol]);
    }
    let quotient: Vec<BTreeSet<u8>> = blocks.into_values().collect();
    separations.sort();
    separations.dedup();
    (quotient, separations, contexts)
}

/// The downward fixed point of the unit-internal condition, seeded away from one end of the exposure.
///
/// `C` starts as every octet that does **not** carry the seed, and an octet leaves `C` as soon as it
/// is reached from outside `D(C) union C`. The operator is monotone downward, so it terminates, and
/// the set it lands on is the greatest unit-internal set below the seed complement.
fn unit_reading(
    alphabet: &[u8],
    follows: &BTreeMap<u8, BTreeSet<u8>>,
    precedes: &BTreeMap<u8, BTreeSet<u8>>,
    seed: &BTreeSet<u8>,
    frame: &str,
) -> FrameReading {
    let empty = BTreeSet::new();
    let mut internal: BTreeSet<u8> = alphabet
        .iter()
        .copied()
        .filter(|octet| !seed.contains(octet))
        .collect();
    let mut rounds = 0u64;
    loop {
        let demanding: BTreeSet<u8> = alphabet
            .iter()
            .copied()
            .filter(|octet| !internal.contains(octet))
            .filter(|octet| {
                let onward = follows.get(octet).unwrap_or(&empty);
                !onward.is_empty() && onward.iter().all(|next| internal.contains(next))
            })
            .collect();
        let reached: BTreeSet<u8> = internal
            .iter()
            .copied()
            .filter(|octet| {
                precedes
                    .get(octet)
                    .unwrap_or(&empty)
                    .iter()
                    .any(|before| !internal.contains(before) && !demanding.contains(before))
            })
            .collect();
        if reached.is_empty() {
            let standing: BTreeSet<u8> = alphabet
                .iter()
                .copied()
                .filter(|octet| !internal.contains(octet) && !demanding.contains(octet))
                .collect();
            return FrameReading {
                frame: frame.to_owned(),
                internal,
                demanding,
                standing,
                rounds,
            };
        }
        for octet in reached {
            internal.remove(&octet);
        }
        rounds += 1;
    }
}

/// Assemble the recovered roles into a runnable codec, and name the adjacencies the material never
/// realized.
///
/// A unit continues exactly across a unit-internal octet, so the boundary entry is decided by the
/// **right** class alone. Every octet emits: nothing in this material is a symbol that contributes no
/// character, and a `Drop` verdict is not forced by any word, so none is invented.
fn assemble(
    alphabet: &[u8],
    roles: &BTreeMap<u8, UnitRole>,
    follows: &BTreeMap<u8, BTreeSet<u8>>,
) -> (RecoveredCodec, Vec<(UnitRole, UnitRole)>) {
    let order = [UnitRole::Standing, UnitRole::Demanding, UnitRole::Internal];
    let present: Vec<UnitRole> = order
        .into_iter()
        .filter(|role| roles.values().any(|carried| carried == role))
        .collect();
    let classes: Vec<BTreeSet<Symbol>> = present
        .iter()
        .map(|role| {
            alphabet
                .iter()
                .filter(|octet| roles.get(octet) == Some(role))
                .map(|octet| Symbol(u32::from(*octet)))
                .collect()
        })
        .collect();
    let emission = vec![Emission::Emit; present.len()];
    let boundary: Vec<Vec<Boundary>> = present
        .iter()
        .map(|_| {
            present
                .iter()
                .map(|right| {
                    if *right == UnitRole::Internal {
                        Boundary::Join
                    } else {
                        Boundary::Cut
                    }
                })
                .collect()
        })
        .collect();
    let empty = BTreeSet::new();
    let mut gauge = Vec::new();
    for left in &present {
        for right in &present {
            let realized = alphabet
                .iter()
                .filter(|octet| roles.get(octet) == Some(left))
                .any(|octet| {
                    follows
                        .get(octet)
                        .unwrap_or(&empty)
                        .iter()
                        .any(|next| roles.get(next) == Some(right))
                });
            if !realized {
                gauge.push((*left, *right));
            }
        }
    }
    (
        RecoveredCodec {
            schema: CODEC_SCHEMA.to_owned(),
            classes,
            emission,
            boundary,
        },
        gauge,
    )
}

/// Write octets as a word the [`RecoveredCodec`] carrier runs on.
///
/// **This used to be a pun and is now an identity.** Until the alphabet was rotated off `char` on
/// 2026-08-13 the carrier was written over Unicode scalars, so an octet had to travel as *the code
/// point of the same value* — injective, invertible, and lossless, but a coincidence of two
/// numberings rather than a statement about the material. A [`Symbol`] is an opaque ordinal into a
/// declared alphabet, so an octet is now simply one, and nothing is being reinterpreted.
pub fn carried(octets: &[u8]) -> Vec<Symbol> {
    octets
        .iter()
        .map(|octet| Symbol(u32::from(*octet)))
        .collect()
}

/// The inverse of [`carried`]. Returns `None` at the first ordinal outside octet range.
pub fn octets_of(carried: &[Symbol]) -> Option<Vec<u8>> {
    carried
        .iter()
        .map(|symbol| u8::try_from(symbol.0).ok())
        .collect()
}

/// The alphabet an octet material declares: 256 symbols, each identified by its own ordinal.
///
/// Carried so a return can be exhibited. It is **not** consulted by the recovery, and nothing here
/// asserts that an octet means a character.
pub fn octet_alphabet() -> SymbolAlphabet {
    SymbolAlphabet::declared(
        (0u16..256)
            .map(|ordinal| (format!("{ordinal:02x}"), vec![ordinal as u8]))
            .collect(),
    )
    .expect("the octet alphabet carries no repeat")
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A returned segmentation, read back as the octet strings it stands for. The carrier holds
    /// ordinals; a fixture asserts about the material, so this is where the two meet.
    fn as_text(segmentation: &[Vec<Symbol>]) -> Vec<String> {
        segmentation
            .iter()
            .map(|token| {
                String::from_utf8(octets_of(token).expect("every ordinal is an octet"))
                    .expect("the fixture material is ascii")
            })
            .collect()
    }

    /// A material built from a made-up two-octet code: `H` heads a unit, `p` and `q` can only appear
    /// inside one, `a` and `b` stand alone. Every exposure opens and closes on a standing octet,
    /// because an exposure cut through the middle of a unit is a truncated exposure and the recovery
    /// is entitled to see whole ones.
    fn coded_material() -> ExposedMaterial {
        let exposures: Vec<Vec<u8>> = [
            "aHpbHqaHpHqbbaHqaHpa",
            "bHqaHpbbHpaHqHpaHqbb",
            "aHpaHqbHpbHqaaHpbHqa",
            "bbHqaaHpbHqHpbaHqaHpb",
        ]
        .iter()
        .map(|text| text.as_bytes().to_vec())
        .collect();
        ExposedMaterial::expose(exposures, 3).expect("exposes")
    }

    /// A synthetic Morse material: letters are runs over `.` and `-`, separated by a space, words
    /// separated by ` / `. It carries a real codec — a human reads it — and that codec has **no
    /// octet-level unit-internal structure at all**, which is exactly what makes it the control.
    fn morse_material() -> ExposedMaterial {
        let letters: BTreeMap<char, &str> = [
            ('a', ".-"),
            ('c', "-.-."),
            ('e', "."),
            ('h', "...."),
            ('l', ".-.."),
            ('n', "-."),
            ('o', "---"),
            ('r', ".-."),
            ('t', "-"),
        ]
        .into_iter()
        .collect();
        let words = ["holon", "chart", "relate", "controller", "then", "north"];
        let mut exposures = Vec::new();
        for rotation in 0..6usize {
            let mut line = Vec::new();
            for step in 0..words.len() {
                let word = words[(step + rotation) % words.len()];
                line.push(
                    word.chars()
                        .map(|letter| letters[&letter].to_owned())
                        .collect::<Vec<_>>()
                        .join(" "),
                );
            }
            exposures.push(line.join(" / ").into_bytes());
        }
        ExposedMaterial::expose(exposures, 3).expect("exposes")
    }

    #[test]
    fn the_alphabet_is_recovered_by_exhausting_every_octet_value() {
        let material = ExposedMaterial::expose(vec![b"abcabc".to_vec(), b"bcabca".to_vec()], 3)
            .expect("exposes");
        let recovery =
            recover(&material, ExposureApertures::declared(3, 100_000)).expect("recovers");
        assert_eq!(recovery.alphabet, vec![b'a', b'b', b'c']);
        assert_eq!(recovery.work.alphabet_probes, 256);
    }

    #[test]
    fn a_material_that_refuses_nothing_returns_the_negative_control_and_no_codec() {
        // A de Bruijn cycle over {a,b} carries every two- and three-octet word, twice over, so the
        // material licenses everything it could and there is no rule to recover. Uniform noise lands
        // here too; the obstruction is the whole return.
        let cycle = "aaababbbaaababbbaaababbbaaababbb";
        let material = ExposedMaterial::expose(
            vec![cycle.as_bytes().to_vec(), cycle.as_bytes().to_vec()],
            3,
        )
        .expect("exposes");
        let recovery =
            recover(&material, ExposureApertures::declared(3, 100_000)).expect("recovers");
        assert_eq!(recovery.census[1].refused, 0);
        assert_eq!(recovery.census[2].refused, 0);
        assert!(recovery
            .obstructions
            .contains(&ExposureObstruction::NothingIsRefused { radius: 3 }));
        assert!(!recovery.is_recovered());
    }

    #[test]
    fn recurrence_is_what_licenses_a_refusal_and_a_single_sighting_licenses_nothing() {
        let material =
            ExposedMaterial::expose(vec![b"xyzq".to_vec(), b"xy".to_vec()], 3).expect("exposes");
        assert!(material.recurs(b"xy"));
        assert!(!material.recurs(b"zq"));
        let recovery =
            recover(&material, ExposureApertures::declared(3, 100_000)).expect("recovers");
        for refusal in &recovery.refusals {
            assert!(material.recurs(&refusal.licensing_prefix));
            assert!(material.recurs(&refusal.licensing_suffix));
        }
        // `zq` was seen once, so nothing missing beside it is a rule.
        assert!(!recovery
            .refusals
            .iter()
            .any(|refusal| refusal.licensing_prefix == b"zq".to_vec()
                || refusal.licensing_suffix == b"zq".to_vec()));
    }

    #[test]
    fn a_two_octet_unit_codec_is_recovered_from_exposure_and_it_runs() {
        let material = coded_material();
        let recovery =
            recover(&material, ExposureApertures::declared(3, 100_000)).expect("recovers");
        assert!(
            recovery.obstructions.is_empty(),
            "{:?}",
            recovery.obstructions
        );
        assert_eq!(recovery.roles[&b'H'], UnitRole::Demanding);
        assert_eq!(recovery.roles[&b'p'], UnitRole::Internal);
        assert_eq!(recovery.roles[&b'q'], UnitRole::Internal);
        assert_eq!(recovery.roles[&b'a'], UnitRole::Standing);
        assert_eq!(recovery.roles[&b'b'], UnitRole::Standing);
        let codec = recovery.codec.as_ref().expect("a codec");
        assert_eq!(
            as_text(&codec.segment(&carried(b"aHpbHq")).expect("segments")),
            vec![
                "a".to_owned(),
                "Hp".to_owned(),
                "b".to_owned(),
                "Hq".to_owned()
            ]
        );
        // and it runs on a unit sequence the exposure never carried
        assert_eq!(
            as_text(&codec.segment(&carried(b"HqHqa")).expect("segments")),
            vec!["Hq".to_owned(), "Hq".to_owned(), "a".to_owned()]
        );
    }

    #[test]
    fn the_recovery_reads_its_own_rule_and_not_a_codec_it_was_never_told_about() {
        // The anti-authorship control. Morse is a real codec and a reader who knows it would say the
        // space is a delimiter and a run of dots is a letter. The material does not license that at
        // the octet grain: a space is reached from `.` and from `-`, and `.` is reached from a space,
        // so **nothing is unit-internal** and the honest reading is that every octet stands alone.
        // The recovery says so, and it does not reach for a code it was never shown.
        let material = morse_material();
        let recovery =
            recover(&material, ExposureApertures::declared(3, 100_000)).expect("recovers");
        assert!(recovery.opening_frame.internal.is_empty());
        assert!(recovery.opening_frame.demanding.is_empty());
        assert_eq!(
            recovery.opening_frame.standing.len(),
            recovery.alphabet.len()
        );
        // and it is not vacuous: the material does carry a rule set, so a codec is established even
        // though its units are single octets.
        assert!(recovery.census[1].refused > 0);
        let codec = recovery.codec.as_ref().expect("a codec");
        assert_eq!(codec.class_count(), 1);
        assert_eq!(
            as_text(&codec.segment(&carried(b"-.-.")).expect("segments")),
            vec![
                "-".to_owned(),
                ".".to_owned(),
                "-".to_owned(),
                ".".to_owned()
            ]
        );
    }

    #[test]
    fn a_reading_that_depends_on_which_end_it_was_seeded_from_is_refused() {
        // The same coded material, with one exposure truncated through the middle of a unit. The
        // opening frame still reads `p` as unit-internal; the closing frame cannot, because `p` now
        // ends an exposure. The two frames part company and the reading is refused by name rather
        // than returned from whichever frame was asked first.
        let mut exposures: Vec<Vec<u8>> = [
            "aHpbHqaHpHqbbaHqaHpa",
            "bHqaHpbbHpaHqHpaHqbb",
            "aHpaHqbHpbHqaaHpbHqa",
        ]
        .iter()
        .map(|text| text.as_bytes().to_vec())
        .collect();
        exposures.push(b"bbHqaaHpbHqHpbaHqaHp".to_vec());
        let material = ExposedMaterial::expose(exposures, 3).expect("exposes");
        let recovery =
            recover(&material, ExposureApertures::declared(3, 100_000)).expect("recovers");
        assert_ne!(
            recovery.opening_frame.internal,
            recovery.closing_frame.internal
        );
        assert!(recovery
            .obstructions
            .iter()
            .any(|obstruction| matches!(obstruction, ExposureObstruction::FramesDisagree { .. })));
        assert!(!recovery.is_recovered());
        assert!(recovery.roles.is_empty());
    }

    #[test]
    fn the_gauge_freedom_names_the_adjacencies_the_material_never_carried() {
        let material = coded_material();
        let recovery =
            recover(&material, ExposureApertures::declared(3, 100_000)).expect("recovers");
        // A standing octet is never followed by an internal one — that is the whole content of the
        // codec — and a demanding octet is followed by nothing but internal ones.
        assert!(recovery
            .gauge_freedom
            .contains(&(UnitRole::Standing, UnitRole::Internal)));
        assert!(recovery
            .gauge_freedom
            .contains(&(UnitRole::Demanding, UnitRole::Standing)));
        assert!(!recovery
            .gauge_freedom
            .contains(&(UnitRole::Demanding, UnitRole::Internal)));
    }

    #[test]
    fn the_direct_quotient_exhibits_the_shortest_context_that_separated_a_pair() {
        let material = coded_material();
        let recovery =
            recover(&material, ExposureApertures::declared(3, 100_000)).expect("recovers");
        assert!(recovery.direct_quotient.len() >= 2);
        for separation in &recovery.direct_separations {
            assert!(separation.left_occurs != separation.right_occurs);
            assert!(separation.context_length() <= recovery.radius);
        }
        // and the quotient is finer than the role reading: `p` and `q` play one role and are still
        // separated, which is the bound the direct grain reports on itself.
        assert_eq!(recovery.roles[&b'p'], recovery.roles[&b'q']);
        assert!(recovery
            .direct_quotient
            .iter()
            .all(|block| !(block.contains(&b'p') && block.contains(&b'q'))));
    }

    #[test]
    fn the_apertures_refuse_rather_than_sample() {
        let material =
            ExposedMaterial::expose(vec![b"abcdefghij".to_vec(), b"jihgfedcba".to_vec()], 3)
                .expect("exposes");
        let refused = recover(&material, ExposureApertures::declared(3, 10)).expect_err("refuses");
        match refused {
            ExposureRefusal::FamilyExceedsAperture { words, aperture } => {
                assert_eq!(aperture, 10);
                assert_eq!(words, 10 + 100 + 1000);
            }
            other => panic!("wrong refusal: {other:?}"),
        }
    }

    #[test]
    fn a_radius_below_adjacency_is_refused_by_name() {
        assert_eq!(
            ExposedMaterial::expose(vec![b"ab".to_vec()], 1).expect_err("refuses"),
            ExposureRefusal::RadiusBelowAdjacency { radius: 1 }
        );
        assert_eq!(
            ExposedMaterial::expose(vec![b"ab".to_vec()], 9).expect_err("refuses"),
            ExposureRefusal::RadiusExceedsCarrier {
                radius: 9,
                carrier_radius: 7
            }
        );
    }

    #[test]
    fn a_word_past_the_exposed_radius_costs_a_scan_and_is_counted_as_one() {
        let material = ExposedMaterial::expose(vec![b"abcdef".to_vec(), b"abcdef".to_vec()], 3)
            .expect("exposes");
        assert_eq!(material.deep_scans(), 0);
        assert!(material.occurs(b"abcde"));
        assert_eq!(material.deep_scans(), 1);
        assert!(!material.occurs(b"fedcba"));
        assert_eq!(material.deep_scans(), 2);
        // and a recovery never spends one: its family is bounded by the exposed radius.
        let recovery =
            recover(&material, ExposureApertures::declared(3, 100_000)).expect("recovers");
        assert_eq!(recovery.work.deep_scans, 2, "only the two asked above");
    }

    #[test]
    fn the_octet_carrier_round_trips() {
        let octets: Vec<u8> = (0u16..=255).map(|value| value as u8).collect();
        assert_eq!(octets_of(&carried(&octets)), Some(octets));
    }

    #[test]
    fn no_word_crosses_an_exposure_boundary() {
        let joined = ExposedMaterial::expose(vec![b"abcdef".to_vec()], 3).expect("exposes");
        let split =
            ExposedMaterial::expose(vec![b"abc".to_vec(), b"def".to_vec()], 3).expect("exposes");
        assert!(joined.occurs(b"cd"));
        assert!(!split.occurs(b"cd"));
    }
}
